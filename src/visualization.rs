use std::collections::BTreeSet;

use pcs::{borrows::engine::BorrowsDomain, free_pcs::FreePcsLocation, utils::PlaceRepacker};
use serde_json::json;

use crate::{
    context::SymExContext,
    debug_info::DebugInfo,
    path::{AcyclicPath, Path},
    results::{ResultAssertion, ResultPath},
    rustc_interface::{
        hir::def_id::DefId,
        middle::{
            mir::{self, Body, ProjectionElem, VarDebugInfo},
            ty::{self, GenericArgsRef, TyCtxt},
        },
    },
    value::{SymValueData, SymValueKind, SyntheticSymValue, Ty},
};

pub trait VisFormat {
    fn to_vis_string(&self, debug_info: &[VarDebugInfo]) -> String;
}

pub fn export_path_json<'sym, 'tcx, T: VisFormat>(
    debug_output_dir: &str,
    path: &Path<'sym, 'tcx, T>,
    fpcs_loc: &FreePcsLocation<BorrowsDomain<'tcx>>,
    instruction_index: usize,
    repacker: PlaceRepacker<'_, 'tcx>,
) {
    let path_component = path
        .path
        .blocks()
        .iter()
        .map(|block| format!("{:?}", block))
        .collect::<Vec<_>>()
        .join("_");
    std::fs::create_dir_all(&debug_output_dir).expect("Unable to create directory");
    let filename = format!(
        "{}/path_{}_stmt_{}.json",
        debug_output_dir, path_component, instruction_index
    );
    let mut json_object = serde_json::Map::new();
    json_object.insert(
        "pcs".to_string(),
        path.pcs.to_json(&repacker.body().var_debug_info),
    );
    json_object.insert(
        "heap".to_string(),
        path.heap.to_json(&repacker.body().var_debug_info),
    );
    json_object.insert(
        "borrows".to_string(),
        fpcs_loc.extra.after.to_json(repacker),
    );
    json_object.insert(
        "repacks_start".to_string(),
        serde_json::Value::Array(
            fpcs_loc
                .repacks_start
                .iter()
                .map(|repack| serde_json::Value::String(format!("{:?}", repack)))
                .collect(),
        ),
    );
    json_object.insert(
        "repacks_middle".to_string(),
        serde_json::Value::Array(
            fpcs_loc
                .repacks_middle
                .iter()
                .map(|repack| serde_json::Value::String(format!("{:?}", repack)))
                .collect(),
        ),
    );
    json_object.insert(
        "borrow_actions_start".to_string(),
        serde_json::Value::Array(
            fpcs_loc
                .extra
                .actions(true)
                .iter()
                .map(|action| action.to_json(repacker))
                .collect(),
        ),
    );
    json_object.insert(
        "borrow_actions_mid".to_string(),
        serde_json::Value::Array(
            fpcs_loc
                .extra
                .actions(false)
                .iter()
                .map(|action| action.to_json(repacker))
                .collect(),
        ),
    );
    let heap_json = serde_json::Value::Object(json_object);
    std::fs::write(filename, serde_json::to_string_pretty(&heap_json).unwrap())
        .expect("Unable to write file");
}

fn path_to_vec(path: &AcyclicPath) -> Vec<usize> {
    path.blocks().iter().map(|&bb| bb.index()).collect()
}

pub fn export_assertions<'sym, 'tcx, T: VisFormat>(
    debug_output_dir: &str,
    assertions: &BTreeSet<ResultAssertion<'sym, 'tcx, T>>,
    debug_info: &[VarDebugInfo],
) {
    let assertions_json: Vec<serde_json::Value> = assertions
        .iter()
        .map(|(path, pcs, assertion)| {
            json!({
                "path": path_to_vec(path),
                "pcs": pcs.to_json(debug_info),
                "assertion": assertion.to_vis_string(debug_info)
            })
        })
        .collect();

    let json_string = serde_json::to_string_pretty(&assertions_json)
        .expect("Failed to serialize result paths to JSON");

    let filename = format!("{}/assertions.json", debug_output_dir);

    std::fs::write(filename, json_string).expect("Failed to write assertions.json file");
}

pub fn export_path_list<'sym, 'tcx, T: VisFormat>(
    debug_output_dir: &str,
    result_paths: &BTreeSet<ResultPath<'sym, 'tcx, T>>,
) {
    let result_paths_json: Vec<Vec<usize>> = result_paths
        .iter()
        .map(|(path, _, _)| path_to_vec(path))
        .collect();

    let json_string = serde_json::to_string_pretty(&result_paths_json)
        .expect("Failed to serialize result paths to JSON");

    let filename = format!("{}/paths.json", debug_output_dir);

    std::fs::write(filename, json_string).expect("Failed to write paths.json file");
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>> SymValueData<'sym, 'tcx, T> {
    pub fn new(kind: SymValueKind<'sym, 'tcx, T>, arena: &'sym SymExContext) -> Self {
        SymValueData {
            kind,
            debug_info: DebugInfo::new(|t| arena.alloc(t)),
        }
    }

    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        self.kind.ty(tcx)
    }
}
impl<'sym, 'tcx, T: VisFormat> std::fmt::Display for SymValueData<'sym, 'tcx, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_vis_string(&[]))
    }
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for SymValueData<'sym, 'tcx, T> {
    fn to_vis_string(&self, debug_info: &[VarDebugInfo]) -> String {
        self.to_vis_string_prec(debug_info, PrecCategory::Bottom)
    }
}
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Clone, Copy)]
enum PrecCategory {
    Atom,
    Prefix,
    Field,
    Multiplicative,
    Additive,
    Shift,
    Bitwise,
    Comparison,
    LogicalAnd,
    LogicalOr,
    Bottom,
}

impl<'sym, 'tcx, T> SymValueKind<'sym, 'tcx, T> {
    fn prec_category(&self) -> PrecCategory {
        match self {
            SymValueKind::Var(_, _) | SymValueKind::Constant(_) | SymValueKind::Synthetic(_) => {
                PrecCategory::Atom
            }
            SymValueKind::Ref(_, _) => PrecCategory::Prefix,
            SymValueKind::CheckedBinaryOp(_, op, _, _) | SymValueKind::BinaryOp(_, op, _, _) => {
                match op {
                    mir::BinOp::Mul | mir::BinOp::Div | mir::BinOp::Rem => {
                        PrecCategory::Multiplicative
                    }
                    mir::BinOp::Add | mir::BinOp::Sub => PrecCategory::Additive,
                    mir::BinOp::Shl | mir::BinOp::Shr => PrecCategory::Shift,
                    mir::BinOp::BitAnd | mir::BinOp::BitXor | mir::BinOp::BitOr => {
                        PrecCategory::Bitwise
                    }
                    mir::BinOp::Eq
                    | mir::BinOp::Lt
                    | mir::BinOp::Le
                    | mir::BinOp::Ne
                    | mir::BinOp::Ge
                    | mir::BinOp::Gt => PrecCategory::Comparison,
                    _ => PrecCategory::Bottom, // For any other binary ops
                }
            }
            SymValueKind::UnaryOp(_, _, _) => PrecCategory::Prefix,
            SymValueKind::Projection(elem, _) => match elem {
                ProjectionElem::Deref => PrecCategory::Prefix,
                ProjectionElem::Field(..) => PrecCategory::Field,
                ProjectionElem::Index(_) => todo!(),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                ProjectionElem::Subslice { from, to, from_end } => todo!(),
                ProjectionElem::Downcast(_, _) => PrecCategory::Prefix, // TODO
                ProjectionElem::OpaqueCast(_) => todo!(),
            },
            SymValueKind::Aggregate(_, _) | SymValueKind::Discriminant(_) => PrecCategory::Atom,
            SymValueKind::Cast(_, _, _) => PrecCategory::Prefix,
            SymValueKind::InternalError(_, _) => PrecCategory::Atom,
        }
    }
}

const CATEGORIES: &[PrecCategory] = &[
    PrecCategory::Bottom,
    PrecCategory::Multiplicative,
    PrecCategory::Additive,
    PrecCategory::Shift,
    PrecCategory::Bitwise,
    PrecCategory::Comparison,
    PrecCategory::LogicalAnd,
    PrecCategory::LogicalOr,
    PrecCategory::Prefix,
    PrecCategory::Field,
    PrecCategory::Atom,
];

impl<'sym, 'tcx, T: VisFormat> SymValueData<'sym, 'tcx, T> {
    fn to_vis_string_prec(
        &self,
        debug_info: &[VarDebugInfo],
        parent_category: PrecCategory,
    ) -> String {
        let self_category = self.kind.prec_category();
        let result = match &self.kind {
            SymValueKind::Var(idx, ty) => {
                let info = debug_info.iter().find(|d| {
                    d.argument_index
                        .map_or(false, |arg_idx| arg_idx == (*idx + 1) as u16)
                });
                if let Some(info) = info {
                    format!("α<sub>{}</sub>", info.name)
                } else {
                    format!("α<sub>{}</sub>: {}", idx, ty)
                }
            }
            SymValueKind::Ref(_, t) => {
                format!("&{}", t.to_vis_string_prec(debug_info, self_category))
            }
            SymValueKind::Constant(c) => format!("{}", c.literal()),
            SymValueKind::CheckedBinaryOp(_, op, lhs, rhs)
            | SymValueKind::BinaryOp(_, op, lhs, rhs) => {
                let op_str = match op {
                    mir::BinOp::Add => "+",
                    mir::BinOp::Sub => "-",
                    mir::BinOp::Mul => "*",
                    mir::BinOp::Div => "/",
                    mir::BinOp::Rem => "%",
                    mir::BinOp::BitXor => "^",
                    mir::BinOp::BitAnd => "&",
                    mir::BinOp::BitOr => "|",
                    mir::BinOp::Shl => "<<",
                    mir::BinOp::Shr => ">>",
                    mir::BinOp::Eq => "==",
                    mir::BinOp::Lt => "<",
                    mir::BinOp::Le => "<=",
                    mir::BinOp::Ne => "!=",
                    mir::BinOp::Ge => ">=",
                    mir::BinOp::Gt => ">",
                    _ => "?",
                };
                format!(
                    "{} {} {}",
                    lhs.to_vis_string_prec(debug_info, self_category),
                    op_str,
                    rhs.to_vis_string_prec(debug_info, self_category)
                )
            }
            SymValueKind::UnaryOp(_, op, expr) => {
                let op_str = match op {
                    mir::UnOp::Not => "!",
                    mir::UnOp::Neg => "-",
                };
                format!(
                    "{}{}",
                    op_str,
                    expr.to_vis_string_prec(debug_info, self_category)
                )
            }
            SymValueKind::Projection(kind, value) => match kind {
                ProjectionElem::Deref => {
                    format!("*{}", value.to_vis_string_prec(debug_info, self_category))
                }
                ProjectionElem::Field(lhs, _) => format!(
                    "{}.{:?}",
                    value.to_vis_string_prec(debug_info, self_category),
                    lhs
                ),
                ProjectionElem::Index(_) => todo!(),
                ProjectionElem::ConstantIndex {
                    offset,
                    min_length,
                    from_end,
                } => todo!(),
                ProjectionElem::Subslice { from, to, from_end } => todo!(),
                ProjectionElem::Downcast(Some(sym), _) => format!(
                    "{}@{}",
                    value.to_vis_string_prec(debug_info, self_category),
                    sym
                ),
                ProjectionElem::Downcast(None, idx) => format!(
                    "{:?}@{:?}",
                    value.to_vis_string_prec(debug_info, self_category),
                    idx
                ),
                ProjectionElem::OpaqueCast(_) => todo!(),
            },
            SymValueKind::Aggregate(kind, values) => {
                let values_str = values
                    .iter()
                    .map(|v| v.to_vis_string(debug_info))
                    .collect::<Vec<_>>()
                    .join(", ");
                let pack_ty = match kind {
                    crate::value::AggregateKind::Rust(_, _) => "R",
                    crate::value::AggregateKind::PCS(_, _) => "P",
                };
                format!("pack[{}]<{}>({})", pack_ty, kind.ty(), values_str)
            }
            SymValueKind::Discriminant(val) => {
                format!("discriminant({})", val.to_vis_string(debug_info))
            }
            SymValueKind::Synthetic(s) => s.to_vis_string(debug_info),
            SymValueKind::Cast(_, _, _) => "todo!()".to_string(),
            SymValueKind::InternalError(err, _) => format!("INTERNAL ERROR: {}", err),
        };

        if needs_parens(self_category, parent_category) {
            format!("({})", result)
        } else {
            result
        }
    }
}

fn needs_parens(child: PrecCategory, parent: PrecCategory) -> bool {
    let child_index = CATEGORIES.iter().position(|cats| cats == &child).unwrap();
    let parent_index = CATEGORIES.iter().position(|cats| cats == &parent).unwrap();

    child_index < parent_index
}
