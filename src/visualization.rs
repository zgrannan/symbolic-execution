use std::collections::BTreeSet;

use pcs::utils::PlaceRepacker;
use serde_json::json;

use crate::{
    context::SymExContext,
    debug_info::DEBUGINFO_NONE,
    execute::ResultAssertions,
    path::{AcyclicPath, Path, SymExPath},
    pcs_interaction::PcsLocation,
    results::{ResultAssertion, ResultPaths},
    rustc_interface::{
        ast::Mutability,
        hir::{def_id::DefId, ItemKind, Node},
        middle::{
            mir::{self, ProjectionElem, VarDebugInfo},
            ty::{self, TyCtxt},
        },
    },
    value::{SymValue, SymValueData, SymValueKind, SyntheticSymValue, Ty},
};

#[derive(Copy, Clone)]
pub enum OutputMode {
    HTML,
    Text,
}

impl OutputMode {
    pub fn newline(&self) -> &'static str {
        match self {
            OutputMode::HTML => "<br>",
            OutputMode::Text => "\n",
        }
    }
    fn lt(&self) -> &'static str {
        match self {
            OutputMode::HTML => "&lt;",
            OutputMode::Text => "<",
        }
    }
    fn gt(&self) -> &'static str {
        match self {
            OutputMode::HTML => "&gt;",
            OutputMode::Text => ">",
        }
    }

    pub fn in_lt_gt(&self, s: impl std::fmt::Display) -> String {
        format!("{}{}{}", self.lt(), s, self.gt())
    }

    pub fn subscript(&self, s: impl std::fmt::Display) -> String {
        match self {
            OutputMode::Text => format!("_{}", s),
            OutputMode::HTML => format!("<sub>{}</sub>", s),
        }
    }
}

pub trait VisFormat {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String;
}

pub enum StepType {
    Instruction(usize),
    Transition,
}

pub fn export_path_json<
    'sym,
    'tcx,
    T: VisFormat + SyntheticSymValue<'sym, 'tcx> + std::fmt::Debug,
>(
    debug_output_dir: &str,
    path: &Path<'sym, 'tcx, T>,
    fpcs_loc: &PcsLocation<'_, 'tcx>,
    step: StepType,
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
        "{}/path_{}_{}.json",
        debug_output_dir,
        path_component,
        match step {
            StepType::Instruction(idx) => format!("stmt_{}", idx),
            StepType::Transition => "transition".to_string(),
        }
    );
    let mut json_object = serde_json::Map::new();
    json_object.insert(
        "pcs".to_string(),
        path.pcs
            .to_json(Some(repacker.tcx()), &repacker.body().var_debug_info),
    );
    json_object.insert("heap".to_string(), path.heap.to_json(repacker));
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
        "reborrow_start".to_string(),
        fpcs_loc.extra_start.to_json(repacker),
    );
    if let Some(reborrow_middle) = &fpcs_loc.extra_middle {
        json_object.insert(
            "reborrow_middle".to_string(),
            reborrow_middle.to_json(repacker),
        );
    }
    let heap_json = serde_json::Value::Object(json_object);
    std::fs::write(filename, serde_json::to_string_pretty(&heap_json).unwrap())
        .expect("Unable to write file");
}

pub fn export_assertions<'sym, 'tcx, T: VisFormat>(
    debug_output_dir: &str,
    assertions: &ResultAssertions<'sym, 'tcx, T>,
    debug_info: &[VarDebugInfo],
    tcx: TyCtxt<'_>,
) {
    let assertions_json: Vec<serde_json::Value> = assertions
        .iter()
        .map(
            |ResultAssertion {
                 path,
                 pcs,
                 assertion,
             }| {
                json!({
                    "path": path.to_index_vec(),
                    "pcs": pcs.to_json(Some(tcx), debug_info),
                    "assertion": assertion.to_vis_string(Some(tcx), debug_info, OutputMode::HTML)
                })
            },
        )
        .collect();

    let json_string = serde_json::to_string_pretty(&assertions_json)
        .expect("Failed to serialize result paths to JSON");

    let filename = format!("{}/assertions.json", debug_output_dir);

    std::fs::write(filename, json_string).expect("Failed to write assertions.json file");
}

pub fn export_path_list<'sym, 'tcx, T: VisFormat>(
    debug_output_dir: &str,
    result_paths: &ResultPaths<'sym, 'tcx, T>,
    _debug_paths: &[Path<'sym, 'tcx, T>],
) {
    let result_paths_json: Vec<Vec<usize>> = result_paths
        .iter()
        .map(|path| path.path().to_index_vec())
        .collect();

    let json_string = serde_json::to_string_pretty(&result_paths_json)
        .expect("Failed to serialize result paths to JSON");

    let filename = format!("{}/paths.json", debug_output_dir);

    std::fs::write(filename, json_string).expect("Failed to write paths.json file");
}

impl<'sym, 'tcx, T, V> SymValueData<'sym, 'tcx, T, V> {
    pub fn new(kind: SymValueKind<'sym, 'tcx, T, V>, _arena: &'sym SymExContext) -> Self {
        SymValueData {
            kind,
            debug_info: DEBUGINFO_NONE,
        }
    }
}

impl<'sym, 'tcx, T: SyntheticSymValue<'sym, 'tcx>, V> SymValueData<'sym, 'tcx, T, V> {
    pub fn ty(&self, tcx: ty::TyCtxt<'tcx>) -> Ty<'tcx> {
        self.kind.ty(tcx)
    }
}

impl<'sym, 'tcx, T: VisFormat> std::fmt::Display for SymValueData<'sym, 'tcx, T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}",
            self.to_vis_string_prec(None, &[], PrecCategory::Bottom, OutputMode::Text)
        )
    }
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for SymValueData<'sym, 'tcx, T> {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        self.to_vis_string_prec(tcx, debug_info, PrecCategory::Bottom, mode)
    }
}

impl<'sym, 'tcx, T: VisFormat> VisFormat for &'sym [SymValue<'sym, 'tcx, T>] {
    fn to_vis_string(
        &self,
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        mode: OutputMode,
    ) -> String {
        self.iter()
            .map(|value| value.to_vis_string(tcx, debug_info, mode))
            .collect::<Vec<_>>()
            .join(", ")
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
            SymValueKind::BinaryOp(_, op, _, _) => {
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
                    offset: _,
                    min_length: _,
                    from_end: _,
                } => todo!(),
                ProjectionElem::Subslice {
                    from: _,
                    to: _,
                    from_end: _,
                } => todo!(),
                ProjectionElem::Downcast(_, _) => PrecCategory::Prefix, // TODO
                ProjectionElem::OpaqueCast(_) => todo!(),
                ProjectionElem::Subtype(_) => todo!(),
            },
            SymValueKind::Aggregate(_, _) | SymValueKind::Discriminant(_) => PrecCategory::Atom,
            SymValueKind::Cast(_, _, _) => PrecCategory::Prefix,
            SymValueKind::InternalError(_, _) => PrecCategory::Atom,
            SymValueKind::Ref(_, _) => PrecCategory::Prefix,
            SymValueKind::BackwardsFn(_) => PrecCategory::Atom,
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
        tcx: Option<TyCtxt<'_>>,
        debug_info: &[VarDebugInfo],
        parent_category: PrecCategory,
        mode: OutputMode,
    ) -> String {
        let self_category = self.kind.prec_category();
        let result = match &self.kind {
            SymValueKind::Var(var, _) => var.to_string(debug_info, mode),
            SymValueKind::Constant(c) => format!("{}", c.literal()),
            SymValueKind::BinaryOp(_, op, lhs, rhs) => {
                let op_str = match op {
                    mir::BinOp::Add | mir::BinOp::AddWithOverflow => "+",
                    mir::BinOp::Sub | mir::BinOp::SubWithOverflow => "-",
                    mir::BinOp::Mul | mir::BinOp::MulWithOverflow => "*",
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
                    lhs.to_vis_string_prec(tcx, debug_info, self_category, mode),
                    op_str,
                    rhs.to_vis_string_prec(tcx, debug_info, self_category, mode)
                )
            }
            SymValueKind::UnaryOp(_, op, expr) => {
                let op_str = match op {
                    mir::UnOp::Not => "!",
                    mir::UnOp::Neg => "-",
                    _ => todo!(),
                };
                format!(
                    "{}{}",
                    op_str,
                    expr.to_vis_string_prec(tcx, debug_info, self_category, mode)
                )
            }
            SymValueKind::Projection(kind, value) => match kind {
                ProjectionElem::Deref => {
                    format!(
                        "*{}",
                        value.to_vis_string_prec(tcx, debug_info, self_category, mode)
                    )
                }
                ProjectionElem::Field(lhs, _) => format!(
                    "{}.{:?}",
                    value.to_vis_string_prec(tcx, debug_info, self_category, mode),
                    lhs
                ),
                ProjectionElem::Index(_) => todo!(),
                ProjectionElem::ConstantIndex {
                    offset: _,
                    min_length: _,
                    from_end: _,
                } => todo!(),
                ProjectionElem::Subslice {
                    from: _,
                    to: _,
                    from_end: _,
                } => todo!(),
                ProjectionElem::Downcast(Some(sym), _) => format!(
                    "{}@{}",
                    value.to_vis_string_prec(tcx, debug_info, self_category, mode),
                    sym
                ),
                ProjectionElem::Downcast(None, idx) => format!(
                    "{:?}@{:?}",
                    value.to_vis_string_prec(tcx, debug_info, self_category, mode),
                    idx
                ),
                ProjectionElem::OpaqueCast(_) => todo!(),
                ProjectionElem::Subtype(_) => todo!(),
            },
            SymValueKind::Aggregate(kind, values) => {
                let pack_ty = match kind {
                    crate::value::AggregateKind::Rust(_, _) => "R",
                    crate::value::AggregateKind::PCS(_, _) => "P",
                };
                let _lt = mode.lt();
                let _gt = mode.gt();
                format!(
                    "pack[{pack_ty}]{}({})",
                    mode.in_lt_gt(kind.ty()),
                    values.to_vis_string(tcx, debug_info, mode)
                )
            }
            SymValueKind::Discriminant(val) => {
                format!("discriminant({})", val.to_vis_string(tcx, debug_info, mode))
            }
            SymValueKind::Synthetic(s) => s.to_vis_string(tcx, debug_info, mode),
            SymValueKind::Cast(_, _, _) => "todo!()".to_string(),
            SymValueKind::InternalError(err, _) => format!("INTERNAL ERROR: {}", err),
            SymValueKind::Ref(val, Mutability::Mut) => {
                format!("&mut {}", val.to_vis_string(tcx, debug_info, mode))
            }
            SymValueKind::Ref(val, Mutability::Not) => {
                format!("&{}", val.to_vis_string(tcx, debug_info, mode))
            }
            SymValueKind::BackwardsFn(backwards_fn) => {
                format!(
                    "{}<sub>back_{}</sub>({}, {})",
                    get_fn_name(tcx, backwards_fn.def_id),
                    get_arg_name(tcx, backwards_fn.def_id, backwards_fn.arg_index),
                    backwards_fn
                        .arg_snapshots
                        .to_vis_string(tcx, debug_info, mode),
                    backwards_fn
                        .return_snapshot
                        .to_vis_string(tcx, debug_info, mode)
                )
            }
        };

        if needs_parens(self_category, parent_category) {
            format!("({})", result)
        } else {
            result
        }
    }
}

fn get_fn_name(tcx: Option<TyCtxt<'_>>, fn_def_id: DefId) -> String {
    if let Some(tcx) = tcx {
        if let Some(item_name) = tcx.opt_item_name(fn_def_id) {
            return item_name.to_string();
        }
    }
    return format!("{:?}", fn_def_id);
}

fn get_arg_name(tcx: Option<TyCtxt<'_>>, fn_def_id: DefId, arg_idx: usize) -> String {
    if let Some(tcx) = tcx {
        if let Some(Node::Item(item)) = tcx.hir().get_if_local(fn_def_id) {
            if let ItemKind::Fn(_, _, body_id) = item.kind {
                let body = tcx.hir().body(body_id);
                if let Some(arg) = body.params.get(arg_idx) {
                    if let Some(ident) = arg.pat.simple_ident() {
                        return ident.name.to_string();
                    }
                }
            }
        }
    }
    return format!("arg{}", arg_idx);
}

fn needs_parens(child: PrecCategory, parent: PrecCategory) -> bool {
    let child_index = CATEGORIES.iter().position(|cats| cats == &child).unwrap();
    let parent_index = CATEGORIES.iter().position(|cats| cats == &parent).unwrap();

    child_index < parent_index
}
