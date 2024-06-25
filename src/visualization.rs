use std::collections::BTreeSet;

use crate::{
    path::Path,
    results::ResultPath,
    rustc_interface::{
        hir::def_id::DefId,
        middle::{
            mir::{self, Body, VarDebugInfo},
            ty::{self, GenericArgsRef, TyCtxt},
        },
    },
};

pub trait VisFormat {
    fn to_vis_string(&self, debug_info: &[VarDebugInfo]) -> String;
}

fn get_fn_data_dir(fn_name: &str) -> String {
    let data_dir = std::env::var("PCS_VIS_DATA_DIR").expect("PCS_VIS_DATA_DIR not set");
    format!("{}/{}", data_dir, fn_name)
}

pub fn export_path_json<'sym, 'tcx, T: VisFormat>(
    fn_name: &str,
    path: &Path<'sym, 'tcx, T>,
    instruction_index: usize,
    debug_info: &[VarDebugInfo],
) {
    let path_component = path
        .path
        .blocks()
        .iter()
        .map(|block| format!("{:?}", block))
        .collect::<Vec<_>>()
        .join("_");
    let fn_dir = get_fn_data_dir(fn_name);
    std::fs::create_dir_all(&fn_dir).expect("Unable to create directory");
    let filename = format!(
        "{}/path_{}_stmt_{}.json",
        fn_dir, path_component, instruction_index
    );
    let heap_json = path.heap.to_json(debug_info);
    std::fs::write(filename, serde_json::to_string_pretty(&heap_json).unwrap())
        .expect("Unable to write file");
}

pub fn export_path_list<'sym, 'tcx, T: VisFormat>(
    fn_name: &str,
    result_paths: &BTreeSet<ResultPath<'sym, 'tcx, T>>,
) {
    let result_paths_json: Vec<Vec<usize>> = result_paths
        .iter()
        .map(|(path, _, _)| path.blocks().iter().map(|&bb| bb.index()).collect())
        .collect();

    let json_string = serde_json::to_string_pretty(&result_paths_json)
        .expect("Failed to serialize result paths to JSON");

    let filename = format!("{}/paths.json", get_fn_data_dir(fn_name),);

    std::fs::write(filename, json_string).expect("Failed to write paths.json file");
}
