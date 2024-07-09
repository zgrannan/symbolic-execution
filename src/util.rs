use crate::rustc_interface::middle::ty;

pub fn assert_tys_match<'tcx>(tcx: ty::TyCtxt<'tcx>, ty1: ty::Ty<'tcx>, ty2: ty::Ty<'tcx>) {
    // let ty1 = tcx.erase_regions(ty1);
    // let ty2 = tcx.erase_regions(ty2);
    // if matches!(ty1.kind(), ty::TyKind::Error(_)) || matches!(ty2.kind(), ty::TyKind::Error(_)) {
    //     return;
    // }
    // match (ty1.kind(), ty2.kind()) {
    //     (ty::TyKind::Ref(_, inner, mutbl), ty::TyKind::Ref(_, inner2, mutbl2)) if mutbl == mutbl2 => {
    //         return assert_tys_match(tcx, *inner, *inner2);
    //     }
    //     _ => {}
    // }

    // assert_eq!(ty1, ty2);
}
