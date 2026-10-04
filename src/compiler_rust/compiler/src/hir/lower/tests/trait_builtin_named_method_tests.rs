//! Regression for
//! `doc/08_tracking/bug/jit_trait_method_tuple_return_read_as_tagged_ints_2026-10-04.md`.
//!
//! A trait-typed receiver is ANY in HIR. A trait method that shares a name
//! with a builtin collection method (`size`, `len`, `get`, ...) used to take
//! the builtin's fixed result type (`size` -> I64) instead of the trait's
//! declared return type, so `val (w, h) = host.size()` destructured tagged
//! RuntimeValues as raw integers under the JIT (1280 read as 10240).
use super::parse_and_lower;
use crate::hir::types::{HirType, TypeId};

const TRAIT_SRC: &str = "trait SizedHost:\n    me size() -> (i32, i32)\n    me len() -> text\n    me scale() -> i32\n\nclass Box2:\n    var w: i32\n\nimpl SizedHost for Box2:\n    me size() -> (i32, i32):\n        (self.w, self.w)\n    me len() -> text:\n        \"box\"\n    me scale() -> i32:\n        self.w\n\n";

fn local_ty(source: &str, func: &str, local: &str) -> (crate::hir::HirModule, TypeId) {
    let module = parse_and_lower(source).unwrap();
    let function = module.functions.iter().find(|f| f.name == func).unwrap();
    let ty = function.locals.iter().find(|l| l.name == local).unwrap().ty;
    (module, ty)
}

#[test]
fn trait_receiver_size_keeps_declared_tuple_return() {
    let src = format!("{TRAIT_SRC}fn probe(host: SizedHost) -> i64:\n    val (w, h) = host.size()\n    0\n");
    let (module, w_ty) = local_ty(&src, "probe", "w");
    assert_eq!(w_ty, TypeId::I32, "w must be the tuple's i32 element, got {:?}", module.types.get(w_ty));
}

#[test]
fn trait_receiver_builtin_named_methods_use_trait_signature() {
    // `len` is a builtin name returning I64; the trait declares text.
    let src = format!("{TRAIT_SRC}fn probe(host: SizedHost) -> i64:\n    val n = host.len()\n    val s = host.scale()\n    val dims = host.size()\n    0\n");
    let (module, n_ty) = local_ty(&src, "probe", "n");
    assert_eq!(n_ty, TypeId::STRING);
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    let s_ty = function.locals.iter().find(|l| l.name == "s").unwrap().ty;
    assert_eq!(s_ty, TypeId::I32);
    let dims_ty = function.locals.iter().find(|l| l.name == "dims").unwrap().ty;
    assert!(matches!(module.types.get(dims_ty), Some(HirType::Tuple(items)) if items == &vec![TypeId::I32, TypeId::I32]), "{:?}", module.types.get(dims_ty));
}

#[test]
fn erased_and_typed_receivers_keep_builtin_types() {
    // No trait declares `size` here: the erased-receiver builtin rule stays.
    let src = "fn probe(items: any, counts: Dict<text, i64>) -> i64:\n    val n = items.size()\n    val m = counts.len()\n    0\n";
    let (module, n_ty) = local_ty(src, "probe", "n");
    assert_eq!(n_ty, TypeId::I64);
    let function = module.functions.iter().find(|f| f.name == "probe").unwrap();
    assert_eq!(function.locals.iter().find(|l| l.name == "m").unwrap().ty, TypeId::I64);
}

#[test]
fn typed_dict_receiver_ignores_trait_named_get() {
    // A typed Dict is never a trait object, even when a trait declares `get`.
    let src = "trait Store:\n    me get(key: text) -> bool\n\nclass Mem:\n    var x: i64\n\nimpl Store for Mem:\n    me get(key: text) -> bool:\n        true\n\nfn probe(counts: Dict<text, i64>) -> i64:\n    val v = counts.get(\"a\")\n    0\n";
    let (_, v_ty) = local_ty(src, "probe", "v");
    assert_eq!(v_ty, TypeId::I64);
}
