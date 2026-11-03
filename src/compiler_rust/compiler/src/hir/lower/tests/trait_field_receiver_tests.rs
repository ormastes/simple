//! Regression for
//! `doc/08_tracking/bug/native_codegen_trait_field_receiver_erased_ambiguous_2026_10_26.md`.
//!
//! A trait-typed FIELD receiver (`self.store.read(k)`) used to lower to a bare
//! `read` MethodCallStatic because the trait type aliases to ANY and only
//! typed LOCALS carried the declared trait owner; the native linker then saw
//! every same-named `*.read` as a candidate (AMBIGUOUS-METHOD).
use super::parse_and_lower;
use crate::mir::MirInst;

const SRC: &str = "trait Store:\n    fn read(key: i64) -> i64\n\nclass Disk:\n    var n: i64\n    fn read(key: i64) -> i64:\n        key\n\nclass Net:\n    var n: i64\n    fn read(key: i64) -> i64:\n        key + 1\n\nclass Adapter:\n    var store: Store\n    fn get(key: i64) -> i64:\n        self.store.read(key)\n";

#[test]
fn trait_typed_field_receiver_lowers_to_vtable_dispatch() {
    let module = parse_and_lower(SRC).unwrap();
    let mir = crate::mir::lower_to_mir(&module).expect("lower to mir");
    let get = mir.functions.iter().find(|f| f.name.ends_with("get")).expect("Adapter.get");
    let insts: Vec<_> = get.blocks.iter().flat_map(|b| &b.instructions).collect();
    assert!(
        insts.iter().any(|i| matches!(i, MirInst::MethodCallVirtual { vtable_slot: 0, .. })),
        "trait field receiver must dispatch through the Store vtable: {insts:?}"
    );
    assert!(
        !insts.iter().any(|i| matches!(i, MirInst::MethodCallStatic { func_name, .. } if func_name == "read")),
        "bare ambiguous `read` must not be emitted: {insts:?}"
    );
}
