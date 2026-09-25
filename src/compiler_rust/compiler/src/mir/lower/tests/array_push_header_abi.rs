//! Push-return ABI lowering pins (FAM freestanding vs canonical hosted).
//!
//! On FAM-layout baremetal runtimes (`Target::array_push_returns_header()` —
//! aarch64/arm32/x86_32 `baremetal_stubs.c`) `rt_array_push` and the typed
//! `rt_typed_*_push` family grow the whole FAM block by realloc and RETURN the
//! possibly moved header; the hosted runtime keeps a stable header and returns
//! bool. A compiled push loop that discards the return re-grows the stale
//! pre-grow block on every iteration — the 16,400-byte-per-push heap leak of
//! doc/08_tracking/bug/array_push_stale_receiver_store_arm64_2026-09-25.md.
//!
//! These tests pin the MIR shape: with the flag set, every push emission
//! captures the call result (`dest: Some`) and a bare `arr.push(x)` statement
//! stores it back into the receiver local; without it, the historical
//! bool-return shape (`dest: None`) is unchanged.

use crate::hir;
use crate::mir::function::MirModule;
use crate::mir::lower::{MirLowerResult, MirLowerer};
use crate::mir::{CallTarget, MirInst};
use simple_parser::Parser;

fn compile_to_mir_with_push_header(source: &str, array_push_returns_header: bool) -> MirLowerResult<MirModule> {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("parse failed");
    let hir_module = hir::lower(&ast).expect("hir lower failed");
    MirLowerer::new()
        .with_refined_types(&hir_module.refined_types)
        .with_type_registry(&hir_module.types)
        .with_trait_infos(&hir_module.trait_infos)
        .with_array_push_returns_header(array_push_returns_header)
        .lower_module(&hir_module)
}

fn push_call_dests(mir: &MirModule, name: &str) -> Vec<Option<crate::mir::instructions::VReg>> {
    mir.functions
        .iter()
        .flat_map(|f| f.blocks.iter())
        .flat_map(|b| b.instructions.iter())
        .filter_map(|i| match i {
            MirInst::Call { dest, target, .. } if target == &CallTarget::from_name(name) => Some(*dest),
            _ => None,
        })
        .collect()
}

/// True when some `Store` writes `value` through an address produced by a
/// `LocalAddr` (the receiver-local store-back).
fn has_local_store_of(mir: &MirModule, value: crate::mir::instructions::VReg) -> bool {
    mir.functions.iter().any(|f| {
        f.blocks.iter().any(|b| {
            let local_addrs: std::collections::HashSet<_> = b
                .instructions
                .iter()
                .filter_map(|i| match i {
                    MirInst::LocalAddr { dest, .. } => Some(*dest),
                    _ => None,
                })
                .collect();
            b.instructions.iter().any(|i| {
                matches!(i, MirInst::Store { addr, value: v, .. } if *v == value && local_addrs.contains(addr))
            })
        })
    })
}

#[test]
fn hosted_push_keeps_bool_return_shape() {
    // Canonical ABI: rt_array_push returns bool — dest stays None and no
    // store-back of a push result exists, for all four push targets.
    let mir = compile_to_mir_with_push_header(
        "fn test():\n    var arr: [i64] = []\n    arr = arr.push(1)\n    arr.push(2)\n",
        false,
    )
    .unwrap();
    let dests = push_call_dests(&mir, "rt_array_push");
    assert!(!dests.is_empty(), "expected rt_array_push calls");
    assert!(dests.iter().all(|d| d.is_none()), "hosted push must discard the bool return");
}

#[test]
fn fam_push_expression_captures_return() {
    // FAM ABI: the push result (post-grow header) becomes the expression
    // value, so `arr = arr.push(1)` stores the NEW header, not the stale one.
    let mir = compile_to_mir_with_push_header(
        "fn test():\n    var arr: [i64] = []\n    arr = arr.push(1)\n",
        true,
    )
    .unwrap();
    let dests = push_call_dests(&mir, "rt_array_push");
    assert_eq!(dests.len(), 1, "expected exactly one rt_array_push call");
    let pushed = dests[0].expect("FAM push must capture the returned header");
    assert!(
        has_local_store_of(&mir, pushed),
        "FAM push result must be stored back into the receiver local"
    );
}

#[test]
fn fam_push_statement_stores_back() {
    // FAM ABI, statement position: nothing consumes the expression value, so
    // the store-back into the receiver local is what keeps the loop-carried
    // array value advancing across grows.
    let mir = compile_to_mir_with_push_header("fn test():\n    var arr: [i64] = []\n    arr.push(2)\n", true).unwrap();
    let dests = push_call_dests(&mir, "rt_array_push");
    assert_eq!(dests.len(), 1);
    let pushed = dests[0].expect("FAM statement push must capture the returned header");
    assert!(has_local_store_of(&mir, pushed));
}

#[test]
fn fam_typed_u8_push_statement_stores_back() {
    let mir = compile_to_mir_with_push_header(
        "fn test():\n    var arr: [u8] = []\n    var byte: u8 = 42\n    arr.push(byte)\n",
        true,
    )
    .unwrap();
    let dests = push_call_dests(&mir, "rt_typed_bytes_u8_push");
    assert_eq!(dests.len(), 1, "expected the typed u8 push fast target");
    let pushed = dests[0].expect("FAM typed push must capture the returned header");
    assert!(has_local_store_of(&mir, pushed));
}

#[test]
fn fam_typed_u32_push_statement_stores_back() {
    let mir = compile_to_mir_with_push_header(
        "fn test():\n    var arr: [u32] = []\n    var word: u32 = 42\n    arr.push(word)\n",
        true,
    )
    .unwrap();
    let dests = push_call_dests(&mir, "rt_typed_words_u32_push");
    assert_eq!(dests.len(), 1);
    let pushed = dests[0].expect("FAM typed push must capture the returned header");
    assert!(has_local_store_of(&mir, pushed));
}

#[test]
fn fam_typed_u64_push_statement_stores_back() {
    let mir = compile_to_mir_with_push_header(
        "fn test():\n    var arr: [u64] = []\n    var word: u64 = 42u64\n    arr.push(word)\n",
        true,
    )
    .unwrap();
    let dests = push_call_dests(&mir, "rt_typed_words_u64_push");
    assert_eq!(dests.len(), 1);
    let pushed = dests[0].expect("FAM typed push must capture the returned header");
    assert!(has_local_store_of(&mir, pushed));
}

fn returned_vreg(mir: &MirModule) -> Option<crate::mir::instructions::VReg> {
    mir.functions.iter().find_map(|f| {
        f.blocks.iter().find_map(|b| match &b.terminator {
            crate::mir::Terminator::Return(Some(v)) => Some(*v),
            _ => None,
        })
    })
}

#[test]
fn fam_u8_array_literal_threads_push_result() {
    // [u8] literal in expression position: the returned handle must be the
    // LAST push's post-grow header, not the created one — a grow mid-fill
    // cannot leave the literal pointing at the pre-grow block.
    let mir = compile_to_mir_with_push_header(
        "fn give() -> [u8]:\n    return [1 as u8, 2 as u8, 3 as u8]\n",
        true,
    )
    .unwrap();
    let dests = push_call_dests(&mir, "rt_typed_bytes_u8_push");
    assert_eq!(dests.len(), 3);
    let last = dests[2].expect("literal fill push must produce a result vreg");
    assert_eq!(
        returned_vreg(&mir),
        Some(last),
        "FAM literal fill must yield the last push's post-grow header"
    );
}

#[test]
fn fam_u64_array_literal_threads_push_result() {
    let mir = compile_to_mir_with_push_header("fn give() -> [u64]:\n    return [1u64, 2u64]\n", true).unwrap();
    let dests = push_call_dests(&mir, "rt_typed_words_u64_push");
    assert_eq!(dests.len(), 2);
    let last = dests[1].expect("literal fill push must produce a result vreg");
    assert_eq!(returned_vreg(&mir), Some(last));
}

#[test]
fn hosted_u8_array_literal_keeps_created_handle() {
    // Canonical ABI: the created handle never moves, so the literal yields the
    // rt_byte_array_new result — never a push result vreg.
    let mir = compile_to_mir_with_push_header(
        "fn give() -> [u8]:\n    return [1 as u8, 2 as u8, 3 as u8]\n",
        false,
    )
    .unwrap();
    let dests = push_call_dests(&mir, "rt_typed_bytes_u8_push");
    assert_eq!(dests.len(), 3);
    let returned = returned_vreg(&mir).expect("literal must yield a handle");
    for d in dests.iter().flatten() {
        assert_ne!(
            returned, *d,
            "hosted literal fill must keep the created handle, not a push result"
        );
    }
}
