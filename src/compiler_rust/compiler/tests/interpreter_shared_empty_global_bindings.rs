//! Mechanism pin: every `CowEnv` (i.e. every function call frame) shares ONE
//! empty `global_bindings` map instead of heap-allocating a fresh
//! `Arc<HashMap>` — an Arc control block plus a `HashMap` header — per frame
//! for a map that is empty in the overwhelming majority of frames.
//!
//! Sibling of `interpreter_shared_empty_captured_env.rs` (7fe00b1c4d5), which
//! shared the empty `CowEnv` itself; its own doc comment named the inner
//! `Arc<HashMap>` for `global_bindings` as part of the same ~600 B of waste
//! but left it allocating per frame.
//!
//! doc/08_tracking/bug/seed_empty_global_bindings_map_allocated_per_frame_2026-08-23.md
use simple_compiler::value::CowEnv;
use std::sync::Arc;

const N: usize = 1000;

#[test]
fn every_frame_shares_one_empty_global_bindings_map() {
    let shared = CowEnv::shared_empty_global_bindings();
    let before = Arc::strong_count(&shared);

    let frames: Vec<CowEnv> = (0..N).map(|_| CowEnv::new()).collect();
    let after = Arc::strong_count(&shared);

    // Pre-fix each frame did `Arc::new(HashMap::new())`, so the shared Arc
    // never gained a holder (after == before).
    assert!(
        after >= before + N,
        "expected >= {N} frames to share the empty global_bindings map, got {} new holders",
        after - before
    );
    drop(frames);
    assert_eq!(
        Arc::strong_count(&shared),
        before,
        "frames must release the share on drop"
    );
}

#[test]
fn with_base_and_from_map_frames_share_it_too() {
    let shared = CowEnv::shared_empty_global_bindings();
    let before = Arc::strong_count(&shared);
    let base = Arc::new(std::collections::HashMap::new());
    let a = CowEnv::with_base(Arc::clone(&base));
    let b = CowEnv::from_map(std::collections::HashMap::new());
    assert_eq!(Arc::strong_count(&shared), before + 2);
    drop((a, b));
    assert_eq!(Arc::strong_count(&shared), before);
}

/// Value semantics are unaffected: a frame that actually binds a global name
/// copies-on-write off the shared map, so the shared empty map stays empty and
/// sibling frames observe nothing.
#[test]
fn a_real_binding_copies_on_write_and_does_not_leak_into_siblings() {
    let shared = CowEnv::shared_empty_global_bindings();
    let mut writer = CowEnv::new();
    let sibling = CowEnv::new();

    writer.bind_global("x".to_string(), Arc::from("mod"), "gx".to_string());

    assert!(shared.is_empty(), "the shared empty map must never be written through");
    assert!(
        sibling.global_binding("x").is_none(),
        "a sibling frame must not observe the writer's binding"
    );
    assert!(writer.global_binding("x").is_some(), "the writer keeps its own binding");
}
