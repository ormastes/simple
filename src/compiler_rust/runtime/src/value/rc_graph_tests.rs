//! Twin of src/runtime/test/rt_rc_selfcheck.c (BSM P4).

use super::*;
use crate::value::heap::is_registered_heap_ptr;
use crate::value::{
    rt_array_new, rt_array_push, rt_dict_new, rt_dict_set, rt_string_new, rt_transient_array_scope_begin,
    rt_transient_array_scope_end,
};

fn s(text: &str) -> RuntimeValue {
    rt_string_new(text.as_ptr(), text.len() as u64)
}

fn live(value: RuntimeValue) -> bool {
    is_registered_heap_ptr(value.as_heap_ptr())
}

#[test]
fn share_retain_release_lifecycle() {
    let child = rt_array_new(0);
    let child_text = s("child-text");
    rt_array_push(child, child_text);
    assert!(rt_rc_share(child));
    assert_eq!(rt_rc_count(child), 1);
    let root = rt_array_new(0);
    let owned = s("owned-text");
    rt_array_push(root, owned);
    rt_array_push(root, child);
    assert!(rt_rc_retain(child), "root's edge retains child");
    assert!(rt_rc_share(root));
    assert_eq!(rt_rc_count(root), 1);
    assert!(rt_rc_share(root), "idempotent");
    assert_eq!(rt_rc_count(root), 1);
    assert!(rt_rc_retain(root));
    assert_eq!(rt_rc_count(root), 2);
    assert!(rt_rc_release(root));
    assert_eq!(rt_rc_count(root), 1);
    assert!(rt_rc_release(root));
    assert!(!live(root) && !live(owned), "root + owned child freed");
    assert!(live(child) && live(child_text), "rc child only released");
    assert_eq!(rt_rc_count(child), 1);
    assert!(rt_rc_release(child));
    assert!(!live(child) && !live(child_text));
}

#[test]
fn release_on_non_rc_refuses() {
    let plain = rt_array_new(0);
    let text = s("plain-text");
    rt_array_push(plain, text);
    assert!(!rt_rc_release(plain));
    assert!(!rt_rc_retain(plain));
    assert_eq!(rt_rc_count(plain), -1);
    assert!(!rt_rc_release(RuntimeValue::from_int(7)));
    assert!(live(plain) && live(text), "nothing freed");
}

#[test]
fn graph_bytes_matches_hand_computed_sum() {
    let g = rt_array_new(0); // capacity 4
    rt_array_push(g, s("abcd"));
    rt_array_push(g, s("efghij"));
    let g_rc = rt_array_new(0);
    rt_array_push(g_rc, s("never-counted"));
    assert!(rt_rc_share(g_rc));
    rt_array_push(g, g_rc);
    // RuntimeArray 32 + 4 slots * 8; RuntimeString 24 + len; rc child 0.
    assert_eq!(rt_heap_graph_bytes(g), 64 + (24 + 4) + (24 + 6));
    assert_eq!(rt_heap_graph_bytes(RuntimeValue::from_int(1)), -1);
}

#[test]
fn share_inside_scope_moves_graph_out() {
    assert!(rt_transient_array_scope_begin());
    let scoped = rt_array_new(0);
    let text = s("scoped-text-value");
    rt_array_push(scoped, text);
    let unshared = rt_array_new(0);
    assert!(rt_rc_share(scoped));
    assert!(rt_transient_array_scope_end());
    assert!(!live(unshared), "scope end frees the unshared array");
    assert!(live(scoped) && live(text), "shared graph survives scope end");
    assert!(rt_rc_release(scoped));
    assert!(!live(scoped) && !live(text));
}

#[test]
fn cycle_check_refuses_self_containing_dict() {
    let d = rt_dict_new(0);
    rt_dict_set(d, s("self-key"), d);
    std::env::set_var("SIMPLE_RC_CYCLE_CHECK", "1");
    let refused = !rt_rc_share(d);
    let dag = rt_array_new(0);
    let leaf = rt_array_new(0);
    rt_array_push(dag, leaf);
    rt_array_push(dag, leaf);
    let dag_ok = rt_rc_share(dag);
    std::env::remove_var("SIMPLE_RC_CYCLE_CHECK");
    assert!(refused && rt_rc_count(d) == -1, "cyclic dict refused");
    assert!(dag_ok, "diamond DAG accepted");
    assert!(rt_rc_release(dag));
    assert!(!live(leaf));
}

#[test]
fn hundred_k_graph_share_release_linear() {
    let root = rt_array_new(0);
    let mut nodes = Vec::with_capacity(100_000);
    for i in 0..100_000 {
        let v = s(&format!("rc-node-{i:08}"));
        rt_array_push(root, v);
        nodes.push(v);
    }
    let t0 = std::time::Instant::now();
    assert!(rt_rc_share(root));
    let t1 = std::time::Instant::now();
    assert!(rt_rc_release(root));
    let t2 = std::time::Instant::now();
    assert!(!live(root));
    // Concurrent tests may re-register a freed address, so allow a sliver.
    let still_live = nodes.iter().filter(|v| live(**v)).count();
    assert!(still_live < 1000, "100k graph freed ({still_live} addresses live again)");
    eprintln!(
        "rc 100k: share={:?} release={:?} (100001 objects)",
        t1 - t0,
        t2 - t1
    );
}
