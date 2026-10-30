//! Object-graph refcount (Build Session Memory Model v1 §2 "RC shared",
//! §3 I5/I6/I8, §4; package P4). Twin of the `rt_rc_*` /
//! `rt_heap_graph_bytes` block in `src/runtime/runtime_native.c`.
//!
//! Ownership rule: every registered heap object is owned by exactly ONE of
//! {transient scope, session, rc root, process (untracked, rc 0)}.
//! `rt_rc_share(root)` makes the root an rc root (rc = 1) and claims its OWNED
//! graph: every node reachable from the root that is not itself an rc root
//! and not a `RT_STRING_FLAG_SHARED` cache string. Claimed nodes leave this
//! thread's transient scope list, so no scope end frees them. A sub-object
//! shared between two rc roots MUST itself be an rc root retained by each
//! parent. `rt_rc_release` reaching 0 frees the owned graph; an rc-root child
//! is RELEASED once per distinct child (not freed); a child still owned by the
//! live transient scope and a SHARED string are left alone. RC graphs are
//! acyclic (I5): `SIMPLE_RC_CYCLE_CHECK=1` makes share fail closed on a
//! back-edge.
//!
//! The count lives in a pointer-keyed side table (I6: `HeapHeader` and every
//! runtime layout are untouched). Only rc roots have a row.

use std::collections::HashMap;
use std::sync::Mutex;

use super::collections::{
    rc_graph_children, rc_graph_free, rc_graph_scope_owns, rc_graph_scope_release, RuntimeArray, RuntimeString,
    RT_STRING_FLAG_SHARED,
};
use super::dict::RuntimeDict;
use super::heap::{registered_heap_type, HeapHeader, HeapObjectType, HeapPtrSet};
use super::RuntimeValue;

/// rc side table: header address -> count. Lock order: this mutex, then the
/// thread's transient scope, then the allocation registry (inside frees).
static RC_TABLE: Mutex<Option<HashMap<usize, u32>>> = Mutex::new(None);

fn with_table<R>(f: impl FnOnce(&mut HashMap<usize, u32>) -> R) -> R {
    let mut guard = RC_TABLE.lock().unwrap_or_else(|e| e.into_inner());
    f(guard.get_or_insert_with(HashMap::new))
}

fn node_kind(value: RuntimeValue) -> Option<HeapObjectType> {
    registered_heap_type(value)
}

fn addr(value: RuntimeValue) -> usize {
    value.as_heap_ptr() as usize
}

fn is_shared_string(value: RuntimeValue, kind: HeapObjectType) -> bool {
    kind == HeapObjectType::String && unsafe { (*value.as_heap_ptr()).reserved } & RT_STRING_FLAG_SHARED != 0
}

/// Root plus its owned non-rc descendants (BFS, deduplicated by address);
/// distinct rc-root children are returned separately and not descended.
/// `skip_scope_owned`: at release, a node still owned by the live transient
/// scope is not part of the graph. None when a node's header is corrupt.
fn collect(
    root: RuntimeValue,
    table: &HashMap<usize, u32>,
    skip_scope_owned: bool,
    seen: &mut HeapPtrSet<usize>,
) -> Option<(Vec<RuntimeValue>, Vec<RuntimeValue>)> {
    let mut owned = Vec::new();
    let mut rc_children = Vec::new();
    let mut rc_seen = HeapPtrSet::<usize>::default();
    if !seen.insert(addr(root)) {
        return Some((owned, rc_children));
    }
    owned.push(root);
    let mut i = 0;
    while i < owned.len() {
        for child in rc_graph_children(owned[i])? {
            let Some(kind) = node_kind(child) else { continue };
            let a = addr(child);
            if table.contains_key(&a) {
                if rc_seen.insert(a) {
                    rc_children.push(child);
                }
                continue;
            }
            if is_shared_string(child, kind) || (skip_scope_owned && rc_graph_scope_owns(child)) {
                continue;
            }
            if seen.insert(a) {
                owned.push(child);
            }
        }
        i += 1;
    }
    Some((owned, rc_children))
}

/// Iterative DFS: true when a back-edge is reachable from `root`.
fn has_cycle(root: RuntimeValue) -> bool {
    // 1 = on the DFS stack, 2 = finished
    let mut color: HashMap<usize, u8> = HashMap::new();
    let mut stack: Vec<(RuntimeValue, Vec<RuntimeValue>, usize)> = Vec::new();
    color.insert(addr(root), 1);
    stack.push((root, rc_graph_children(root).unwrap_or_default(), 0));
    while let Some(frame) = stack.last_mut() {
        if frame.2 >= frame.1.len() {
            color.insert(addr(frame.0), 2);
            stack.pop();
            continue;
        }
        let child = frame.1[frame.2];
        frame.2 += 1;
        if node_kind(child).is_none() {
            continue;
        }
        match color.get(&addr(child)) {
            Some(1) => return true,
            Some(_) => continue,
            None => {
                color.insert(addr(child), 1);
                let kids = rc_graph_children(child).unwrap_or_default();
                stack.push((child, kids, 0));
            }
        }
    }
    false
}

fn node_bytes(value: RuntimeValue, kind: HeapObjectType) -> i64 {
    let ptr = value.as_heap_ptr();
    unsafe {
        match kind {
            HeapObjectType::String => {
                (std::mem::size_of::<RuntimeString>() as u64 + (*(ptr as *const RuntimeString)).len) as i64
            }
            HeapObjectType::Array => {
                let a = &*(ptr as *const RuntimeArray);
                let elem = if a.is_byte_packed() { 1 } else { 8 };
                let data = if a.data.is_null() { 0 } else { a.capacity * elem };
                (std::mem::size_of::<RuntimeArray>() as u64 + data) as i64
            }
            HeapObjectType::Dict => {
                let d = &*(ptr as *const RuntimeDict);
                let data = if d.data.is_null() { 0 } else { d.capacity * 16 };
                (std::mem::size_of::<RuntimeDict>() as u64 + data) as i64
            }
            _ => (*(ptr as *const HeapHeader)).size as i64,
        }
    }
}

/// Root becomes refcounted (rc = 1) and its owned graph leaves the transient
/// scope. Idempotent on an rc root. False for non-heap / unregistered /
/// SHARED-string roots, and with `SIMPLE_RC_CYCLE_CHECK=1` on a back-edge.
#[no_mangle]
pub extern "C" fn rt_rc_share(value: RuntimeValue) -> bool {
    let Some(kind) = node_kind(value) else { return false };
    let mut guard = RC_TABLE.lock().unwrap_or_else(|e| e.into_inner());
    let table = guard.get_or_insert_with(HashMap::new);
    if table.contains_key(&addr(value)) {
        return true;
    }
    if is_shared_string(value, kind) {
        return false;
    }
    if std::env::var("SIMPLE_RC_CYCLE_CHECK").is_ok_and(|v| v.starts_with('1')) && has_cycle(value) {
        return false;
    }
    let mut seen = HeapPtrSet::<usize>::default();
    let Some((owned, _)) = collect(value, table, false, &mut seen) else {
        return false;
    };
    let mut bits = HeapPtrSet::<u64>::default();
    bits.extend(owned.iter().map(|v| v.0));
    rc_graph_scope_release(&bits);
    table.insert(addr(value), 1);
    true
}

/// rc += 1; false if `value` is not an rc root.
#[no_mangle]
pub extern "C" fn rt_rc_retain(value: RuntimeValue) -> bool {
    if node_kind(value).is_none() {
        return false;
    }
    with_table(|table| match table.get_mut(&addr(value)) {
        Some(rc) if *rc < u32::MAX => {
            *rc += 1;
            true
        }
        _ => false,
    })
}

/// rc -= 1; at 0 frees the owned graph and releases rc-root children.
/// False if `value` is not an rc root.
#[no_mangle]
pub extern "C" fn rt_rc_release(value: RuntimeValue) -> bool {
    if node_kind(value).is_none() {
        return false;
    }
    let mut guard = RC_TABLE.lock().unwrap_or_else(|e| e.into_inner());
    let table = guard.get_or_insert_with(HashMap::new);
    let Some(rc) = table.get_mut(&addr(value)) else { return false };
    *rc -= 1;
    if *rc > 0 {
        return true;
    }
    table.remove(&addr(value));
    // Collect everything first, free after: no node is read after its free.
    let mut seen = HeapPtrSet::<usize>::default();
    let mut dead = Vec::new();
    let mut zero_roots = vec![value];
    let mut k = 0;
    while k < zero_roots.len() {
        // A corrupt header leaks the remainder rather than freeing it.
        let Some((owned, kids)) = collect(zero_roots[k], table, true, &mut seen) else { break };
        dead.extend(owned);
        for kid in kids {
            let a = addr(kid);
            if let Some(krc) = table.get_mut(&a) {
                *krc -= 1;
                if *krc == 0 {
                    table.remove(&a);
                    zero_roots.push(kid);
                }
            }
        }
        k += 1;
    }
    drop(guard);
    for node in dead {
        rc_graph_free(node);
    }
    true
}

/// Current count, or -1 if `value` is not an rc root.
#[no_mangle]
pub extern "C" fn rt_rc_count(value: RuntimeValue) -> i64 {
    if node_kind(value).is_none() {
        return -1;
    }
    with_table(|table| table.get(&addr(value)).map_or(-1, |rc| *rc as i64))
}

/// Bytes of the owned graph: headers + payload buffers (array data at
/// capacity * elem, dict slots at capacity * 16, string bytes); rc-root
/// children contribute 0. -1 for an invalid root.
#[no_mangle]
pub extern "C" fn rt_heap_graph_bytes(value: RuntimeValue) -> i64 {
    if node_kind(value).is_none() {
        return -1;
    }
    let guard = RC_TABLE.lock().unwrap_or_else(|e| e.into_inner());
    let empty = HashMap::new();
    let table = guard.as_ref().unwrap_or(&empty);
    let mut seen = HeapPtrSet::<usize>::default();
    let Some((owned, _)) = collect(value, table, false, &mut seen) else {
        return -1;
    };
    owned
        .into_iter()
        .filter_map(|v| node_kind(v).map(|k| node_bytes(v, k)))
        .sum()
}

#[cfg(test)]
#[path = "rc_graph_tests.rs"]
mod rc_graph_tests;
