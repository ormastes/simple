use super::*;

#[test]
fn state_query_tracks_actual_lifecycle_without_mutation() {
    assert_eq!(rt_transient_array_scope_state_v1(), 0);
    assert!(!rt_transient_array_scope_pause());
    assert!(!rt_transient_array_scope_end());
    assert_eq!(rt_transient_array_scope_state_v1(), 0);
    assert!(rt_transient_array_scope_begin());
    assert_eq!(rt_transient_array_scope_state_v1(), 1);
    assert!(!rt_transient_array_scope_begin());
    assert_eq!(rt_transient_array_scope_state_v1(), 1);
    assert!(rt_transient_array_scope_pause());
    assert_eq!(rt_transient_array_scope_state_v1(), 2);
    assert!(!rt_transient_array_scope_begin());
    assert_eq!(rt_transient_array_scope_state_v1(), 2);
    assert!(rt_transient_array_scope_end());
    assert_eq!(rt_transient_array_scope_state_v1(), 0);
    assert!(!rt_transient_array_scope_end());
    assert_eq!(rt_transient_array_scope_state_v1(), 0);
}

#[test]
fn query_uses_calling_thread_and_preserves_other_threads_scope() {
    assert_eq!(rt_transient_array_scope_state_v1(), 0);
    assert!(rt_transient_array_scope_begin());
    for main_state in [1, 2] {
        if main_state == 2 { assert!(rt_transient_array_scope_pause()); }
        std::thread::spawn(|| {
            // Another Rust TLS context cannot see or end the caller's scope.
            assert_eq!(rt_transient_array_scope_state_v1(), 0);
            assert!(!rt_transient_array_scope_pause());
            assert!(!rt_transient_array_scope_end());
            // Its real thread-local allocator permits an independent scope.
            assert!(rt_transient_array_scope_begin());
            assert_eq!(rt_transient_array_scope_state_v1(), 1);
            assert!(!rt_transient_array_scope_begin());
            assert_eq!(rt_transient_array_scope_state_v1(), 1);
            assert!(rt_transient_array_scope_pause());
            assert_eq!(rt_transient_array_scope_state_v1(), 2);
            assert!(rt_transient_array_scope_end());
            assert_eq!(rt_transient_array_scope_state_v1(), 0);
        }).join().unwrap();
        assert_eq!(rt_transient_array_scope_state_v1(), main_state);
    }
    assert!(rt_transient_array_scope_end());
    assert_eq!(rt_transient_array_scope_state_v1(), 0);
}

#[test]
fn promote_cost_is_proportional_to_reachable_not_scope_size() {
    // Many tracked objects, then many small promotions while paused: each
    // promotion must not rescan the whole scope (it was O(objects) twice per
    // call -- ~50% of a stage2 parse profile, 2026-10-24).
    assert!(rt_transient_array_scope_begin());
    let mut kept = Vec::new();
    for i in 0..200_000u64 {
        let array = rt_array_new(1);
        assert!(!array.is_nil());
        if i % 400 == 0 {
            kept.push(array);
        }
    }
    assert!(rt_transient_array_scope_pause());
    let started = std::time::Instant::now();
    for array in &kept {
        assert!(rt_transient_heap_promote(*array));
    }
    let elapsed = started.elapsed();
    // A promoted object is no longer scope owned: promoting it again is the
    // persistent no-op path.
    assert!(rt_transient_heap_promote(kept[0]));
    assert!(rt_transient_array_scope_end());
    // Promoted arrays survived scope end and are still valid.
    for array in &kept {
        assert!(rt_array_push(*array, RuntimeValue::from_int(7)));
        rt_array_free(*array);
    }
    eprintln!("promote_cost: {} promotions over 200000 tracked in {:?}", kept.len(), elapsed);
    assert!(elapsed < std::time::Duration::from_secs(2), "promotion rescans the scope: {:?}", elapsed);
}

#[test]
#[ignore]
fn zz_heap_registry_scaling_bench() {
    for threads in [1usize, 8, 40, 80] {
        let per = 2_000_000 / threads.max(1) * 1;
        let started = std::time::Instant::now();
        let handles: Vec<_> = (0..threads).map(|_| std::thread::spawn(move || {
            let mut keep = Vec::with_capacity(64);
            for i in 0..per {
                let a = rt_array_new(1);
                let _ = rt_array_push(a, RuntimeValue::from_int(i as i64));
                keep.push(a);
                if keep.len() == 64 { for a in keep.drain(..) { rt_array_free(a); } }
            }
            for a in keep.drain(..) { rt_array_free(a); }
        })).collect();
        for h in handles { h.join().unwrap(); }
        let el = started.elapsed();
        eprintln!("registry_bench threads={} total_ops=2000000 elapsed={:?} Mops/s={:.2}", threads, el, 2.0 / el.as_secs_f64());
    }
}

/// Scope-end cost vs registry size. Each scope registers the same `K`
/// objects; only the number of unrelated live registry entries (`n`)
/// changes. Run alone: `cargo test -p simple-runtime --lib
/// transient_scope_end_cost_vs_registry_size -- --ignored --nocapture
/// --test-threads=1`.
#[test]
#[ignore]
fn transient_scope_end_cost_vs_registry_size() {
    const K: usize = 200_000; // > 3 lock chunks
    let mut background: Vec<RuntimeValue> = Vec::new();
    for &n in &[1_000usize, 100_000, 1_000_000, 4_000_000] {
        while background.len() < n {
            background.push(rt_tuple_new(1));
        }
        let mut best = u128::MAX;
        for _ in 0..5 {
            assert!(rt_transient_array_scope_begin());
            for i in 0..K {
                match i % 4 {
                    0 => { rt_tuple_new(1); }
                    1 => { rt_array_new(0); }
                    2 => { let s = format!("transient scope bench {i}"); rt_string_new(s.as_ptr(), s.len() as u64); }
                    _ => { super::super::dict::rt_dict_new(0); }
                }
            }
            let t = std::time::Instant::now();
            assert!(rt_transient_array_scope_end());
            best = best.min(t.elapsed().as_micros());
        }
        println!("scope_end_cost registry_live={n} objects={K} best_us={best} ns_per_obj={}", best * 1000 / K as u128);
    }
    for value in background {
        rt_tuple_free(value);
    }
}

/// The batched scope end frees exactly what the per-object path freed:
/// every unpaused tracked kind, never a shared string, a paused allocation,
/// a promoted (escaping) graph, or an object already freed mid-scope.
#[test]
fn transient_scope_end_batch_frees_only_scope_owned_objects() {
    use super::super::heap::is_registered_heap_ptr;
    let live = |v: RuntimeValue| is_registered_heap_ptr(v.as_heap_ptr());
    assert!(rt_transient_array_scope_begin());
    let s = "batched scope end string";
    let string = rt_string_new(s.as_ptr(), s.len() as u64);
    let shared = rt_string_new(s.as_ptr(), s.len() as u64);
    mark_string_shared(shared);
    let array = rt_array_new(4);
    let tuple = rt_tuple_new(2);
    let dict = super::super::dict::rt_dict_new(4);
    let freed_early = rt_tuple_new(7);
    rt_tuple_free(freed_early);
    let escaping = rt_array_new(1);
    let child = rt_tuple_new(1);
    assert!(rt_array_push(escaping, child));
    assert!(rt_transient_array_scope_pause());
    let paused = rt_tuple_new(1);
    assert!(rt_transient_heap_promote(escaping));
    assert!(rt_transient_array_scope_end());

    // `freed_early` is not checked: a later allocation may legitimately reuse
    // its address. The duplicate-entry case is pinned deterministically below.
    for v in [string, array, tuple, dict] {
        assert!(!live(v));
    }
    for v in [shared, escaping, child, paused] {
        assert!(live(v));
    }
    assert_eq!(rt_array_get(escaping, 0).0, child.0);
    unsafe { (*shared.as_heap_ptr()).reserved &= !RT_STRING_FLAG_SHARED };
    assert_eq!(rt_string_free(shared), 1);
    rt_array_free(escaping);
    rt_tuple_free(child);
    rt_tuple_free(paused);
}

/// Closures keep the per-object path: an unpinned one is freed at scope end,
/// a pinned one is orphaned and freed by its last release. The generic arm
/// (Object/Enum/Int/Float boxes) is freed by the batch.
#[test]
fn transient_scope_end_batch_handles_closures_and_generic_boxes() {
    extern "C" fn closure_body() {}
    use super::super::heap::is_registered_heap_ptr;
    use super::super::objects::{rt_closure_new, rt_closure_release, rt_closure_retain, rt_enum_new, rt_object_new};
    let live = |v: RuntimeValue| is_registered_heap_ptr(v.as_heap_ptr());
    assert!(rt_transient_array_scope_begin());
    let body = closure_body as *const () as *const u8;
    let unpinned = rt_closure_new(body, 0);
    let pinned = rt_closure_new(body, 1);
    assert_eq!(rt_closure_retain(pinned), 1);
    let object = rt_object_new(7, 2);
    let enum_value = rt_enum_new(77, 3, RuntimeValue::NIL);
    let wide_int = RuntimeValue::from_int(i64::MAX);
    let float = RuntimeValue::from_float(0.125);
    let boxes = [object, enum_value, wide_int, float];
    assert!(boxes.iter().all(|v| v.is_heap() && live(*v)));
    assert!(rt_transient_array_scope_end());

    assert!(!live(unpinned));
    assert!(boxes.iter().all(|v| !live(*v)));
    assert!(live(pinned), "a pinned closure outlives its scope");
    assert_eq!(rt_closure_release(pinned), 1);
    assert!(!live(pinned), "its last release frees it");
}

/// A stale duplicate entry (an address freed and reallocated mid-scope is
/// tracked twice) is erased exactly once even when the two entries fall in
/// different lock chunks. The batch never frees: the caller deallocates only
/// after the last chunk, so the address cannot be recycled in between.
/// Chunks are per registry shard, so the filler is drawn from the target's
/// shard only (other allocations are freed again) to really span two chunks.
/// Ignored by default: it holds ~4.2M tuples (~300 MB) to fill one shard past a
/// 64K chunk, and that alloc/free storm races the process-global
/// `rt_heap_registry_count()` assertions in sibling tests. Run it alone:
/// `cargo test -p simple-runtime --lib transient_scope_end_batch_erases_cross_chunk_duplicate_once -- --ignored`
#[test]
#[ignore = "heavy (~4.2M tuples); run alone with --ignored"]
fn transient_scope_end_batch_erases_cross_chunk_duplicate_once() {
    use super::super::heap::{
        heap_registry_shard_index, is_registered_heap_ptr, unregister_heap_ptrs_batch, HEAP_UNREGISTER_BATCH_CHUNK,
    };
    let target = rt_tuple_new(3);
    let shard = heap_registry_shard_index(target.as_heap_ptr() as usize);
    let mut candidates = vec![target];
    let mut other_shards = Vec::new();
    while candidates.len() < HEAP_UNREGISTER_BATCH_CHUNK + 16 {
        let filler = rt_tuple_new(1);
        if heap_registry_shard_index(filler.as_heap_ptr() as usize) == shard {
            candidates.push(filler);
        } else {
            other_shards.push(filler);
        }
    }
    for filler in other_shards {
        rt_tuple_free(filler);
    }
    candidates.push(target);
    let mut erased = Vec::new();
    unregister_heap_ptrs_batch(&candidates, |_, _| true, &mut erased);
    assert_eq!(erased.len(), candidates.len() - 1, "the duplicate is skipped");
    assert_eq!(erased.iter().filter(|(ptr, _)| *ptr == target.as_heap_ptr()).count(), 1);
    assert!(!is_registered_heap_ptr(target.as_heap_ptr()));
    for (ptr, kind) in erased {
        unsafe { dealloc_erased_transient(ptr, kind) };
    }
}
