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
