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
