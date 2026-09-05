use crate::{
    rt_pool_state_close_v1, rt_pool_state_completed_v1, rt_pool_state_create_v1, rt_pool_state_destroy_v1,
    rt_pool_state_join_idle_v1, rt_pool_state_outstanding_v1, rt_pool_state_try_submit_i64_v1,
    rt_pool_task_join_i64_v1, rt_pool_task_release_i64_v1, rt_pool_task_status_i64_v1,
};

const DIRECT_FUNCTION_MARKER: i64 = 0x5344_4952_4543_5446;

extern "C" fn plus_one(input: i64) -> i64 {
    input + 1
}
extern "C" fn identity(input: i64) -> i64 {
    input
}

unsafe fn submit(state: i64, entry: extern "C" fn(i64) -> i64, input: i64) -> i64 {
    // Native Simple function values are two-word direct-function descriptors.
    // The runtime validates and copies this descriptor before submit returns.
    let descriptor = [entry as usize as i64, DIRECT_FUNCTION_MARKER];
    unsafe { rt_pool_state_try_submit_i64_v1(state, descriptor.as_ptr() as usize as i64, input) }
}

#[test]
fn bounded_pool_state_restores_credit_only_after_release() {
    unsafe {
        let state = rt_pool_state_create_v1(2);
        assert_ne!(state, 0);
        let h1 = submit(state, plus_one, 40);
        let h2 = submit(state, plus_one, 41);
        assert!(h1 > 0 && h2 > 0);
        assert_eq!(rt_pool_state_outstanding_v1(state), 2);
        assert_eq!(submit(state, plus_one, 42), -1);
        assert_eq!(rt_pool_task_join_i64_v1(h1), 41);
        assert_eq!(rt_pool_task_status_i64_v1(h1), 2);
        assert_eq!(rt_pool_state_outstanding_v1(state), 2);
        assert_eq!(rt_pool_task_release_i64_v1(h1), 1);
        assert_eq!(rt_pool_task_release_i64_v1(h1), -1);
        assert_eq!(rt_pool_task_status_i64_v1(h1), -1);
        assert_eq!(rt_pool_state_outstanding_v1(state), 1);
        let h3 = submit(state, plus_one, 42);
        assert!(h3 > 0);
        assert_eq!(rt_pool_state_close_v1(state), 1);
        assert_eq!(submit(state, plus_one, 43), -2);
        assert_eq!(rt_pool_state_join_idle_v1(state), 1);
        assert_eq!(rt_pool_task_join_i64_v1(h2), 42);
        assert_eq!(rt_pool_task_join_i64_v1(h3), 43);
        assert_eq!(rt_pool_state_completed_v1(state), 3);
        assert_eq!(rt_pool_task_release_i64_v1(h2), 1);
        assert_eq!(rt_pool_task_release_i64_v1(h3), 1);
        assert_eq!(rt_pool_state_destroy_v1(state), 1);
        assert_eq!(rt_pool_state_outstanding_v1(state), -1);
    }
}

#[test]
fn pool_handles_reject_stale_forged_and_cross_kind_values() {
    unsafe {
        let state = rt_pool_state_create_v1(1);
        let task = submit(state, identity, 0);
        assert!(state > 0 && task > 0);
        assert_ne!(state, task);
        assert_eq!(rt_pool_task_join_i64_v1(task), 0);
        assert_eq!(rt_pool_task_status_i64_v1(task), 2);
        assert_eq!(rt_pool_task_status_i64_v1(state), -1);
        assert_eq!(rt_pool_state_outstanding_v1(task), -1);
        for forged in [0, -1, task ^ (1_i64 << 16), task & !0xffff_i64] {
            assert_eq!(rt_pool_task_status_i64_v1(forged), -1);
        }
        assert_eq!(rt_pool_task_release_i64_v1(task), 1);
        assert_eq!(rt_pool_task_status_i64_v1(task), -1);
        let replacement = submit(state, identity, 7);
        assert!(replacement > 0);
        assert_ne!(replacement, task);
        assert_eq!(rt_pool_task_join_i64_v1(replacement), 7);
        assert_eq!(rt_pool_task_release_i64_v1(replacement), 1);
        assert_eq!(rt_pool_state_close_v1(state), 1);
        assert_eq!(rt_pool_state_destroy_v1(state), 1);
        assert_eq!(rt_pool_state_outstanding_v1(state), -1);
    }
}

#[test]
fn bounded_state_reuses_task_storage_for_100k_results() {
    unsafe {
        let state = rt_pool_state_create_v1(1);
        assert!(state > 0);
        let mut sampled_stale = Vec::new();
        for input in 0..100_000_i64 {
            let task = submit(state, plus_one, input);
            assert!(task > 0);
            assert!(matches!(rt_pool_task_status_i64_v1(task), 0 | 1));
            assert_eq!(rt_pool_state_outstanding_v1(state), 1);
            assert_eq!(rt_pool_task_join_i64_v1(task), input + 1);
            assert_eq!(rt_pool_task_release_i64_v1(task), 1);
            assert_eq!(rt_pool_task_status_i64_v1(task), -1);
            if input % 1000 == 0 {
                sampled_stale.push(task);
            }
        }
        for stale in sampled_stale {
            assert_eq!(rt_pool_task_status_i64_v1(stale), -1);
        }
        assert_eq!(rt_pool_state_completed_v1(state), 100_000);
        assert_eq!(rt_pool_state_outstanding_v1(state), 0);
        assert_eq!(rt_pool_state_close_v1(state), 1);
        assert_eq!(rt_pool_state_destroy_v1(state), 1);
    }
}

#[test]
fn state_metric_lookup_is_pinned_against_concurrent_destroy() {
    use std::sync::{Arc, Barrier};
    for _ in 0..1_000 {
        unsafe {
            let state = rt_pool_state_create_v1(1);
            assert!(state > 0);
            assert_eq!(rt_pool_state_close_v1(state), 1);
            let barrier = Arc::new(Barrier::new(2));
            let reader_barrier = Arc::clone(&barrier);
            let reader = std::thread::spawn(move || {
                reader_barrier.wait();
                rt_pool_state_outstanding_v1(state)
            });
            barrier.wait();
            assert_eq!(rt_pool_state_destroy_v1(state), 1);
            assert!(matches!(reader.join().unwrap(), 0 | -1));
        }
    }
}

#[test]
fn independent_pool_states_do_not_share_admission_credit() {
    unsafe {
        let a = rt_pool_state_create_v1(1);
        let b = rt_pool_state_create_v1(1);
        let ha = submit(a, plus_one, 6);
        let hb = submit(b, plus_one, 8);
        assert!(ha > 0 && hb > 0);
        assert_eq!(rt_pool_task_join_i64_v1(ha), 7);
        assert_eq!(rt_pool_task_join_i64_v1(hb), 9);
        assert_eq!(rt_pool_task_release_i64_v1(ha), 1);
        assert_eq!(rt_pool_task_release_i64_v1(hb), 1);
        assert_eq!(rt_pool_state_close_v1(a), 1);
        assert_eq!(rt_pool_state_close_v1(b), 1);
        assert_eq!(rt_pool_state_destroy_v1(a), 1);
        assert_eq!(rt_pool_state_destroy_v1(b), 1);
    }
}
