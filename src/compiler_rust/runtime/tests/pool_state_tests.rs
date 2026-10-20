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

// A closure submitted to the pool must stay alive until its task has run, even
// when the submitter's transient scope (its only owner) ends first. The boxed
// entry blocks on GATE before reading its capture, so the read happens after
// the scope end. Before the pool retained closures, the capture read a freed
// closure (nil) and the task answered a wrong value.
static CLOSURE_GATE: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
static CLOSURE_ENTERED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);

extern "C" fn add_capture_after_gate(closure: crate::value::RuntimeValue, tagged: crate::value::RuntimeValue) -> crate::value::RuntimeValue {
    use std::sync::atomic::Ordering;
    CLOSURE_ENTERED.store(true, Ordering::SeqCst);
    while !CLOSURE_GATE.load(Ordering::SeqCst) {
        std::thread::yield_now();
    }
    let capture = crate::value::rt_closure_get_capture(closure, 0);
    crate::value::rt_value_int(crate::value::rt_value_unbox_int(tagged) + crate::value::rt_value_unbox_int(capture))
}

#[test]
fn submitted_closure_outlives_the_submitters_scope() {
    use std::sync::atomic::Ordering;
    // Open the gate on every exit, so a failed assertion never leaves a worker spinning.
    struct OpenGate;
    impl Drop for OpenGate {
        fn drop(&mut self) {
            CLOSURE_GATE.store(true, std::sync::atomic::Ordering::SeqCst);
        }
    }
    let _open_gate = OpenGate;
    let (retains0, releases0, _) = crate::value::closure_pin_stats();
    unsafe {
        let state = rt_pool_state_create_v1(1);
        assert_ne!(state, 0);
        assert!(crate::value::rt_transient_array_scope_begin());
        let closure = crate::value::rt_closure_new(add_capture_after_gate as usize as *const u8, 1);
        assert!(crate::value::rt_closure_set_capture(closure, 0, crate::value::rt_value_int(7)));
        let task = rt_pool_state_try_submit_i64_v1(state, closure.0 as i64, 5);
        assert!(task > 0);
        // Capacity 1 is full: the refused submit must not keep its retain.
        assert_eq!(rt_pool_state_try_submit_i64_v1(state, closure.0 as i64, 9), -1);
        // Run the scope end while the task is still pending or blocked at the gate.
        while !CLOSURE_ENTERED.load(Ordering::SeqCst) && rt_pool_task_status_i64_v1(task) == 0 {
            std::thread::yield_now();
        }
        assert!(crate::value::rt_transient_array_scope_end());
        CLOSURE_GATE.store(true, Ordering::SeqCst);
        assert_eq!(rt_pool_task_join_i64_v1(task), 12);
        assert_eq!(rt_pool_task_release_i64_v1(task), 1);
        let (retains, releases, _) = crate::value::closure_pin_stats();
        assert_eq!(retains - retains0, 2, "accepted + refused submit");
        assert_eq!(releases - releases0, 2, "every retain released exactly once");
        // The scope ended while pinned, so the last release freed it.
        assert!(crate::value::rt_closure_func_ptr(closure).is_null());
        assert_eq!(crate::value::rt_closure_release(closure), 0, "no pin left: never a double free");
        assert_eq!(rt_pool_state_close_v1(state), 1);
        assert_eq!(rt_pool_state_destroy_v1(state), 1);
    }
}
