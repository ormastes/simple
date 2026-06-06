use super::*;
use std::sync::atomic::{AtomicI32, AtomicI64};
use std::time::Duration;

#[test]
fn test_threaded_mode() {
    let executor = FutureExecutor::new(AsyncMode::Threaded);
    executor.set_worker_count(2);
    executor.start();

    let counter = Arc::new(AtomicI32::new(0));
    let counter_clone = counter.clone();

    executor.submit(move || {
        counter_clone.fetch_add(1, Ordering::SeqCst);
    });

    // Wait a bit for the task to complete
    thread::sleep(Duration::from_millis(100));

    assert_eq!(counter.load(Ordering::SeqCst), 1);
    executor.shutdown();
}

#[test]
fn test_threaded_mode_current_task_id() {
    let executor = FutureExecutor::new(AsyncMode::Threaded);
    executor.set_worker_count(1);
    executor.start();

    let observed = Arc::new(AtomicI64::new(0));
    let observed_clone = observed.clone();

    let task_id = executor.submit(move || {
        observed_clone.store(rt_executor_current_task_id(), Ordering::SeqCst);
    });

    let deadline = std::time::Instant::now() + Duration::from_millis(500);
    while observed.load(Ordering::SeqCst) == 0 && std::time::Instant::now() < deadline {
        thread::sleep(Duration::from_millis(5));
    }

    assert_eq!(observed.load(Ordering::SeqCst), task_id as i64);
    assert_eq!(rt_executor_current_task_id(), 0);
    executor.shutdown();
}

#[test]
fn test_manual_mode() {
    let executor = FutureExecutor::new(AsyncMode::Manual);

    let counter = Arc::new(AtomicI32::new(0));
    let counter_clone = counter.clone();

    executor.submit(move || {
        counter_clone.fetch_add(1, Ordering::SeqCst);
    });

    // Task should not execute until polled
    assert_eq!(counter.load(Ordering::SeqCst), 0);
    assert_eq!(executor.pending_count(), 1);

    // Now poll
    assert!(executor.poll_one());
    assert_eq!(counter.load(Ordering::SeqCst), 1);
    assert_eq!(executor.pending_count(), 0);
}

#[test]
fn test_manual_mode_current_task_id() {
    let executor = FutureExecutor::new(AsyncMode::Manual);

    let observed = Arc::new(AtomicI64::new(0));
    let observed_clone = observed.clone();

    let task_id = executor.submit(move || {
        observed_clone.store(rt_executor_current_task_id(), Ordering::SeqCst);
    });

    assert_eq!(rt_executor_current_task_id(), 0);
    assert!(executor.poll_one());
    assert_eq!(observed.load(Ordering::SeqCst), task_id as i64);
    assert_eq!(rt_executor_current_task_id(), 0);
}

#[test]
fn test_promise() {
    let promise: Promise<i32> = Promise::new();
    let promise_clone = promise.clone();

    assert_eq!(promise.state(), PromiseState::Pending);

    thread::spawn(move || {
        thread::sleep(Duration::from_millis(10));
        promise_clone.resolve(42);
    });

    let result = promise.wait();
    assert_eq!(result, Ok(42));
    assert_eq!(promise.state(), PromiseState::Fulfilled);
}

#[test]
fn test_promise_reject() {
    let promise: Promise<i32> = Promise::new();
    promise.reject("error".to_string());

    assert_eq!(promise.state(), PromiseState::Rejected);
    assert_eq!(promise.try_get(), Some(Err("error".to_string())));
}

// ========================================================================
// Isolated Thread tests
// ========================================================================

fn native_closure_record(func: *const ()) -> Box<usize> {
    Box::new(func as usize)
}

extern "C" fn double_value(_closure: u64, v: RuntimeValue) -> RuntimeValue {
    let n = v.as_int();
    RuntimeValue::from_int(n * 2)
}

extern "C" fn add_values(_closure: u64, v1: RuntimeValue, v2: RuntimeValue) -> RuntimeValue {
    let a = v1.as_int();
    let b = v2.as_int();
    RuntimeValue::from_int(a + b)
}

#[test]
fn test_isolated_thread_spawn_and_join() {
    let closure = native_closure_record(double_value as *const ());
    let handle = rt_thread_spawn_isolated((&*closure) as *const usize as u64, RuntimeValue::from_int(21));

    assert!(handle != 0);
    assert!(rt_thread_id(handle) > 0);

    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);

    rt_thread_free(handle);
}

#[test]
fn test_isolated_thread_spawn_with_args_and_join() {
    let closure = native_closure_record(add_values as *const ());
    let handle = rt_thread_spawn_isolated_with_args(
        (&*closure) as *const usize as u64,
        RuntimeValue::from_int(10),
        RuntimeValue::from_int(32),
    );

    assert!(handle != 0);

    let result = rt_thread_join(handle);
    assert!(result.is_int());
    assert_eq!(result.as_int(), 42);

    rt_thread_free(handle);
}

#[test]
fn test_isolated_thread_is_done() {
    extern "C" fn slow_work(_closure: u64, v: RuntimeValue) -> RuntimeValue {
        thread::sleep(Duration::from_millis(50));
        v
    }

    let closure = native_closure_record(slow_work as *const ());
    let handle = rt_thread_spawn_isolated((&*closure) as *const usize as u64, RuntimeValue::from_int(1));

    // Thread should not be done immediately
    assert_eq!(rt_thread_is_done(handle), 0);

    // Wait for completion
    let result = rt_thread_join(handle);
    assert!(result.is_int());

    // Now should be done
    assert_eq!(rt_thread_is_done(handle), 1);

    rt_thread_free(handle);
}

#[test]
fn test_thread_available_parallelism() {
    let cores = rt_thread_available_parallelism();
    assert!(cores >= 1);
}

#[test]
fn test_thread_sleep() {
    let start = std::time::Instant::now();
    rt_thread_sleep(50);
    let elapsed = start.elapsed();
    assert!(elapsed >= Duration::from_millis(40));
}

#[test]
fn test_thread_yield() {
    // Just verify it doesn't panic
    rt_thread_yield();
}
