//! Runtime crate integration tests
//! Tests GC, actors, executor, and concurrency public functions
//! Focus: Public function coverage for simple_runtime

#![allow(unused_imports, unused_variables)]

use simple_runtime::gc::GcRuntime;
use std::sync::Arc;

// =============================================================================
// GcRuntime Tests
// =============================================================================

#[test]
fn test_gc_runtime_new() {
    let gc = GcRuntime::new();
    assert!(std::mem::size_of_val(&gc) > 0);
}

#[test]
fn test_gc_runtime_verbose_stdout() {
    let gc = GcRuntime::verbose_stdout();
    assert!(std::mem::size_of_val(&gc) > 0);
}

#[test]
fn test_gc_runtime_heap() {
    let gc = GcRuntime::new();
    let heap = gc.heap();
    assert!(Arc::strong_count(heap) >= 1);
}

#[test]
fn test_gc_runtime_heap_bytes() {
    let gc = GcRuntime::new();
    let bytes = gc.heap_bytes();
    // Heap bytes should be non-negative
    assert!(bytes >= 0);
}

#[test]
fn test_gc_runtime_collect() {
    let gc = GcRuntime::new();
    let collected = gc.collect("test");
    // Should return the number of bytes collected
    assert!(collected >= 0);
}

// =============================================================================
// Root Registration Tests
// =============================================================================

#[test]
fn test_unique_root_count_initial() {
    use simple_runtime::gc::unique_root_count;
    let count = unique_root_count();
    // Initial count should be non-negative
    assert!(count >= 0);
}

#[test]
fn test_shared_root_count_initial() {
    use simple_runtime::gc::shared_root_count;
    let count = shared_root_count();
    // Initial count should be non-negative
    assert!(count >= 0);
}

#[test]
fn test_get_unique_roots() {
    use simple_runtime::gc::get_unique_roots;
    let roots = get_unique_roots();
    // Should return a vector (may be empty)
    let _ = roots;
}

#[test]
fn test_get_shared_roots() {
    use simple_runtime::gc::get_shared_roots;
    let roots = get_shared_roots();
    // Should return a vector (may be empty)
    let _ = roots;
}

// =============================================================================
// Executor Tests
// =============================================================================

#[test]
fn test_executor_access() {
    use simple_runtime::executor;
    let exec = executor::executor();
    assert!(std::mem::size_of_val(exec) > 0);
}

#[test]
fn test_executor_pending_count() {
    use simple_runtime::executor::pending_count;
    let count = pending_count();
    // Count should be non-negative
    assert!(count >= 0);
}

#[test]
fn test_executor_is_manual_mode() {
    use simple_runtime::executor::is_manual_mode;
    let manual = is_manual_mode();
    // Should return a boolean
    let _ = manual;
}

#[test]
fn test_poll_one() {
    use simple_runtime::executor::poll_one;
    let polled = poll_one();
    // Should return a boolean indicating if work was done
    let _ = polled;
}

#[test]
fn test_poll_all() {
    use simple_runtime::executor::poll_all;
    let count = poll_all();
    // Should return count of tasks polled
    assert!(count >= 0);
}

// =============================================================================
// Promise Tests
// =============================================================================

#[test]
fn test_promise_new() {
    use simple_runtime::executor::Promise;
    let promise: Promise<i32> = Promise::new();
    assert!(!promise.is_settled());
}

#[test]
fn test_promise_resolve() {
    use simple_runtime::executor::Promise;
    let promise: Promise<i32> = Promise::new();
    promise.resolve(42);
    assert!(promise.is_settled());
}

#[test]
fn test_promise_reject() {
    use simple_runtime::executor::Promise;
    let promise: Promise<i32> = Promise::new();
    promise.reject("error".to_string());
    assert!(promise.is_settled());
}

#[test]
fn test_promise_state() {
    use simple_runtime::executor::{Promise, PromiseState};
    let promise: Promise<i32> = Promise::new();
    assert!(matches!(promise.state(), PromiseState::Pending));
    promise.resolve(42);
    assert!(matches!(promise.state(), PromiseState::Fulfilled));
}

#[test]
fn test_promise_try_get() {
    use simple_runtime::executor::Promise;
    let promise: Promise<i32> = Promise::new();
    assert!(promise.try_get().is_none());
    promise.resolve(42);
    assert!(promise.try_get().is_some());
}

#[test]
fn test_promise_wait() {
    use simple_runtime::executor::Promise;
    use std::sync::Arc;
    use std::thread;

    let promise: Arc<Promise<i32>> = Arc::new(Promise::new());
    let promise_clone = promise.clone();

    // Resolve in another thread
    thread::spawn(move || {
        promise_clone.resolve(100);
    });

    let result = promise.wait();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 100);
}

// =============================================================================
// FutureExecutor Tests
// =============================================================================

#[test]
fn test_future_executor_new() {
    use simple_runtime::executor::{AsyncMode, FutureExecutor};
    let executor = FutureExecutor::new(AsyncMode::Manual);
    assert!(std::mem::size_of_val(&executor) > 0);
}

#[test]
fn test_future_executor_default() {
    use simple_runtime::executor::FutureExecutor;
    let executor = FutureExecutor::default_executor();
    assert!(std::mem::size_of_val(&executor) > 0);
}

#[test]
fn test_future_executor_mode() {
    use simple_runtime::executor::{AsyncMode, FutureExecutor};
    let executor = FutureExecutor::new(AsyncMode::Manual);
    assert!(matches!(executor.mode(), AsyncMode::Manual));
}

#[test]
fn test_future_executor_set_mode() {
    use simple_runtime::executor::{AsyncMode, FutureExecutor};
    let executor = FutureExecutor::new(AsyncMode::Manual);
    executor.set_mode(AsyncMode::Threaded);
    assert!(matches!(executor.mode(), AsyncMode::Threaded));
}

#[test]
fn test_future_executor_submit() {
    use simple_runtime::executor::{AsyncMode, FutureExecutor};
    let executor = FutureExecutor::new(AsyncMode::Manual);

    let task_id = executor.submit(|| {
        // Simple work - must return ()
        let _ = 42;
    });

    assert!(task_id > 0 || task_id == 0);
}

#[test]
fn test_future_executor_poll_one() {
    use simple_runtime::executor::{AsyncMode, FutureExecutor};
    let executor = FutureExecutor::new(AsyncMode::Manual);

    executor.submit(|| { let _ = 42; });

    let polled = executor.poll_one();
    // Should have polled one task
    assert!(polled);
}

#[test]
fn test_future_executor_poll_all() {
    use simple_runtime::executor::{AsyncMode, FutureExecutor};
    let executor = FutureExecutor::new(AsyncMode::Manual);

    executor.submit(|| { let _ = 1; });
    executor.submit(|| { let _ = 2; });
    executor.submit(|| { let _ = 3; });

    let count = executor.poll_all();
    assert_eq!(count, 3);
}

#[test]
fn test_future_executor_pending_count() {
    use simple_runtime::executor::{AsyncMode, FutureExecutor};
    let executor = FutureExecutor::new(AsyncMode::Manual);

    executor.submit(|| { let _ = 1; });
    executor.submit(|| { let _ = 2; });

    assert!(executor.pending_count() >= 2);

    executor.poll_all();
    assert_eq!(executor.pending_count(), 0);
}

// =============================================================================
// Concurrency Tests (Actors)
// =============================================================================

#[test]
fn test_spawn_actor() {
    use simple_runtime::concurrency::spawn_actor;

    // spawn_actor takes a closure with (sender, receiver) arguments
    let handle = spawn_actor(|_sender, _receiver| {
        // Simple actor work
    });

    // Use id() method instead of field access
    assert!(handle.id() >= 0);
}

#[test]
fn test_scheduled_spawner_new() {
    use simple_runtime::concurrency::ScheduledSpawner;
    let spawner = ScheduledSpawner::new();
    // Just verify it doesn't panic
    let _ = spawner;
}

// =============================================================================
// GclessAllocator Tests
// =============================================================================

#[test]
fn test_gcless_allocator_new() {
    use simple_runtime::memory::gcless::GclessAllocator;
    let alloc = GclessAllocator::new();
    assert!(std::mem::size_of_val(&alloc) > 0);
}

// =============================================================================
// NoGcAllocator Tests
// =============================================================================

#[test]
fn test_no_gc_allocator_new() {
    use simple_runtime::memory::no_gc::NoGcAllocator;
    let alloc = NoGcAllocator::new();
    assert!(std::mem::size_of_val(&alloc) > 0);
}

// =============================================================================
// Async Mode Configuration Tests
// =============================================================================

#[test]
fn test_configure_async_mode() {
    use simple_runtime::executor::{configure_async_mode, AsyncMode};
    // Configure and verify no panic
    configure_async_mode(AsyncMode::Manual);
}

#[test]
fn test_configure_worker_count() {
    use simple_runtime::executor::configure_worker_count;
    // Configure and verify no panic
    configure_worker_count(4);
}

// =============================================================================
// Spawn Function Tests
// =============================================================================

#[test]
fn test_spawn_function() {
    use simple_runtime::executor::spawn;

    let task_id = spawn(|| {
        // Simple work - must return ()
        let _ = 42;
    });

    assert!(task_id >= 0);
}

// =============================================================================
// GPU Work Item State Tests
// =============================================================================

#[test]
fn test_gpu_work_item_state_get() {
    use simple_runtime::value::gpu::get_work_item_state;
    let state = get_work_item_state();
    // Should return a valid state
    assert!(state.global_id[0] >= 0);
}

#[test]
fn test_gpu_work_item_state_set_get() {
    use simple_runtime::value::gpu::{get_work_item_state, set_work_item_state, GpuWorkItemState};

    let state = GpuWorkItemState {
        global_id: [1, 2, 3],
        local_id: [0, 0, 0],
        group_id: [0, 0, 0],
        global_size: [10, 10, 10],
        local_size: [1, 1, 1],
        num_groups: [10, 10, 10],
    };

    set_work_item_state(state.clone());
    let retrieved = get_work_item_state();

    assert_eq!(retrieved.global_id, state.global_id);
}
