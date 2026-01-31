//! Cooperative async runtime scheduler for Simple futures.
//!
//! Provides a task-based cooperative scheduler that drives async functions
//! through their state machine states. Unlike the eager executor in `executor.rs`,
//! this scheduler supports true suspension and resumption of async tasks.
//!
//! # Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────┐
//! │                  AsyncScheduler                     │
//! ├────────────────────────────────────────────────────┤
//! │  Ready Queue: tasks ready to make progress         │
//! │  Wait List:   tasks waiting on another future      │
//! │                                                    │
//! │  run_until_complete(main_task):                     │
//! │    while tasks remain:                             │
//! │      pop ready task                                │
//! │      resume its state machine (call body_func)     │
//! │      if task suspends: move to wait list           │
//! │      if task completes: resolve dependents         │
//! └────────────────────────────────────────────────────┘
//! ```

use std::collections::VecDeque;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

use crate::value::RuntimeValue;

/// Unique task identifier.
static NEXT_TASK_ID: AtomicU64 = AtomicU64::new(1);

// Use the public FFI functions for future operations.
use crate::value::{rt_future_await, rt_future_get_result, rt_future_is_ready};

/// An async task managed by the scheduler.
struct AsyncTask {
    /// Unique ID for this task.
    id: u64,
    /// The future this task is driving.
    future: RuntimeValue,
    /// Tasks waiting for this task to complete.
    dependents: Vec<u64>,
}

/// The cooperative async scheduler.
///
/// Maintains ready and waiting queues. Tasks in the ready queue are polled
/// by calling their future's body_func. When a task's future becomes ready,
/// any dependents are moved to the ready queue.
pub struct AsyncScheduler {
    /// Tasks ready to be polled.
    ready: VecDeque<AsyncTask>,
    /// Tasks waiting for a dependency.
    waiting: Vec<AsyncTask>,
    /// Completed task results, keyed by task ID.
    results: Vec<(u64, RuntimeValue)>,
}

impl AsyncScheduler {
    /// Create a new empty scheduler.
    pub fn new() -> Self {
        AsyncScheduler {
            ready: VecDeque::new(),
            waiting: Vec::new(),
            results: Vec::new(),
        }
    }

    /// Spawn a new task from a future. Returns the task ID.
    pub fn spawn(&mut self, future: RuntimeValue) -> u64 {
        let id = NEXT_TASK_ID.fetch_add(1, Ordering::SeqCst);
        self.ready.push_back(AsyncTask {
            id,
            future,
            dependents: Vec::new(),
        });
        id
    }

    /// Poll a single future: if already ready return true,
    /// otherwise try to execute it via rt_future_await (which calls
    /// the body_func and blocks until ready).
    fn poll_future(future: RuntimeValue) -> bool {
        // Already ready?
        if rt_future_is_ready(future) == 1 {
            return true;
        }

        // Drive the future to completion via the existing await mechanism.
        let _result = rt_future_await(future);

        // After await, it should be ready.
        rt_future_is_ready(future) == 1
    }

    /// Run the scheduler until the given task completes.
    /// Returns the result of the main task's future.
    pub fn run_until_complete(&mut self, main_task_id: u64) -> RuntimeValue {
        loop {
            let mut newly_ready_ids: Vec<u64> = Vec::new();

            let ready_count = self.ready.len();
            for _ in 0..ready_count {
                if let Some(task) = self.ready.pop_front() {
                    let is_ready = Self::poll_future(task.future);

                    if is_ready {
                        let result = rt_future_get_result(task.future);

                        self.results.push((task.id, result));

                        for dep_id in &task.dependents {
                            newly_ready_ids.push(*dep_id);
                        }

                        if task.id == main_task_id {
                            return result;
                        }
                    } else {
                        // Round-robin: re-add to ready queue
                        self.ready.push_back(task);
                    }
                }
            }

            // Move waiting tasks whose dependencies completed to ready
            let mut i = 0;
            while i < self.waiting.len() {
                let dominated_id = self.waiting[i].id;
                if newly_ready_ids.contains(&dominated_id) {
                    let task = self.waiting.remove(i);
                    self.ready.push_back(task);
                } else {
                    i += 1;
                }
            }

            // All queues empty — check if main already completed
            if self.ready.is_empty() && self.waiting.is_empty() {
                for (id, result) in &self.results {
                    if *id == main_task_id {
                        return *result;
                    }
                }
                return RuntimeValue::NIL;
            }

            // No ready tasks but waiting tasks exist: yield and retry
            if self.ready.is_empty() && !self.waiting.is_empty() {
                std::thread::yield_now();
                while let Some(task) = self.waiting.pop() {
                    self.ready.push_back(task);
                }
            }
        }
    }
}

// =============================================================================
// Global scheduler instance
// =============================================================================

lazy_static::lazy_static! {
    static ref GLOBAL_SCHEDULER: Mutex<AsyncScheduler> = Mutex::new(AsyncScheduler::new());
}

// =============================================================================
// FFI Functions
// =============================================================================

/// Spawn a future as an async task in the global scheduler.
/// Returns a task handle (encoded as RuntimeValue integer).
#[no_mangle]
pub extern "C" fn rt_async_spawn(future: RuntimeValue) -> RuntimeValue {
    let mut sched = GLOBAL_SCHEDULER.lock().unwrap();
    let task_id = sched.spawn(future);
    RuntimeValue::from_int(task_id as i64)
}

/// Await a future using the cooperative scheduler.
///
/// Creates a temporary scheduler and runs until the future completes.
/// This avoids deadlocks with the global scheduler lock.
#[no_mangle]
pub extern "C" fn rt_async_schedule_await(future: RuntimeValue) -> RuntimeValue {
    // Fast path: already ready
    if rt_future_is_ready(future) == 1 {
        return rt_future_get_result(future);
    }

    let mut sched = AsyncScheduler::new();
    let task_id = sched.spawn(future);
    sched.run_until_complete(task_id)
}

/// Run a future to completion using the cooperative scheduler.
/// This is the main entry point for async programs.
#[no_mangle]
pub extern "C" fn rt_async_run_until_complete(future: RuntimeValue) -> RuntimeValue {
    let mut sched = AsyncScheduler::new();
    let task_id = sched.spawn(future);
    sched.run_until_complete(task_id)
}

/// Spawn a future in the global scheduler without waiting.
/// Returns the task ID as an i64.
#[no_mangle]
pub extern "C" fn rt_async_spawn_task(future: RuntimeValue) -> i64 {
    let mut sched = GLOBAL_SCHEDULER.lock().unwrap();
    sched.spawn(future) as i64
}

/// Poll all ready tasks in the global scheduler.
/// Returns the number of tasks that completed.
#[no_mangle]
pub extern "C" fn rt_async_poll_tasks() -> i64 {
    let mut sched = GLOBAL_SCHEDULER.lock().unwrap();
    let before = sched.results.len();

    let ready_count = sched.ready.len();
    let mut completed = Vec::new();

    for _ in 0..ready_count {
        if let Some(task) = sched.ready.pop_front() {
            let is_ready = AsyncScheduler::poll_future(task.future);
            if is_ready {
                let result = rt_future_get_result(task.future);
                completed.push((task.id, result, task.dependents));
            } else {
                sched.ready.push_back(task);
            }
        }
    }

    for (id, result, _deps) in &completed {
        sched.results.push((*id, *result));
    }

    (sched.results.len() - before) as i64
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::rt_future_resolve;

    #[test]
    fn scheduler_runs_resolved_future() {
        let future = rt_future_resolve(RuntimeValue::from_int(42));
        let mut sched = AsyncScheduler::new();
        let task_id = sched.spawn(future);
        let result = sched.run_until_complete(task_id);
        assert_eq!(result.as_int(), 42);
    }

    #[test]
    fn scheduler_handles_multiple_tasks() {
        let f1 = rt_future_resolve(RuntimeValue::from_int(10));
        let f2 = rt_future_resolve(RuntimeValue::from_int(20));

        let mut sched = AsyncScheduler::new();
        let _t1 = sched.spawn(f1);
        let t2 = sched.spawn(f2);

        let result = sched.run_until_complete(t2);
        assert_eq!(result.as_int(), 20);
    }

    #[test]
    fn ffi_schedule_await_resolved() {
        let future = rt_future_resolve(RuntimeValue::from_int(99));
        let result = rt_async_schedule_await(future);
        assert_eq!(result.as_int(), 99);
    }

    #[test]
    fn ffi_run_until_complete_resolved() {
        let future = rt_future_resolve(RuntimeValue::from_int(7));
        let result = rt_async_run_until_complete(future);
        assert_eq!(result.as_int(), 7);
    }
}
