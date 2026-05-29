//! Task identity bridge for future stackful fiber runtimes.
//!
//! The runtime does not own a fiber scheduler yet, but fiber backends need a
//! stable way to participate in `rt_current_task_id` without becoming ambient
//! thread-local security state. A fiber scheduler enters the current fiber task
//! before polling/running it and restores the previous value afterward.

use std::cell::Cell;

thread_local! {
    static CURRENT_FIBER_TASK_ID: Cell<u64> = const { Cell::new(0) };
}

#[no_mangle]
pub extern "C" fn rt_fiber_enter_task_id(task_id: i64) -> i64 {
    let normalized = if task_id > 0 { task_id as u64 } else { 0 };
    CURRENT_FIBER_TASK_ID.with(|cell| {
        let previous = cell.get();
        cell.set(normalized);
        previous as i64
    })
}

#[no_mangle]
pub extern "C" fn rt_fiber_exit_task_id(previous_task_id: i64) {
    let normalized = if previous_task_id > 0 {
        previous_task_id as u64
    } else {
        0
    };
    CURRENT_FIBER_TASK_ID.with(|cell| cell.set(normalized));
}

#[no_mangle]
pub extern "C" fn rt_fiber_current_task_id() -> i64 {
    CURRENT_FIBER_TASK_ID.with(|cell| cell.get() as i64)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fiber_task_identity_restores_previous_scope() {
        assert_eq!(rt_fiber_current_task_id(), 0);
        let previous_outer = rt_fiber_enter_task_id(41);
        assert_eq!(previous_outer, 0);
        assert_eq!(rt_fiber_current_task_id(), 41);

        let previous_inner = rt_fiber_enter_task_id(99);
        assert_eq!(previous_inner, 41);
        assert_eq!(rt_fiber_current_task_id(), 99);

        rt_fiber_exit_task_id(previous_inner);
        assert_eq!(rt_fiber_current_task_id(), 41);
        rt_fiber_exit_task_id(previous_outer);
        assert_eq!(rt_fiber_current_task_id(), 0);
    }
}
