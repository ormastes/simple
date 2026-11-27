//! Native core-C observer provider. Compiled directly as a no_std object only
//! by the explicit Rust-observer core capsule builder selection. Never included
//! in the default runtime cdylib, whose RuntimeValue arrays have another ABI.
#![no_std]

use core::ffi::c_void;

#[repr(C)]
struct Observation {
    version: i64,
    owner_error: i64,
    stdout_state: i64,
    exit_kind: i64,
    exit_value: i64,
    exit_error: i64,
}

const _: [(); 48] = [(); core::mem::size_of::<Observation>()];
const _: [(); 8] = [(); core::mem::size_of::<*mut c_void>()];
const _: [(); core::mem::align_of::<i64>()] = [(); core::mem::align_of::<Observation>()];
const _: [(); 0] = [(); core::mem::offset_of!(Observation, version)];
const _: [(); 8] = [(); core::mem::offset_of!(Observation, owner_error)];
const _: [(); 16] = [(); core::mem::offset_of!(Observation, stdout_state)];
const _: [(); 24] = [(); core::mem::offset_of!(Observation, exit_kind)];
const _: [(); 32] = [(); core::mem::offset_of!(Observation, exit_value)];
const _: [(); 40] = [(); core::mem::offset_of!(Observation, exit_error)];
const INVALID_RECORD: i64 = if cfg!(windows) { 13 } else { 22 };

unsafe extern "C" {
    fn simple_piped_owner_observe_v1(pid: i64, collect_exit: i64, out: *mut Observation, out_size: i64);
    fn simple_piped_receipt_new_v1(state: i64, code: i64, error: i64) -> *mut c_void;
}

fn observe(pid: i64, collect_exit: i64) -> Observation {
    // Fail closed even if an incorrectly linked owner fails to initialize.
    let mut out = Observation { version: 0, owner_error: 1, stdout_state: -1,
        exit_kind: -1, exit_value: 0, exit_error: 1 };
    unsafe { simple_piped_owner_observe_v1(pid, collect_exit, &mut out, 48) };
    out
}

#[no_mangle]
pub extern "C" fn rt_process_stdout_state(pid: i64) -> i64 {
    let out = observe(pid, 0);
    if out.version != 1 || out.owner_error != 0 { return -1; }
    match out.stdout_state { -1 | 0 | 1 => out.stdout_state, _ => -1 }
}

#[no_mangle]
pub extern "C" fn rt_process_piped_exit_status_value(pid: i64) -> *mut c_void {
    let out = observe(pid, 1);
    let (state, code, error) = if out.version != 1 {
        (-1, 0, INVALID_RECORD)
    } else if out.owner_error != 0 {
        (-1, 0, out.owner_error)
    } else if out.stdout_state == -1 {
        (-1, 0, if out.exit_error != 0 { out.exit_error } else { INVALID_RECORD })
    } else if out.stdout_state == 0 {
        (0, 0, 0)
    } else if out.stdout_state != 1 {
        (-1, 0, INVALID_RECORD)
    } else {
        match out.exit_kind {
            0 => (0, 0, 0),
            1 if out.exit_value >= 0 && out.exit_value <= u32::MAX as i64 => (1, out.exit_value, 0),
            2 if out.exit_value > 0 && out.exit_value < 128 => (1, 128 + out.exit_value, 0),
            -1 => (-1, 0, if out.exit_error != 0 { out.exit_error } else { INVALID_RECORD }),
            _ => (-1, 0, INVALID_RECORD),
        }
    };
    // C owns native tagged-array allocation and the caller owns the result.
    // This is allocation only; all receipt policy above is evaluated in Rust.
    unsafe { simple_piped_receipt_new_v1(state, code, error) }
}
