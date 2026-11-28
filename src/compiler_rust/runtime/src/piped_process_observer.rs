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

// Explicit child environment + bounded readiness. Argument policy is evaluated
// here; the canonical C piped registry owns the OS handles, exactly like the
// observers above. Codes mirror runtime_process_observer_private.h.
const PIPED_ENV_INVALID: i64 = -22;
const PIPED_STREAM_STDOUT: i64 = 1;
const PIPED_STREAM_STDERR: i64 = 2;
const PIPED_WAIT_MAX_MS: i64 = 86_400_000;
const PIPED_WAIT_INVALID: i64 = -22;
const PIPED_WAIT_OS_ERROR: i64 = -5;

unsafe extern "C" {
    fn simple_piped_owner_spawn_environment_v1(
        cmd: *const u8, args: *mut c_void, environment: *mut c_void, mode: i64) -> i64;
    fn simple_piped_owner_wait_readable_v1(pid: i64, stream: i64, timeout_ms: i64) -> i64;
}

#[no_mangle]
pub unsafe extern "C" fn rt_process_spawn_piped_environment_v1(
    cmd: *const u8, args: *mut c_void, environment: *mut c_void, mode: i64,
) -> i64 {
    if cmd.is_null() || unsafe { *cmd } == 0 || (mode != 0 && mode != 1) {
        return PIPED_ENV_INVALID;
    }
    let pid = unsafe { simple_piped_owner_spawn_environment_v1(cmd, args, environment, mode) };
    // Only a PID, the rejection code, or the spawn-failure sentinel may escape.
    if pid > 0 || pid == PIPED_ENV_INVALID { pid } else { -1 }
}

#[no_mangle]
pub extern "C" fn rt_process_wait_readable_v1(pid: i64, stream: i64, timeout_ms: i64) -> i64 {
    if pid <= 0 || (stream != PIPED_STREAM_STDOUT && stream != PIPED_STREAM_STDERR)
        || !(0..=PIPED_WAIT_MAX_MS).contains(&timeout_ms) {
        return PIPED_WAIT_INVALID;
    }
    match unsafe { simple_piped_owner_wait_readable_v1(pid, stream, timeout_ms) } {
        code @ (1 | 0 | -2 | -3 | -5 | -22) => code,
        _ => PIPED_WAIT_OS_ERROR,
    }
}

// ---------------------------------------------------------------------------
// Split-stderr / byte-safe piped family: the Rust twin of the C exports at the
// end of src/runtime/runtime_process.c. The C owner keeps the registry and the
// OS handles (one owner, so a C-spawned child is readable from this lane and
// vice versa); this lane owns the caller-facing policy: argument validation,
// per-call caps, packed-vs-boxed [u8] handling, and result allocation through
// the owner's array allocator. Every owner hook is one nonblocking OS step, so
// no export here can park while the child fills the other pipe.
// ---------------------------------------------------------------------------

unsafe extern "C" {
    fn simple_piped_owner_spawn_split_v1(cmd: *const u8, cmd_len: i64, args: *mut c_void) -> i64;
    fn simple_piped_owner_read_v1(pid: i64, stream: i64, out: *mut u8, cap: i64) -> i64;
    fn simple_piped_owner_stream_state_v1(pid: i64, stream: i64) -> i64;
    fn simple_piped_owner_read_stderr_text_v1(pid: i64) -> *const u8;
    fn simple_piped_owner_write_v1(pid: i64, data: *const u8, data_len: i64, offset: i64, max_bytes: i64) -> i64;
    fn simple_piped_bytes_new_v1(data: *const u8, len: i64) -> *mut c_void;
    fn rt_array_bytes_basis_len(array: *mut c_void) -> i64;
    fn rt_array_bytes_basis_ptr(array: *mut c_void) -> i64;
    fn rt_array_len(array: *mut c_void) -> i64;
    fn rt_array_get(array: *mut c_void, index: i64) -> i64;
    fn rt_value_as_int(value: i64) -> i64;
}

/// Must equal PIPED_BYTES_CAP_V1 / PIPED_WRITE_CHUNK_V1 in runtime_process.c.
const PIPED_BYTES_CAP: usize = 65536;
const PIPED_WRITE_CHUNK: usize = 4096;
const STREAM_STDOUT: i64 = 1;
const STREAM_STDERR: i64 = 2;

#[no_mangle]
pub extern "C" fn rt_process_spawn_piped_split_v1(cmd: *const u8, cmd_len: i64, args: *mut c_void) -> i64 {
    if cmd.is_null() || cmd_len <= 0 { return -1; }
    let pid = unsafe { simple_piped_owner_spawn_split_v1(cmd, cmd_len, args) };
    if pid > 0 { pid } else { -1 }
}

fn read_bytes(pid: i64, stream: i64, max_bytes: i64) -> *mut c_void {
    let mut buffer = [0u8; PIPED_BYTES_CAP];
    let cap = if max_bytes <= 0 { 0 } else if max_bytes as u64 > PIPED_BYTES_CAP as u64 {
        PIPED_BYTES_CAP as i64 } else { max_bytes };
    let count = if pid > 0 && cap > 0 {
        unsafe { simple_piped_owner_read_v1(pid, stream, buffer.as_mut_ptr(), cap) }
    } else { -1 };
    // An owner reporting more than it was given is a broken contract: deliver
    // nothing rather than read past the buffer.
    let count = if count > 0 && count <= cap { count } else { 0 };
    unsafe { simple_piped_bytes_new_v1(buffer.as_ptr(), count) }
}

#[no_mangle]
pub extern "C" fn rt_process_read_stdout_bytes_v1(pid: i64, max_bytes: i64) -> *mut c_void {
    read_bytes(pid, STREAM_STDOUT, max_bytes)
}

#[no_mangle]
pub extern "C" fn rt_process_read_stderr_bytes_v1(pid: i64, max_bytes: i64) -> *mut c_void {
    read_bytes(pid, STREAM_STDERR, max_bytes)
}

#[no_mangle]
pub extern "C" fn rt_process_read_stderr(pid: i64) -> *const u8 {
    // The owner returns its own thread-local, NUL-terminated buffer even for an
    // invalid pid, so the empty-text sentinel matches the C lane exactly.
    unsafe { simple_piped_owner_read_stderr_text_v1(pid) }
}

#[no_mangle]
pub extern "C" fn rt_process_stderr_state_v1(pid: i64) -> i64 {
    let state = unsafe { simple_piped_owner_stream_state_v1(pid, STREAM_STDERR) };
    match state { -2 | -1 | 0 | 1 => state, _ => -1 }
}

#[no_mangle]
pub extern "C" fn rt_process_write_stdin_bytes_some_v1(
    pid: i64, data: *mut c_void, offset: i64, max_bytes: i64,
) -> i64 {
    if pid <= 0 || data.is_null() || offset < 0 || max_bytes <= 0 { return -1; }
    let packed_len = unsafe { rt_array_bytes_basis_len(data) };
    if packed_len >= 0 {
        if offset > packed_len { return -1; }
        if offset == packed_len { return 0; }
        let bytes = unsafe { rt_array_bytes_basis_ptr(data) } as usize as *const u8;
        if bytes.is_null() { return -1; }
        return unsafe { simple_piped_owner_write_v1(pid, bytes, packed_len, offset, max_bytes) };
    }
    let total = unsafe { rt_array_len(data) };
    if offset > total { return -1; }
    if offset == total { return 0; }
    let mut chunk = [0u8; PIPED_WRITE_CHUNK];
    let mut want = total - offset;
    if want > max_bytes { want = max_bytes; }
    if want > PIPED_WRITE_CHUNK as i64 { want = PIPED_WRITE_CHUNK as i64; }
    let mut index = 0usize;
    while (index as i64) < want {
        let value = unsafe { rt_value_as_int(rt_array_get(data, offset + index as i64)) };
        if !(0..=255).contains(&value) { return -1; }
        chunk[index] = value as u8;
        index += 1;
    }
    unsafe { simple_piped_owner_write_v1(pid, chunk.as_ptr(), want, 0, want) }
}
