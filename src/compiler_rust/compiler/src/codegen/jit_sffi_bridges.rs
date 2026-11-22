//! Compiler-owned C-ABI bridges for runtime SFFI externs used by Cranelift JIT.
//!
//! Some extern families declared in `src/lib/` live either in the compiler's own
//! interpreter runtime (`interpreter_extern::network`, `interpreter_extern::system`)
//! or in C archives (`libruntime_sffi_c.a`) whose raw `const char*` / nullable
//! `SplArray*` C ABI must be adapted at the `RuntimeValue` boundary. Exposing real
//! C-ABI entrypoints here and registering them in `COMPILER_OWNED_RUNTIME_SYMBOLS`
//! lets Cranelift JIT compile callers natively without hybrid-interp splicing.

use simple_runtime::value::{rt_array_new, rt_array_push, rt_string_data, rt_string_len, rt_string_new};
use simple_runtime::RuntimeValue;

use crate::interpreter::interpreter_extern::{network, system};
use crate::runtime_bridge::{runtime_to_value, value_to_runtime};
use crate::value::Value;

#[inline]
fn rv_to_value(raw: i64) -> Value {
    runtime_to_value(RuntimeValue::from_raw(raw as u64))
}

#[inline]
fn value_to_rv(value: &Value) -> i64 {
    value_to_runtime(value).to_raw() as i64
}

#[inline]
fn empty_text_rv() -> i64 {
    unsafe { rt_string_new(std::ptr::null(), 0) }.to_raw() as i64
}

#[inline]
fn ptr_or_nil_to_rv(ptr: *mut std::ffi::c_void) -> i64 {
    if ptr.is_null() {
        RuntimeValue::NIL.to_raw() as i64
    } else {
        ptr as usize as i64
    }
}

unsafe fn cstr_arg(rv_raw: i64, expected_len: i64) -> (Option<Vec<u8>>, i64) {
    let rv = RuntimeValue::from_raw(rv_raw as u64);
    let actual_len = rt_string_len(rv);
    let data_ptr = rt_string_data(rv);
    if actual_len > 0 && actual_len == expected_len && !data_ptr.is_null() {
        let mut buf = Vec::with_capacity(actual_len as usize + 1);
        buf.extend_from_slice(std::slice::from_raw_parts(data_ptr, actual_len as usize));
        buf.push(0);
        (Some(buf), expected_len)
    } else if actual_len == 0 && expected_len == 0 {
        (Some(vec![0]), 0)
    } else {
        (None, -1)
    }
}

#[inline]
fn cstr_ptr(buf: &Option<Vec<u8>>) -> *const u8 {
    buf.as_deref().map_or(std::ptr::null(), <[u8]>::as_ptr)
}

fn process_input_error_receipt(count: usize, attempt_slot_val: Option<i64>) -> i64 {
    let arr = rt_array_new(count as u64);
    if arr.is_nil() {
        return RuntimeValue::NIL.to_raw() as i64;
    }
    for i in 0..count {
        let word = if i == 0 {
            -4
        } else if i == 2 {
            attempt_slot_val.unwrap_or(0)
        } else {
            0
        };
        if !rt_array_push(arr, RuntimeValue::from_int(word)) {
            return RuntimeValue::NIL.to_raw() as i64;
        }
    }
    arr.to_raw() as i64
}

// =========================================================================
// HTTP request bridges (interpreter_extern::network -> ureq)
// =========================================================================

pub(crate) extern "C" fn jit_rt_http_request(method: i64, url: i64, headers: i64, body: i64) -> i64 {
    let args = [rv_to_value(method), rv_to_value(url), rv_to_value(headers), rv_to_value(body)];
    match network::rt_http_request(&args) {
        Ok(val) => value_to_rv(&val),
        Err(err) => value_to_rv(&Value::Tuple(vec![
            Value::Int(-1),
            Value::text(String::new()),
            Value::text(err.to_string()),
        ])),
    }
}

pub(crate) extern "C" fn jit_rt_http_request_v2(
    method: i64,
    url: i64,
    headers: i64,
    body: i64,
    timeout_ms: i64,
) -> i64 {
    let args = [
        rv_to_value(method),
        rv_to_value(url),
        rv_to_value(headers),
        rv_to_value(body),
        Value::Int(timeout_ms),
    ];
    match network::rt_http_request_v2(&args) {
        Ok(val) => value_to_rv(&val),
        Err(err) => value_to_rv(&Value::Tuple(vec![
            Value::Int(-1),
            Value::text(String::new()),
            Value::text(String::new()),
            Value::byte_array(Vec::new()),
            Value::text(err.to_string()),
        ])),
    }
}

// =========================================================================
// Piped process registry bridges (interpreter_extern::system)
// =========================================================================

pub(crate) extern "C" fn jit_rt_process_spawn_piped(cmd: i64, args: i64) -> i64 {
    match system::rt_process_spawn_piped(&[rv_to_value(cmd), rv_to_value(args)]) {
        Ok(Value::Int(pid)) => pid,
        _ => -1,
    }
}

pub(crate) extern "C" fn jit_rt_process_read_stdout(pid: i64) -> i64 {
    match system::rt_process_read_stdout(&[Value::Int(pid)]) {
        Ok(val) => value_to_rv(&val),
        Err(_) => empty_text_rv(),
    }
}

pub(crate) extern "C" fn jit_rt_process_write_stdin_some(
    pid: i64,
    data: i64,
    data_len: i64,
    offset: i64,
    max_bytes: i64,
) -> i64 {
    let args = [
        Value::Int(pid),
        rv_to_value(data),
        Value::Int(data_len),
        Value::Int(offset),
        Value::Int(max_bytes),
    ];
    match system::rt_process_write_stdin_some(&args) {
        Ok(Value::Int(n)) => n,
        _ => -1,
    }
}

pub(crate) extern "C" fn jit_rt_process_is_alive(pid: i64) -> bool {
    matches!(system::rt_process_is_alive(&[Value::Int(pid)]), Ok(Value::Bool(true)))
}

pub(crate) extern "C" fn jit_rt_process_close_piped(pid: i64) -> bool {
    matches!(system::rt_process_close_piped(&[Value::Int(pid)]), Ok(Value::Bool(true)))
}

pub(crate) extern "C" fn jit_rt_process_stdout_state(pid: i64) -> i64 {
    match system::rt_process_stdout_state(&[Value::Int(pid)]) {
        Ok(Value::Int(state)) => state,
        _ => -1,
    }
}

pub(crate) extern "C" fn jit_rt_process_piped_exit_status_value(pid: i64) -> i64 {
    match system::rt_process_piped_exit_status_value(&[Value::Int(pid)]) {
        Ok(val) => value_to_rv(&val),
        Err(_) => value_to_rv(&Value::array(vec![
            Value::Int(1),
            Value::Int(-1),
            Value::Int(0),
            Value::Int(6),
        ])),
    }
}

pub(crate) extern "C" fn jit_rt_process_spawn_piped_generation_v1(cmd: i64, cmd_len: i64, args: i64) -> i64 {
    match system::rt_process_spawn_piped_generation_v1(&[rv_to_value(cmd), Value::Int(cmd_len), rv_to_value(args)]) {
        Ok(Value::Int(gen)) => gen,
        _ => -1,
    }
}

pub(crate) extern "C" fn jit_rt_process_piped_pid_for_generation_v1(generation: i64) -> i64 {
    match system::rt_process_piped_pid_for_generation_v1(&[Value::Int(generation)]) {
        Ok(Value::Int(pid)) => pid,
        _ => -2,
    }
}

pub(crate) extern "C" fn jit_rt_process_read_stdout_ref_v1(pid: i64, generation: i64) -> i64 {
    match system::rt_process_read_stdout_ref_v1(&[Value::Int(pid), Value::Int(generation)]) {
        Ok(val) => value_to_rv(&val),
        Err(_) => empty_text_rv(),
    }
}

pub(crate) extern "C" fn jit_rt_process_stdout_state_ref_v1(pid: i64, generation: i64) -> i64 {
    match system::rt_process_stdout_state_ref_v1(&[Value::Int(pid), Value::Int(generation)]) {
        Ok(Value::Int(state)) => state,
        _ => -1,
    }
}

pub(crate) extern "C" fn jit_rt_process_validate_piped_ref_v1(pid: i64, generation: i64) -> i64 {
    match system::rt_process_validate_piped_ref_v1(&[Value::Int(pid), Value::Int(generation)]) {
        Ok(Value::Int(res)) => res,
        _ => -2,
    }
}

pub(crate) extern "C" fn jit_rt_process_write_stdin_some_ref_v1(
    pid: i64,
    generation: i64,
    data: i64,
    data_len: i64,
    offset: i64,
    max_bytes: i64,
) -> i64 {
    let args = [
        Value::Int(pid),
        Value::Int(generation),
        rv_to_value(data),
        Value::Int(data_len),
        Value::Int(offset),
        Value::Int(max_bytes),
    ];
    match system::rt_process_write_stdin_some_ref_v1(&args) {
        Ok(Value::Int(n)) => n,
        _ => -1,
    }
}

pub(crate) extern "C" fn jit_rt_process_is_piped_alive_ref_v1(pid: i64, generation: i64) -> i64 {
    match system::rt_process_is_piped_alive_ref_v1(&[Value::Int(pid), Value::Int(generation)]) {
        Ok(Value::Int(res)) => res,
        _ => -2,
    }
}

pub(crate) extern "C" fn jit_rt_process_close_piped_ref_v1(pid: i64, generation: i64) -> i64 {
    match system::rt_process_close_piped_ref_v1(&[Value::Int(pid), Value::Int(generation)]) {
        Ok(Value::Int(res)) => res,
        _ => -2,
    }
}

// =========================================================================
// Local Unix socket v1 C-ABI adapters (`runtime_socket_nonblock.c`)
// =========================================================================

unsafe extern "C" {
    fn rt_local_unix_connect_v1(p: *const u8, n: i64, u: i64, d: i64) -> *mut std::ffi::c_void;
    fn rt_local_unix_read_v1(t: i64, m: i64, d: i64) -> *mut std::ffi::c_void;
    fn rt_local_unix_write_some_v1(t: i64, b: *const std::ffi::c_void, o: i64, m: i64, d: i64)
        -> *mut std::ffi::c_void;
    fn rt_local_unix_write_some_admitted_v1(
        t: i64,
        b: *const std::ffi::c_void,
        o: i64,
        m: i64,
        d: i64,
        e: i64,
    ) -> *mut std::ffi::c_void;
    fn rt_local_unix_close_v1(t: i64) -> *mut std::ffi::c_void;
}

pub(crate) extern "C" fn jit_rt_local_unix_connect_v1(
    path: i64,
    path_bytes: i64,
    expected_uid: i64,
    deadline: i64,
) -> i64 {
    unsafe {
        let (path_buf, n) = cstr_arg(path, path_bytes);
        ptr_or_nil_to_rv(rt_local_unix_connect_v1(cstr_ptr(&path_buf), n, expected_uid, deadline))
    }
}

pub(crate) extern "C" fn jit_rt_local_unix_read_v1(token: i64, maximum: i64, deadline: i64) -> i64 {
    ptr_or_nil_to_rv(unsafe { rt_local_unix_read_v1(token, maximum, deadline) })
}

pub(crate) extern "C" fn jit_rt_local_unix_write_some_v1(
    token: i64,
    bytes: i64,
    offset: i64,
    maximum: i64,
    deadline: i64,
) -> i64 {
    ptr_or_nil_to_rv(unsafe {
        rt_local_unix_write_some_v1(token, bytes as usize as *const std::ffi::c_void, offset, maximum, deadline)
    })
}

pub(crate) extern "C" fn jit_rt_local_unix_write_some_admitted_v1(
    token: i64,
    bytes: i64,
    offset: i64,
    maximum: i64,
    deadline: i64,
    expires: i64,
) -> i64 {
    ptr_or_nil_to_rv(unsafe {
        rt_local_unix_write_some_admitted_v1(
            token,
            bytes as usize as *const std::ffi::c_void,
            offset,
            maximum,
            deadline,
            expires,
        )
    })
}

pub(crate) extern "C" fn jit_rt_local_unix_close_v1(token: i64) -> i64 {
    ptr_or_nil_to_rv(unsafe { rt_local_unix_close_v1(token) })
}

// =========================================================================
// Fail-closed C-only credential/stream/input providers (non-brokered JIT)
// =========================================================================

pub(crate) extern "C" fn jit_rt_retained_private_credential_open_v1(_path: i64, _length: i64) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_retained_private_credential_state_v1(_token: i64) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_retained_private_credential_error_v1(_token: i64) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_retained_private_credential_read_v1(
    _token: i64,
    _buffer: i64,
    _capacity: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_retained_private_credential_publish_v1(
    _token: i64,
    _initial: i64,
    _initial_length: i64,
    _ready: i64,
    _ready_length: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_retained_private_credential_close_v1(_token: i64) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_stream_reserve_v2() -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_stream_bind_v2(
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_stream_abandon_unlaunched_v2(
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_stream_pid_v2(
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_stream_retire_v2(
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
    _proof: i64,
    _proof_len: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_read_stdout_owned_v2(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
) -> i64 {
    empty_text_rv()
}

pub(crate) extern "C" fn jit_rt_process_stdout_state_owned_v2(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_validate_piped_owned_v2(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_write_stdin_some_owned_v2(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_len: i64,
    _identity: i64,
    _identity_len: i64,
    _data: i64,
    _data_len: i64,
    _offset: i64,
    _max_bytes: i64,
) -> i64 {
    -1
}

pub(crate) extern "C" fn jit_rt_process_input_enable_v1(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_bytes: i64,
    _identity: i64,
    _identity_bytes: i64,
) -> i64 {
    process_input_error_receipt(2, None)
}

pub(crate) extern "C" fn jit_rt_process_input_install_v1(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_bytes: i64,
    _identity: i64,
    _identity_bytes: i64,
    _target: i64,
    _target_bytes: i64,
    _nonce: i64,
    _nonce_bytes: i64,
    _revision: i64,
    _expires: i64,
) -> i64 {
    process_input_error_receipt(2, None)
}

pub(crate) extern "C" fn jit_rt_process_input_revoke_v1(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_bytes: i64,
    _identity: i64,
    _identity_bytes: i64,
    _target: i64,
    _target_bytes: i64,
    _nonce: i64,
    _nonce_bytes: i64,
    _revision: i64,
) -> i64 {
    process_input_error_receipt(2, None)
}

pub(crate) extern "C" fn jit_rt_process_input_state_v1(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_bytes: i64,
    _identity: i64,
    _identity_bytes: i64,
) -> i64 {
    process_input_error_receipt(268, None)
}

pub(crate) extern "C" fn jit_rt_process_input_write_some_v1(
    _pid: i64,
    _generation: i64,
    _root: i64,
    _root_bytes: i64,
    _identity: i64,
    _identity_bytes: i64,
    _target: i64,
    _target_bytes: i64,
    _nonce: i64,
    _nonce_bytes: i64,
    _revision: i64,
    attempt: i64,
    _data: i64,
    _data_bytes: i64,
    _offset: i64,
    _maximum: i64,
) -> i64 {
    const INPUT_IMMEDIATE_MAX_V1: i64 = 1_152_921_504_606_846_975;
    let attempt_val = if attempt > 0 && attempt <= INPUT_IMMEDIATE_MAX_V1 {
        attempt
    } else {
        0
    };
    process_input_error_receipt(4, Some(attempt_val))
}

// =========================================================================
// Linux cgroup v2/v3 stream & broker C-ABI adapters (`runtime_process_owned.c`)
// =========================================================================

unsafe extern "C" {
    fn rt_linux_group_stream_admit_v2(path: *const u8, path_len: i64) -> i64;
    fn rt_linux_group_launch_stream_broker_v2(
        program: *const u8,
        program_len: i64,
        digest: *const u8,
        digest_len: i64,
        args: *const std::ffi::c_void,
        generation: i64,
        root: *const u8,
        root_len: i64,
        identity: *const u8,
        identity_len: i64,
        delegated: *const u8,
        delegated_len: i64,
        deadline: i64,
    ) -> *mut std::ffi::c_void;
    fn rt_linux_group_stream_admit_profiled_v3(
        delegated: *const u8,
        delegated_len: i64,
        broker_path: *const u8,
        broker_path_len: i64,
        policy: *const u8,
        policy_len: i64,
        words: *const std::ffi::c_void,
    ) -> i64;
    fn rt_linux_group_launch_stream_broker_profiled_v3(
        program: *const u8,
        program_len: i64,
        digest: *const u8,
        digest_len: i64,
        args: *const std::ffi::c_void,
        generation: i64,
        root: *const u8,
        root_len: i64,
        identity: *const u8,
        identity_len: i64,
        delegated: *const u8,
        delegated_len: i64,
        deadline: i64,
        broker_path: *const u8,
        broker_path_len: i64,
        policy: *const u8,
        policy_len: i64,
        words: *const std::ffi::c_void,
    ) -> *mut std::ffi::c_void;
}

pub(crate) extern "C" fn jit_rt_linux_group_stream_admit_v2(path: i64, path_len: i64) -> i64 {
    unsafe {
        let (path_buf, n) = cstr_arg(path, path_len);
        rt_linux_group_stream_admit_v2(cstr_ptr(&path_buf), n)
    }
}

pub(crate) extern "C" fn jit_rt_linux_group_launch_stream_broker_v2(
    program: i64,
    program_len: i64,
    digest: i64,
    digest_len: i64,
    args: i64,
    generation: i64,
    root: i64,
    root_len: i64,
    identity: i64,
    identity_len: i64,
    delegated: i64,
    delegated_len: i64,
    deadline: i64,
) -> i64 {
    unsafe {
        let (prog_buf, pn) = cstr_arg(program, program_len);
        let (dig_buf, dn) = cstr_arg(digest, digest_len);
        let (root_buf, rn) = cstr_arg(root, root_len);
        let (id_buf, idn) = cstr_arg(identity, identity_len);
        let (del_buf, deln) = cstr_arg(delegated, delegated_len);
        ptr_or_nil_to_rv(rt_linux_group_launch_stream_broker_v2(
            cstr_ptr(&prog_buf),
            pn,
            cstr_ptr(&dig_buf),
            dn,
            args as usize as *const std::ffi::c_void,
            generation,
            cstr_ptr(&root_buf),
            rn,
            cstr_ptr(&id_buf),
            idn,
            cstr_ptr(&del_buf),
            deln,
            deadline,
        ))
    }
}

pub(crate) extern "C" fn jit_rt_linux_group_stream_admit_profiled_v3(
    delegated: i64,
    delegated_len: i64,
    broker_path: i64,
    broker_path_len: i64,
    policy: i64,
    policy_len: i64,
    words: i64,
) -> i64 {
    unsafe {
        let (del_buf, deln) = cstr_arg(delegated, delegated_len);
        let (brk_buf, brkn) = cstr_arg(broker_path, broker_path_len);
        let (pol_buf, poln) = cstr_arg(policy, policy_len);
        rt_linux_group_stream_admit_profiled_v3(
            cstr_ptr(&del_buf),
            deln,
            cstr_ptr(&brk_buf),
            brkn,
            cstr_ptr(&pol_buf),
            poln,
            words as usize as *const std::ffi::c_void,
        )
    }
}

pub(crate) extern "C" fn jit_rt_linux_group_launch_stream_broker_profiled_v3(
    program: i64,
    program_len: i64,
    digest: i64,
    digest_len: i64,
    args: i64,
    generation: i64,
    root: i64,
    root_len: i64,
    identity: i64,
    identity_len: i64,
    delegated: i64,
    delegated_len: i64,
    deadline: i64,
    broker_path: i64,
    broker_path_len: i64,
    policy: i64,
    policy_len: i64,
    words: i64,
) -> i64 {
    unsafe {
        let (prog_buf, pn) = cstr_arg(program, program_len);
        let (dig_buf, dn) = cstr_arg(digest, digest_len);
        let (root_buf, rn) = cstr_arg(root, root_len);
        let (id_buf, idn) = cstr_arg(identity, identity_len);
        let (del_buf, deln) = cstr_arg(delegated, delegated_len);
        let (brk_buf, brkn) = cstr_arg(broker_path, broker_path_len);
        let (pol_buf, poln) = cstr_arg(policy, policy_len);
        ptr_or_nil_to_rv(rt_linux_group_launch_stream_broker_profiled_v3(
            cstr_ptr(&prog_buf),
            pn,
            cstr_ptr(&dig_buf),
            dn,
            args as usize as *const std::ffi::c_void,
            generation,
            cstr_ptr(&root_buf),
            rn,
            cstr_ptr(&id_buf),
            idn,
            cstr_ptr(&del_buf),
            deln,
            deadline,
            cstr_ptr(&brk_buf),
            brkn,
            cstr_ptr(&pol_buf),
            poln,
            words as usize as *const std::ffi::c_void,
        ))
    }
}
