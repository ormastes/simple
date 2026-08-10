//! Contract checking implemented directly in Rust.

/// Native codegen passes `text` extern arguments as a raw `(ptr, len)`
/// byte-span pair, not a NUL-terminated C string (same convention as
/// `rt_file_exists`/`rt_env_get`/`rt_mem_attr_set_owner`; see
/// doc/08_tracking/bug/extern_text_cchar_abi_family_sweep_2026-07-29.md).
/// This was previously declared `*const c_char` and decoded with
/// `CStr::from_ptr`, which silently dropped the panic message (an empty or
/// garbage string) under the JIT/native engine while still aborting.
#[no_mangle]
pub unsafe extern "C" fn rt_panic(message_ptr: *const u8, message_len: u64) {
    let message = string_arg_or_unknown(message_ptr, message_len as i64);
    let message = if message == "<unknown>" {
        "panic".to_string()
    } else {
        message
    };
    eprintln!("{message}");
    super::env_process::terminal_emergency_restore_for_panic();
    std::process::abort();
}

fn contract_kind_name(kind: i64) -> &'static str {
    match kind {
        0 => "Precondition",
        1 => "Postcondition",
        2 => "Error postcondition",
        3 => "Entry invariant",
        4 => "Exit invariant",
        5 => "Assertion",
        _ => "Precondition",
    }
}

#[no_mangle]
pub unsafe extern "C" fn simple_contract_check(
    condition: i64,
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
) {
    if condition != 0 {
        return;
    }

    let kind_name = contract_kind_name(kind);
    let func_name = string_arg_or_unknown(func_name_ptr, func_name_len);
    eprintln!("{kind_name} violation in function '{func_name}': contract condition failed");
    super::env_process::terminal_emergency_restore_for_panic();
    std::process::abort();
}

#[no_mangle]
pub unsafe extern "C" fn simple_contract_check_msg(
    condition: i64,
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
    message_ptr: *const u8,
    message_len: i64,
) {
    if condition != 0 {
        return;
    }

    let kind_name = contract_kind_name(kind);
    let func_name = string_arg_or_unknown(func_name_ptr, func_name_len);
    if let Some(message) = string_arg(message_ptr, message_len) {
        eprintln!("{kind_name} violation in function '{func_name}': contract condition failed ({message})");
    } else {
        eprintln!("{kind_name} violation in function '{func_name}': contract condition failed");
    }
    super::env_process::terminal_emergency_restore_for_panic();
    std::process::abort();
}

unsafe fn string_arg_or_unknown(ptr: *const u8, len: i64) -> String {
    string_arg(ptr, len).unwrap_or_else(|| "<unknown>".to_string())
}

unsafe fn string_arg(ptr: *const u8, len: i64) -> Option<String> {
    if ptr.is_null() || len <= 0 {
        return None;
    }
    let bytes = std::slice::from_raw_parts(ptr, len as usize);
    Some(String::from_utf8_lossy(bytes).into_owned())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(target_os = "linux")]
    unsafe fn assert_contract_abort_restores_terminal(with_message: bool) {
        let mut master = -1;
        let mut slave = -1;
        assert_eq!(
            libc::openpty(
                &mut master,
                &mut slave,
                std::ptr::null_mut(),
                std::ptr::null(),
                std::ptr::null(),
            ),
            0
        );
        let mut before = std::mem::MaybeUninit::<libc::termios>::zeroed();
        assert_eq!(libc::tcgetattr(slave, before.as_mut_ptr()), 0);
        let before = before.assume_init();
        let child = libc::fork();
        assert!(child >= 0);
        if child == 0 {
            libc::close(master);
            if libc::dup2(slave, libc::STDIN_FILENO) != libc::STDIN_FILENO {
                libc::_exit(90);
            }
            libc::close(slave);
            if super::super::env_process::rt_terminal_signal_scope_begin() <= 0 {
                libc::_exit(91);
            }
            if !super::super::env_process::rt_terminal_enable_raw_mode().as_bool() {
                libc::_exit(92);
            }
            let function = b"terminal_contract_fixture";
            if with_message {
                let message = b"intentional assertion";
                simple_contract_check_msg(
                    0,
                    5,
                    function.as_ptr(),
                    function.len() as i64,
                    message.as_ptr(),
                    message.len() as i64,
                );
            } else {
                simple_contract_check(0, 5, function.as_ptr(), function.len() as i64);
            }
            libc::_exit(93);
        }
        let mut status = 0;
        assert_eq!(libc::waitpid(child, &mut status, 0), child);
        assert!(libc::WIFSIGNALED(status) || libc::WEXITSTATUS(status) != 0);
        let mut after = std::mem::MaybeUninit::<libc::termios>::zeroed();
        assert_eq!(libc::tcgetattr(slave, after.as_mut_ptr()), 0);
        let after = after.assume_init();
        assert_eq!(
            before.c_lflag & (libc::ICANON | libc::ECHO),
            after.c_lflag & (libc::ICANON | libc::ECHO)
        );
        libc::close(master);
        libc::close(slave);
    }

    #[test]
    fn contract_kind_names_match_legacy_runtime() {
        assert_eq!(contract_kind_name(0), "Precondition");
        assert_eq!(contract_kind_name(1), "Postcondition");
        assert_eq!(contract_kind_name(2), "Error postcondition");
        assert_eq!(contract_kind_name(3), "Entry invariant");
        assert_eq!(contract_kind_name(4), "Exit invariant");
        assert_eq!(contract_kind_name(5), "Assertion");
        assert_eq!(contract_kind_name(99), "Precondition");
    }

    #[test]
    fn passing_contract_checks_return() {
        let name = b"fn_name";
        let message = b"ok";
        unsafe {
            simple_contract_check(1, 0, name.as_ptr(), name.len() as i64);
            simple_contract_check_msg(
                1,
                1,
                name.as_ptr(),
                name.len() as i64,
                message.as_ptr(),
                message.len() as i64,
            );
        }
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn failing_contract_entrypoints_restore_terminal_before_abort() {
        unsafe {
            assert_contract_abort_restores_terminal(false);
            assert_contract_abort_restores_terminal(true);
        }
    }

    #[test]
    fn string_args_handle_null_and_empty() {
        unsafe {
            assert_eq!(string_arg_or_unknown(std::ptr::null(), 3), "<unknown>");
            assert_eq!(string_arg_or_unknown(b"abc".as_ptr(), 0), "<unknown>");
            assert_eq!(string_arg_or_unknown(b"abc".as_ptr(), 3), "abc");
        }
    }
}
