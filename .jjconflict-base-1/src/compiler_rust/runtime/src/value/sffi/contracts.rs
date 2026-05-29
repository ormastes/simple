//! Contract checking implemented directly in Rust.

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

#[inline(always)]
pub unsafe fn simple_contract_check(condition: i64, kind: i64, func_name_ptr: *const u8, func_name_len: i64) {
    if condition != 0 {
        return;
    }

    let kind_name = contract_kind_name(kind);
    let func_name = string_arg_or_unknown(func_name_ptr, func_name_len);
    eprintln!("{kind_name} violation in function '{func_name}': contract condition failed");
    std::process::abort();
}

#[inline(always)]
pub unsafe fn simple_contract_check_msg(
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

    #[test]
    fn string_args_handle_null_and_empty() {
        unsafe {
            assert_eq!(string_arg_or_unknown(std::ptr::null(), 3), "<unknown>");
            assert_eq!(string_arg_or_unknown(b"abc".as_ptr(), 0), "<unknown>");
            assert_eq!(string_arg_or_unknown(b"abc".as_ptr(), 3), "abc");
        }
    }
}
