//! Error handling SFFI implemented directly in Rust.

use crate::value::core::RuntimeValue;

unsafe fn string_from_raw_parts(ptr: *const u8, len: u64, fallback: &str) -> String {
    if ptr.is_null() || len == 0 {
        return fallback.to_string();
    }
    let bytes = std::slice::from_raw_parts(ptr, len as usize);
    String::from_utf8_lossy(bytes).into_owned()
}

/// Exit status used when a compiled program reaches a symbol the backend could
/// not resolve. 70 is `EX_SOFTWARE` (sysexits.h): an internal software fault,
/// which is exactly what a codegen dispatch gap is.
pub const NOT_FOUND_EXIT_CODE: i32 = 70;

/// The diagnostic printed for an unresolved function lookup.
///
/// Split out from the `extern "C"` entry point so the wording stays unit
/// testable now that the entry point terminates the process instead of
/// returning a value.
fn function_not_found_message(name: Option<&str>) -> String {
    match name {
        Some(name) => format!("Runtime error: Function '{name}' not found"),
        None => "Runtime error: Function not found (unknown name)".to_string(),
    }
}

/// The diagnostic printed for an unresolved method lookup.
fn method_not_found_message(type_name: &str, method_name: &str) -> String {
    format!("Runtime error: Method '{method_name}' not found on type '{type_name}'")
}

/// Both lookups used to print a warning and then return
/// `RuntimeValue::from_special(tags::SPECIAL_ERROR)`. That sentinel formats as
/// the six-character text `error` (see `sffi/io_print.rs`, arm
/// `tags::SPECIAL_ERROR`) and reports a length of `-1`, so a program that hit a
/// missing method kept running and wrote the literal word `error` wherever the
/// real value belonged -- while still exiting 0.
///
/// That turned every backend dispatch gap into a silent data-corruption bug.
/// The concrete case that forced this change: `" ".repeat(n)` had no runtime
/// definition, so `simple fix` would have written `error` in place of
/// indentation into users' source files, with a zero exit status.
///
/// A missing symbol is a compiler defect, never a recoverable program
/// condition, so it now terminates instead of fabricating a value.
fn abort_not_found(message: String) -> ! {
    eprintln!("{message}");
    eprintln!(
        "Runtime error: unresolved symbol -- this is a code-generation dispatch gap, not a \
         program error. Refusing to substitute a placeholder value (it would render as the \
         text 'error' and silently corrupt output)."
    );
    use std::io::Write;
    let _ = std::io::stderr().flush();
    let _ = std::io::stdout().flush();
    std::process::exit(NOT_FOUND_EXIT_CODE)
}

#[no_mangle]
pub unsafe extern "C" fn rt_function_not_found(name_ptr: *const u8, name_len: u64) -> RuntimeValue {
    let owned;
    let name = if name_ptr.is_null() {
        None
    } else {
        owned = string_from_raw_parts(name_ptr, name_len, "");
        Some(owned.as_str())
    };
    abort_not_found(function_not_found_message(name))
}
#[no_mangle]
pub unsafe extern "C" fn rt_method_not_found(
    type_ptr: *const u8,
    type_len: u64,
    method_ptr: *const u8,
    method_len: u64,
) -> RuntimeValue {
    let type_name = string_from_raw_parts(type_ptr, type_len, "<unknown type>");
    let method_name = string_from_raw_parts(method_ptr, method_len, "<unknown method>");
    abort_not_found(method_not_found_message(&type_name, &method_name))
}

#[cfg(test)]
mod tests {
    use super::*;

    // The previous tests here asserted that both entry points RETURN
    // `RuntimeValue::from_special(tags::SPECIAL_ERROR)`. That is precisely the
    // silent-substitution behavior that corrupted output, so those assertions
    // are gone rather than relaxed: the entry points no longer return at all.
    // What remains testable -- and what a user actually sees -- is the wording
    // of the diagnostic.

    #[test]
    fn function_not_found_message_names_the_symbol() {
        assert_eq!(
            function_not_found_message(Some("str.repeat")),
            "Runtime error: Function 'str.repeat' not found"
        );
    }

    #[test]
    fn function_not_found_message_handles_missing_name() {
        assert_eq!(
            function_not_found_message(None),
            "Runtime error: Function not found (unknown name)"
        );
    }

    #[test]
    fn method_not_found_message_names_type_and_method() {
        assert_eq!(
            method_not_found_message("MyStruct", "my_method"),
            "Runtime error: Method 'my_method' not found on type 'MyStruct'"
        );
    }

    #[test]
    fn raw_parts_decoding_is_lossy_not_panicking() {
        let invalid_utf8 = [0xFFu8, 0xFE, 0xFD];
        let decoded = unsafe { string_from_raw_parts(invalid_utf8.as_ptr(), invalid_utf8.len() as u64, "") };
        assert!(!decoded.is_empty());
        assert!(decoded.contains('\u{FFFD}'));
    }

    #[test]
    fn raw_parts_null_and_empty_use_the_fallback() {
        assert_eq!(
            unsafe { string_from_raw_parts(std::ptr::null(), 0, "<unknown type>") },
            "<unknown type>"
        );
        assert_eq!(
            unsafe { string_from_raw_parts(b"ignored".as_ptr(), 0, "<unknown method>") },
            "<unknown method>"
        );
    }

    #[test]
    fn not_found_exit_code_is_ex_software() {
        assert_eq!(NOT_FOUND_EXIT_CODE, 70);
    }
}
