//! Contract checking FFI for Design by Contract support.
//!
//! Provides runtime contract validation for preconditions, postconditions, and invariants.
//! When contract checking is enabled, compiled code calls these functions to verify
//! contracts at runtime.
//!
//! ## Contract Types
//!
//! - **Precondition (Pre)**: Must be true when function is called
//! - **Postcondition (Post)**: Must be true when function returns normally
//! - **Error Postcondition (ErrPost)**: Must be true when function returns with error
//! - **Invariant Entry (InvEntry)**: Must be true when method is called
//! - **Invariant Exit (InvExit)**: Must be true when method returns
//! - **Assertion**: Must be true at the point of the assert/check statement
//!
//! ## Usage Pattern
//!
//! 1. Contracts are declared in Simple source code
//! 2. Compiler generates calls to these functions when contract checking is enabled
//! 3. If condition is false, contract violation is reported and program panics
//! 4. If condition is true, function returns normally
//!
//! ## Panic Behavior
//!
//! Contract violations result in panic, which is appropriate for Design by Contract
//! since contract violations indicate programming errors that should not be recovered from.

use crate::value::contracts::ContractViolationKind;

/// Internal function to check contract and generate panic message.
/// This is a safe Rust function that can be tested with catch_unwind.
///
/// Returns `Ok(())` if condition is true, `Err(message)` if contract violated.
fn check_contract_internal(
    condition: bool,
    kind: ContractViolationKind,
    func_name: &str,
    custom_msg: Option<&str>,
) -> Result<(), String> {
    if condition {
        return Ok(());
    }

    let base_msg = format!(
        "{} violation in function '{}': contract condition failed",
        kind.name(),
        func_name
    );

    if let Some(msg) = custom_msg {
        Err(format!("{} ({})", base_msg, msg))
    } else {
        Err(base_msg)
    }
}

/// Check a contract condition and panic if it fails.
/// This is called from compiled code when contract checking is enabled.
///
/// # Arguments
/// * `condition` - The boolean condition (1 = true, 0 = false)
/// * `kind` - Type of contract (0=Pre, 1=Post, 2=ErrPost, 3=InvEntry, 4=InvExit, 5=Assertion)
/// * `func_name_ptr` - Pointer to function name string (UTF-8), may be null
/// * `func_name_len` - Length of function name
///
/// # Safety
/// func_name_ptr must be a valid pointer to func_name_len bytes of UTF-8 data, or null.
#[no_mangle]
pub unsafe extern "C" fn simple_contract_check(
    condition: i64,
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
) {
    let violation_kind = ContractViolationKind::from_i64(kind).unwrap_or(ContractViolationKind::Pre);

    let func_name = if func_name_ptr.is_null() || func_name_len <= 0 {
        "<unknown>"
    } else {
        let slice = std::slice::from_raw_parts(func_name_ptr, func_name_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    if let Err(msg) = check_contract_internal(condition != 0, violation_kind, func_name, None) {
        panic!("{}", msg);
    }
}

/// Check a contract condition with a custom message and panic if it fails.
/// This is called from compiled code when contract checking is enabled.
///
/// # Arguments
/// * `condition` - The boolean condition (1 = true, 0 = false)
/// * `kind` - Type of contract (0=Pre, 1=Post, 2=ErrPost, 3=InvEntry, 4=InvExit, 5=Assertion)
/// * `func_name_ptr` - Pointer to function name string (UTF-8), may be null
/// * `func_name_len` - Length of function name
/// * `message_ptr` - Pointer to message string (UTF-8), may be null
/// * `message_len` - Length of message
///
/// # Safety
/// Pointers must be valid or null.
#[no_mangle]
pub unsafe extern "C" fn simple_contract_check_msg(
    condition: i64,
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
    message_ptr: *const u8,
    message_len: i64,
) {
    let violation_kind = ContractViolationKind::from_i64(kind).unwrap_or(ContractViolationKind::Pre);

    let func_name = if func_name_ptr.is_null() || func_name_len <= 0 {
        "<unknown>"
    } else {
        let slice = std::slice::from_raw_parts(func_name_ptr, func_name_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    let custom_msg = if message_ptr.is_null() || message_len <= 0 {
        None
    } else {
        let slice = std::slice::from_raw_parts(message_ptr, message_len as usize);
        std::str::from_utf8(slice).ok()
    };

    if let Err(msg) = check_contract_internal(condition != 0, violation_kind, func_name, custom_msg) {
        panic!("{}", msg);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests for FFI functions - only test non-panic paths
    // (extern "C" functions cannot unwind through catch_unwind)

    #[test]
    fn test_contract_check_true_condition() {
        // Should not panic when condition is true
        unsafe {
            simple_contract_check(1, 0, std::ptr::null(), 0);
            simple_contract_check(42, 0, std::ptr::null(), 0); // Any non-zero is true
        }
    }

    #[test]
    fn test_contract_check_msg_true_condition() {
        // Should not panic when condition is true
        unsafe {
            simple_contract_check_msg(1, 0, std::ptr::null(), 0, std::ptr::null(), 0);
        }
    }

    // Tests for internal contract checking logic (testable with catch_unwind)

    #[test]
    fn test_check_contract_internal_true_returns_ok() {
        let result = check_contract_internal(true, ContractViolationKind::Pre, "test_func", None);
        assert!(result.is_ok());
    }

    #[test]
    fn test_check_contract_internal_false_returns_err() {
        let result = check_contract_internal(false, ContractViolationKind::Pre, "test_func", None);
        assert!(result.is_err());
        let msg = result.unwrap_err();
        assert!(
            msg.contains("Precondition violation"),
            "Expected 'Precondition violation' in: {}",
            msg
        );
        assert!(msg.contains("test_func"), "Expected function name in: {}", msg);
    }

    #[test]
    fn test_check_contract_internal_with_custom_message() {
        let result = check_contract_internal(
            false,
            ContractViolationKind::Post,
            "my_function",
            Some("custom error message"),
        );
        assert!(result.is_err());
        let msg = result.unwrap_err();
        assert!(
            msg.contains("Postcondition violation"),
            "Expected 'Postcondition violation' in: {}",
            msg
        );
        assert!(msg.contains("my_function"), "Expected function name in: {}", msg);
        assert!(
            msg.contains("custom error message"),
            "Expected custom message in: {}",
            msg
        );
    }

    #[test]
    fn test_check_contract_internal_all_violation_kinds() {
        // Test all violation kinds - names must match ContractViolationKind::name()
        let kinds = [
            (ContractViolationKind::Pre, "Precondition"),
            (ContractViolationKind::Post, "Postcondition"),
            (ContractViolationKind::ErrPost, "Error postcondition"),
            (ContractViolationKind::InvariantEntry, "Entry invariant"),
            (ContractViolationKind::InvariantExit, "Exit invariant"),
        ];

        for (kind, expected_name) in kinds {
            let result = check_contract_internal(false, kind, "test_func", None);
            assert!(result.is_err(), "Expected Err for {:?}", kind);
            let msg = result.unwrap_err();
            assert!(
                msg.contains(expected_name),
                "Expected '{}' in message for {:?}, got: {}",
                expected_name,
                kind,
                msg
            );
        }
    }

    #[test]
    fn test_check_contract_internal_special_function_names() {
        // Test with empty function name
        let result = check_contract_internal(false, ContractViolationKind::Pre, "", None);
        assert!(result.is_err());

        // Test with function name containing special characters
        let result = check_contract_internal(false, ContractViolationKind::Pre, "my::module::function<T>", None);
        assert!(result.is_err());
        let msg = result.unwrap_err();
        assert!(msg.contains("my::module::function<T>"));
    }
}
