//! Contract violation types (CTR-050-054)
//!
//! This module provides typed contract violations for Design by Contract support.
//! Each violation type corresponds to a specific contract check failure:
//!
//! - CTR-050: `ContractViolation::Pre` - Precondition failure
//! - CTR-051: `ContractViolation::Post` - Postcondition failure
//! - CTR-052: `ContractViolation::ErrPost` - Error postcondition failure
//! - CTR-053: `ContractViolation::InvariantEntry` - Invariant failure at entry
//! - CTR-054: `ContractViolation::InvariantExit` - Invariant failure at exit

use super::core::RuntimeValue;
use super::heap::{HeapHeader, HeapObjectType};
use std::alloc::{alloc, dealloc, Layout};
use std::ptr;

/// Contract violation kind, matching MIR ContractKind
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ContractViolationKind {
    /// Precondition failure (CTR-050)
    Pre = 0,
    /// Postcondition failure (CTR-051)
    Post = 1,
    /// Error postcondition failure (CTR-052)
    ErrPost = 2,
    /// Invariant failure at function entry (CTR-053)
    InvariantEntry = 3,
    /// Invariant failure at function exit (CTR-054)
    InvariantExit = 4,
    /// Inline assertion failure (assert/check statement)
    Assertion = 5,
}

impl ContractViolationKind {
    /// Get the kind from an integer value
    pub fn from_i64(kind: i64) -> Option<Self> {
        match kind {
            0 => Some(Self::Pre),
            1 => Some(Self::Post),
            2 => Some(Self::ErrPost),
            3 => Some(Self::InvariantEntry),
            4 => Some(Self::InvariantExit),
            5 => Some(Self::Assertion),
            _ => None,
        }
    }

    /// Get the display name for this violation kind
    pub fn name(&self) -> &'static str {
        match self {
            Self::Pre => "Precondition",
            Self::Post => "Postcondition",
            Self::ErrPost => "Error postcondition",
            Self::InvariantEntry => "Entry invariant",
            Self::InvariantExit => "Exit invariant",
            Self::Assertion => "Assertion",
        }
    }
}

/// Runtime representation of a contract violation.
/// This is a heap-allocated object that stores violation details.
#[repr(C)]
pub struct RuntimeContractViolation {
    /// Heap header for GC
    pub header: HeapHeader,
    /// Type of violation
    pub kind: ContractViolationKind,
    /// Function name where violation occurred (null-terminated)
    pub func_name_ptr: *const u8,
    /// Length of function name
    pub func_name_len: usize,
    /// Optional message (null-terminated)
    pub message_ptr: *const u8,
    /// Length of message
    pub message_len: usize,
}

impl RuntimeContractViolation {
    /// Allocate a new contract violation on the heap
    pub fn new(kind: ContractViolationKind, func_name: &str, message: Option<&str>) -> *mut Self {
        let layout = Layout::new::<Self>();

        unsafe {
            let ptr = alloc(layout) as *mut Self;
            if ptr.is_null() {
                return ptr::null_mut();
            }

            // Initialize header
            (*ptr).header = HeapHeader::new(HeapObjectType::ContractViolation, std::mem::size_of::<Self>() as u32);
            (*ptr).kind = kind;

            // Copy function name
            let func_name_bytes = func_name.as_bytes();
            let name_layout = Layout::array::<u8>(func_name_bytes.len() + 1).unwrap();
            let name_ptr = alloc(name_layout);
            if !name_ptr.is_null() {
                ptr::copy_nonoverlapping(func_name_bytes.as_ptr(), name_ptr, func_name_bytes.len());
                *name_ptr.add(func_name_bytes.len()) = 0; // null terminator
                (*ptr).func_name_ptr = name_ptr;
                (*ptr).func_name_len = func_name_bytes.len();
            } else {
                (*ptr).func_name_ptr = ptr::null();
                (*ptr).func_name_len = 0;
            }

            // Copy message if present
            if let Some(msg) = message {
                let msg_bytes = msg.as_bytes();
                let msg_layout = Layout::array::<u8>(msg_bytes.len() + 1).unwrap();
                let msg_ptr = alloc(msg_layout);
                if !msg_ptr.is_null() {
                    ptr::copy_nonoverlapping(msg_bytes.as_ptr(), msg_ptr, msg_bytes.len());
                    *msg_ptr.add(msg_bytes.len()) = 0; // null terminator
                    (*ptr).message_ptr = msg_ptr;
                    (*ptr).message_len = msg_bytes.len();
                } else {
                    (*ptr).message_ptr = ptr::null();
                    (*ptr).message_len = 0;
                }
            } else {
                (*ptr).message_ptr = ptr::null();
                (*ptr).message_len = 0;
            }

            ptr
        }
    }

    /// Free a contract violation (deallocate memory)
    pub unsafe fn free(ptr: *mut Self) {
        if ptr.is_null() {
            return;
        }

        // Free function name
        if !(*ptr).func_name_ptr.is_null() && (*ptr).func_name_len > 0 {
            let name_layout = Layout::array::<u8>((*ptr).func_name_len + 1).unwrap();
            dealloc((*ptr).func_name_ptr as *mut u8, name_layout);
        }

        // Free message
        if !(*ptr).message_ptr.is_null() && (*ptr).message_len > 0 {
            let msg_layout = Layout::array::<u8>((*ptr).message_len + 1).unwrap();
            dealloc((*ptr).message_ptr as *mut u8, msg_layout);
        }

        // Free the violation itself
        let layout = Layout::new::<Self>();
        dealloc(ptr as *mut u8, layout);
    }

    /// Get the function name as a string slice
    pub fn func_name(&self) -> &str {
        if self.func_name_ptr.is_null() || self.func_name_len == 0 {
            return "<unknown>";
        }
        unsafe {
            let slice = std::slice::from_raw_parts(self.func_name_ptr, self.func_name_len);
            std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
        }
    }

    /// Get the message as an optional string slice
    pub fn message(&self) -> Option<&str> {
        if self.message_ptr.is_null() || self.message_len == 0 {
            return None;
        }
        unsafe {
            let slice = std::slice::from_raw_parts(self.message_ptr, self.message_len);
            std::str::from_utf8(slice).ok()
        }
    }

    /// Format the violation as an error message
    pub fn format(&self) -> String {
        let base = format!(
            "{} violation in function '{}': contract condition failed",
            self.kind.name(),
            self.func_name()
        );
        if let Some(msg) = self.message() {
            format!("{} ({})", base, msg)
        } else {
            base
        }
    }
}

// ============================================================================
// FFI Functions for Contract Violations
// ============================================================================

/// Create a new contract violation object.
///
/// # Arguments
/// * `kind` - Type of contract (0=Pre, 1=Post, 2=ErrPost, 3=InvEntry, 4=InvExit)
/// * `func_name_ptr` - Pointer to function name string (UTF-8)
/// * `func_name_len` - Length of function name
/// * `message_ptr` - Pointer to message string (UTF-8), may be null
/// * `message_len` - Length of message
///
/// # Returns
/// A RuntimeValue containing a pointer to the violation object
#[no_mangle]
pub unsafe extern "C" fn rt_contract_violation_new(
    kind: i64,
    func_name_ptr: *const u8,
    func_name_len: i64,
    message_ptr: *const u8,
    message_len: i64,
) -> RuntimeValue {
    let violation_kind = match ContractViolationKind::from_i64(kind) {
        Some(k) => k,
        None => ContractViolationKind::Pre, // Default to precondition
    };

    let func_name = if func_name_ptr.is_null() || func_name_len <= 0 {
        "<unknown>"
    } else {
        let slice = std::slice::from_raw_parts(func_name_ptr, func_name_len as usize);
        std::str::from_utf8(slice).unwrap_or("<invalid UTF-8>")
    };

    let message = if message_ptr.is_null() || message_len <= 0 {
        None
    } else {
        let slice = std::slice::from_raw_parts(message_ptr, message_len as usize);
        std::str::from_utf8(slice).ok()
    };

    let ptr = RuntimeContractViolation::new(violation_kind, func_name, message);
    if ptr.is_null() {
        RuntimeValue::NIL
    } else {
        RuntimeValue::from_heap_ptr(ptr as *mut HeapHeader)
    }
}

/// Get the kind of a contract violation.
///
/// # Arguments
/// * `violation` - A RuntimeValue containing a contract violation object
///
/// # Returns
/// The violation kind as an integer (0-4), or -1 if the value is not a violation
#[no_mangle]
pub extern "C" fn rt_contract_violation_kind(violation: RuntimeValue) -> i64 {
    if !violation.is_heap() {
        return -1;
    }

    let ptr = violation.as_heap_ptr() as *const RuntimeContractViolation;
    unsafe {
        if (*ptr).header.object_type != HeapObjectType::ContractViolation {
            return -1;
        }
        (*ptr).kind as i64
    }
}

/// Get the function name from a contract violation.
///
/// # Arguments
/// * `violation` - A RuntimeValue containing a contract violation object
///
/// # Returns
/// A RuntimeValue containing a string with the function name, or NIL if invalid
#[no_mangle]
pub extern "C" fn rt_contract_violation_func_name(violation: RuntimeValue) -> RuntimeValue {
    if !violation.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = violation.as_heap_ptr() as *const RuntimeContractViolation;
    unsafe {
        if (*ptr).header.object_type != HeapObjectType::ContractViolation {
            return RuntimeValue::NIL;
        }

        let func_name = (*ptr).func_name();
        super::collections::rt_string_new(func_name.as_ptr(), func_name.len() as u64)
    }
}

/// Get the message from a contract violation.
///
/// # Arguments
/// * `violation` - A RuntimeValue containing a contract violation object
///
/// # Returns
/// A RuntimeValue containing a string with the message, or NIL if no message
#[no_mangle]
pub extern "C" fn rt_contract_violation_message(violation: RuntimeValue) -> RuntimeValue {
    if !violation.is_heap() {
        return RuntimeValue::NIL;
    }

    let ptr = violation.as_heap_ptr() as *const RuntimeContractViolation;
    unsafe {
        if (*ptr).header.object_type != HeapObjectType::ContractViolation {
            return RuntimeValue::NIL;
        }

        match (*ptr).message() {
            Some(msg) => super::collections::rt_string_new(msg.as_ptr(), msg.len() as u64),
            None => RuntimeValue::NIL,
        }
    }
}

/// Check if a value is a contract violation.
///
/// # Arguments
/// * `value` - The value to check
///
/// # Returns
/// 1 if the value is a contract violation, 0 otherwise
#[no_mangle]
pub extern "C" fn rt_is_contract_violation(value: RuntimeValue) -> i64 {
    if !value.is_heap() {
        return 0;
    }

    let ptr = value.as_heap_ptr() as *const RuntimeContractViolation;
    unsafe {
        if (*ptr).header.object_type == HeapObjectType::ContractViolation {
            1
        } else {
            0
        }
    }
}

/// Free a contract violation object.
///
/// # Safety
/// The value must be a valid contract violation object.
#[no_mangle]
pub unsafe extern "C" fn rt_contract_violation_free(violation: RuntimeValue) {
    if !violation.is_heap() {
        return;
    }

    let ptr = violation.as_heap_ptr() as *mut RuntimeContractViolation;
    if (*ptr).header.object_type != HeapObjectType::ContractViolation {
        return;
    }

    RuntimeContractViolation::free(ptr);
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_violation_kind_from_i64() {
        assert_eq!(ContractViolationKind::from_i64(0), Some(ContractViolationKind::Pre));
        assert_eq!(ContractViolationKind::from_i64(1), Some(ContractViolationKind::Post));
        assert_eq!(ContractViolationKind::from_i64(2), Some(ContractViolationKind::ErrPost));
        assert_eq!(
            ContractViolationKind::from_i64(3),
            Some(ContractViolationKind::InvariantEntry)
        );
        assert_eq!(
            ContractViolationKind::from_i64(4),
            Some(ContractViolationKind::InvariantExit)
        );
        assert_eq!(
            ContractViolationKind::from_i64(5),
            Some(ContractViolationKind::Assertion)
        );
        assert_eq!(ContractViolationKind::from_i64(6), None);
        assert_eq!(ContractViolationKind::from_i64(-1), None);
    }

    #[test]
    fn test_violation_kind_name() {
        assert_eq!(ContractViolationKind::Pre.name(), "Precondition");
        assert_eq!(ContractViolationKind::Post.name(), "Postcondition");
        assert_eq!(ContractViolationKind::ErrPost.name(), "Error postcondition");
        assert_eq!(ContractViolationKind::InvariantEntry.name(), "Entry invariant");
        assert_eq!(ContractViolationKind::InvariantExit.name(), "Exit invariant");
        assert_eq!(ContractViolationKind::Assertion.name(), "Assertion");
    }

    #[test]
    fn test_contract_violation_create() {
        let ptr =
            RuntimeContractViolation::new(ContractViolationKind::Pre, "test_function", Some("x must be positive"));

        assert!(!ptr.is_null());

        unsafe {
            assert_eq!((*ptr).kind, ContractViolationKind::Pre);
            assert_eq!((*ptr).func_name(), "test_function");
            assert_eq!((*ptr).message(), Some("x must be positive"));

            let formatted = (*ptr).format();
            assert!(formatted.contains("Precondition violation"));
            assert!(formatted.contains("test_function"));
            assert!(formatted.contains("x must be positive"));

            RuntimeContractViolation::free(ptr);
        }
    }

    #[test]
    fn test_contract_violation_no_message() {
        let ptr = RuntimeContractViolation::new(ContractViolationKind::Post, "another_function", None);

        assert!(!ptr.is_null());

        unsafe {
            assert_eq!((*ptr).kind, ContractViolationKind::Post);
            assert_eq!((*ptr).func_name(), "another_function");
            assert_eq!((*ptr).message(), None);

            let formatted = (*ptr).format();
            assert!(formatted.contains("Postcondition violation"));
            assert!(formatted.contains("another_function"));
            assert!(!formatted.contains("("));

            RuntimeContractViolation::free(ptr);
        }
    }

    #[test]
    fn test_ffi_contract_violation_new() {
        let func_name = b"ffi_test";
        let message = b"test message";

        unsafe {
            let violation = rt_contract_violation_new(
                0, // Pre
                func_name.as_ptr(),
                func_name.len() as i64,
                message.as_ptr(),
                message.len() as i64,
            );

            assert!(!violation.is_nil());
            assert!(violation.is_heap());

            assert_eq!(rt_contract_violation_kind(violation), 0);
            assert_eq!(rt_is_contract_violation(violation), 1);

            rt_contract_violation_free(violation);
        }
    }

    #[test]
    fn test_ffi_not_a_violation() {
        let int_val = RuntimeValue::from_int(42);
        assert_eq!(rt_is_contract_violation(int_val), 0);
        assert_eq!(rt_contract_violation_kind(int_val), -1);
    }
}
