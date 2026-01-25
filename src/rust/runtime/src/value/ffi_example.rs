//! Example FFI wrapper demonstrating the object-based FFI system.
//!
//! This module shows how to wrap a Rust type using the FFI system.
//!
//! # Example Usage in Simple
//!
//! ```simple
//! # Create a counter
//! val counter = Counter.new(0)
//!
//! # Increment
//! counter.increment()
//! counter.increment()
//!
//! # Get value
//! val value = counter.get()
//! print "Counter value: {value}"  # Output: Counter value: 2
//!
//! # Reset
//! counter.reset()
//! print "After reset: {counter.get()}"  # Output: After reset: 0
//! ```

use super::core::RuntimeValue;
use super::ffi_macros::{get_arg_as, IntoRuntimeValue};
use super::ffi_object::{fnv1a_hash, method_flags, FfiMethodEntry, FfiVtable};
use super::ffi_registry::get_registry;

use std::sync::OnceLock;

// ============================================================================
// The Rust Type to Wrap
// ============================================================================

/// A simple counter for demonstration purposes.
#[derive(Debug, Clone)]
pub struct Counter {
    value: i64,
}

impl Counter {
    /// Create a new counter with the given initial value.
    pub fn new(initial: i64) -> Self {
        Self { value: initial }
    }

    /// Increment the counter by 1.
    pub fn increment(&mut self) {
        self.value += 1;
    }

    /// Increment the counter by a specific amount.
    pub fn increment_by(&mut self, amount: i64) {
        self.value += amount;
    }

    /// Get the current value.
    pub fn get(&self) -> i64 {
        self.value
    }

    /// Reset the counter to 0.
    pub fn reset(&mut self) {
        self.value = 0;
    }

    /// Set the counter to a specific value.
    pub fn set(&mut self, value: i64) {
        self.value = value;
    }
}

// ============================================================================
// FFI Wrapper Implementation using OnceLock (safe pattern)
// ============================================================================

/// Counter FFI state, initialized once.
struct CounterFfi {
    methods: Box<[FfiMethodEntry]>,
    vtable: FfiVtable,
}

// Safety: FfiMethodEntry and FfiVtable contain only static pointers
unsafe impl Send for CounterFfi {}
unsafe impl Sync for CounterFfi {}

// Type name
static COUNTER_TYPE_NAME: &[u8] = b"Counter";

// Static method names (for pointers in method entries)
static METHOD_GET: &[u8] = b"get";
static METHOD_INCREMENT: &[u8] = b"increment";
static METHOD_INCREMENT_BY: &[u8] = b"increment_by";
static METHOD_RESET: &[u8] = b"reset";
static METHOD_SET: &[u8] = b"set";

// OnceLock for safe initialization
static COUNTER_FFI: OnceLock<CounterFfi> = OnceLock::new();

/// Get or initialize the Counter FFI state.
fn get_counter_ffi() -> &'static CounterFfi {
    COUNTER_FFI.get_or_init(|| {
        // Create method entries with computed hashes
        let mut methods = vec![
            FfiMethodEntry::new(
                fnv1a_hash(METHOD_GET),
                METHOD_GET.as_ptr(),
                METHOD_GET.len() as u32,
                method_flags::RETURNS_VALUE,
                counter_get_ffi as *const (),
            ),
            FfiMethodEntry::new(
                fnv1a_hash(METHOD_INCREMENT),
                METHOD_INCREMENT.as_ptr(),
                METHOD_INCREMENT.len() as u32,
                method_flags::MUTABLE,
                counter_increment_ffi as *const (),
            ),
            FfiMethodEntry::new(
                fnv1a_hash(METHOD_INCREMENT_BY),
                METHOD_INCREMENT_BY.as_ptr(),
                METHOD_INCREMENT_BY.len() as u32,
                method_flags::MUTABLE,
                counter_increment_by_ffi as *const (),
            ),
            FfiMethodEntry::new(
                fnv1a_hash(METHOD_RESET),
                METHOD_RESET.as_ptr(),
                METHOD_RESET.len() as u32,
                method_flags::MUTABLE,
                counter_reset_ffi as *const (),
            ),
            FfiMethodEntry::new(
                fnv1a_hash(METHOD_SET),
                METHOD_SET.as_ptr(),
                METHOD_SET.len() as u32,
                method_flags::MUTABLE,
                counter_set_ffi as *const (),
            ),
        ];

        // Sort by name_hash for binary search
        methods.sort_by_key(|m| m.name_hash);

        let methods = methods.into_boxed_slice();

        // Create vtable
        let vtable = FfiVtable::new(
            COUNTER_TYPE_NAME.as_ptr(),
            COUNTER_TYPE_NAME.len() as u32,
            methods.len() as u32,
            methods.as_ptr(),
            Some(counter_drop_ffi),
            Some(counter_clone_ffi),
        );

        CounterFfi { methods, vtable }
    })
}

// ============================================================================
// FFI Functions
// ============================================================================

/// Register the Counter type with the global registry.
/// Returns the type ID (or 0 if already registered).
#[no_mangle]
pub extern "C" fn counter_register_type() -> u32 {
    let ffi = get_counter_ffi();
    get_registry().register_type("Counter", &ffi.vtable)
}

/// Get the Counter vtable.
pub fn counter_vtable() -> *const FfiVtable {
    let ffi = get_counter_ffi();
    &ffi.vtable
}

/// Create a new Counter FFI object.
#[no_mangle]
pub extern "C" fn counter_new_ffi(initial: i64) -> RuntimeValue {
    // Ensure FFI is initialized
    let _ = get_counter_ffi();

    // Get or register the type
    let type_id = {
        let id = get_registry().get_type_id("Counter");
        if id == 0 {
            counter_register_type()
        } else {
            id
        }
    };

    if type_id == 0 {
        return RuntimeValue::NIL;
    }

    // Create the counter and store it
    let counter = Counter::new(initial);
    get_registry().create_object(type_id, counter)
}

/// Drop function called when the FFI object is destroyed.
unsafe extern "C" fn counter_drop_ffi(handle: u32) {
    // The object is stored in the registry, which will drop it automatically
    // when removed. This function is just a hook for custom cleanup if needed.
    let _ = handle;
}

/// Clone function to create a copy of the counter.
unsafe extern "C" fn counter_clone_ffi(handle: u32) -> u32 {
    let type_id = get_registry().get_type_id("Counter");
    if type_id == 0 {
        return 0;
    }

    get_registry()
        .with_storage(type_id, |storage| {
            storage.with::<Counter, _, _>(handle, |counter| {
                let cloned = counter.clone();
                storage.insert(cloned)
            })
        })
        .flatten()
        .unwrap_or(0)
}

/// Get the counter value.
unsafe extern "C" fn counter_get_ffi(
    handle: u32,
    _argc: u32,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let type_id = get_registry().get_type_id("Counter");
    if type_id == 0 {
        return RuntimeValue::NIL;
    }

    get_registry()
        .with_storage(type_id, |storage| {
            storage.with::<Counter, _, _>(handle, |counter| counter.get().into_runtime_value())
        })
        .flatten()
        .unwrap_or(RuntimeValue::NIL)
}

/// Increment the counter by 1.
unsafe extern "C" fn counter_increment_ffi(
    handle: u32,
    _argc: u32,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let type_id = get_registry().get_type_id("Counter");
    if type_id == 0 {
        return RuntimeValue::NIL;
    }

    get_registry()
        .with_storage(type_id, |storage| {
            storage.with_mut::<Counter, _, _>(handle, |counter| {
                counter.increment();
                RuntimeValue::NIL
            })
        })
        .flatten()
        .unwrap_or(RuntimeValue::NIL)
}

/// Increment the counter by a specific amount.
unsafe extern "C" fn counter_increment_by_ffi(
    handle: u32,
    argc: u32,
    argv: *const RuntimeValue,
) -> RuntimeValue {
    let type_id = get_registry().get_type_id("Counter");
    if type_id == 0 {
        return RuntimeValue::NIL;
    }

    let amount = get_arg_as::<i64>(argv, argc, 0).unwrap_or(1);

    get_registry()
        .with_storage(type_id, |storage| {
            storage.with_mut::<Counter, _, _>(handle, |counter| {
                counter.increment_by(amount);
                RuntimeValue::NIL
            })
        })
        .flatten()
        .unwrap_or(RuntimeValue::NIL)
}

/// Reset the counter to 0.
unsafe extern "C" fn counter_reset_ffi(
    handle: u32,
    _argc: u32,
    _argv: *const RuntimeValue,
) -> RuntimeValue {
    let type_id = get_registry().get_type_id("Counter");
    if type_id == 0 {
        return RuntimeValue::NIL;
    }

    get_registry()
        .with_storage(type_id, |storage| {
            storage.with_mut::<Counter, _, _>(handle, |counter| {
                counter.reset();
                RuntimeValue::NIL
            })
        })
        .flatten()
        .unwrap_or(RuntimeValue::NIL)
}

/// Set the counter to a specific value.
unsafe extern "C" fn counter_set_ffi(
    handle: u32,
    argc: u32,
    argv: *const RuntimeValue,
) -> RuntimeValue {
    let type_id = get_registry().get_type_id("Counter");
    if type_id == 0 {
        return RuntimeValue::NIL;
    }

    let value = get_arg_as::<i64>(argv, argc, 0).unwrap_or(0);

    get_registry()
        .with_storage(type_id, |storage| {
            storage.with_mut::<Counter, _, _>(handle, |counter| {
                counter.set(value);
                RuntimeValue::NIL
            })
        })
        .flatten()
        .unwrap_or(RuntimeValue::NIL)
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::ffi_object::rt_ffi_object_is_ffi;
    use crate::value::ffi_registry::rt_ffi_clear_registry;

    #[test]
    fn test_counter_create_and_use() {
        // Clear registry for test isolation
        rt_ffi_clear_registry();

        // Create a counter
        let counter = counter_new_ffi(10);
        assert!(!counter.is_nil());
        assert!(rt_ffi_object_is_ffi(counter));

        // Get value
        unsafe {
            let handle = super::super::ffi_object::rt_ffi_object_handle(counter);
            let value = counter_get_ffi(handle, 0, std::ptr::null());
            assert!(value.is_int());
            assert_eq!(value.as_int(), 10);
        }
    }

    #[test]
    fn test_counter_increment() {
        rt_ffi_clear_registry();

        let counter = counter_new_ffi(0);
        assert!(!counter.is_nil());

        unsafe {
            let handle = super::super::ffi_object::rt_ffi_object_handle(counter);

            // Increment
            counter_increment_ffi(handle, 0, std::ptr::null());
            counter_increment_ffi(handle, 0, std::ptr::null());
            counter_increment_ffi(handle, 0, std::ptr::null());

            // Get value
            let value = counter_get_ffi(handle, 0, std::ptr::null());
            assert_eq!(value.as_int(), 3);
        }
    }

    #[test]
    fn test_counter_increment_by() {
        rt_ffi_clear_registry();

        let counter = counter_new_ffi(0);
        assert!(!counter.is_nil());

        unsafe {
            let handle = super::super::ffi_object::rt_ffi_object_handle(counter);

            // Increment by 5
            let args = [RuntimeValue::from_int(5)];
            counter_increment_by_ffi(handle, 1, args.as_ptr());

            // Get value
            let value = counter_get_ffi(handle, 0, std::ptr::null());
            assert_eq!(value.as_int(), 5);

            // Increment by 10
            let args = [RuntimeValue::from_int(10)];
            counter_increment_by_ffi(handle, 1, args.as_ptr());

            let value = counter_get_ffi(handle, 0, std::ptr::null());
            assert_eq!(value.as_int(), 15);
        }
    }

    #[test]
    fn test_counter_reset() {
        rt_ffi_clear_registry();

        let counter = counter_new_ffi(100);

        unsafe {
            let handle = super::super::ffi_object::rt_ffi_object_handle(counter);

            // Reset
            counter_reset_ffi(handle, 0, std::ptr::null());

            // Get value
            let value = counter_get_ffi(handle, 0, std::ptr::null());
            assert_eq!(value.as_int(), 0);
        }
    }

    #[test]
    fn test_counter_set() {
        rt_ffi_clear_registry();

        let counter = counter_new_ffi(0);

        unsafe {
            let handle = super::super::ffi_object::rt_ffi_object_handle(counter);

            // Set to 42
            let args = [RuntimeValue::from_int(42)];
            counter_set_ffi(handle, 1, args.as_ptr());

            // Get value
            let value = counter_get_ffi(handle, 0, std::ptr::null());
            assert_eq!(value.as_int(), 42);
        }
    }

    #[test]
    fn test_counter_type_registration() {
        rt_ffi_clear_registry();

        // Register the type
        let type_id = counter_register_type();
        assert_ne!(type_id, 0);

        // Duplicate registration should fail
        let dup_id = counter_register_type();
        assert_eq!(dup_id, 0);

        // Look up by name
        let found_id = get_registry().get_type_id("Counter");
        assert_eq!(found_id, type_id);
    }

    #[test]
    fn test_counter_method_lookup() {
        rt_ffi_clear_registry();

        unsafe {
            let vtable = &*counter_vtable();

            // Check method count
            assert_eq!(vtable.method_count, 5);

            // Look up methods
            assert!(vtable.has_method("get"));
            assert!(vtable.has_method("increment"));
            assert!(vtable.has_method("increment_by"));
            assert!(vtable.has_method("reset"));
            assert!(vtable.has_method("set"));
            assert!(!vtable.has_method("nonexistent"));
        }
    }

    #[test]
    fn test_counter_drop() {
        rt_ffi_clear_registry();

        // Create counters
        let _c1 = counter_new_ffi(1);
        let _c2 = counter_new_ffi(2);
        let _c3 = counter_new_ffi(3);

        // Check object count
        let type_id = get_registry().get_type_id("Counter");
        assert_eq!(get_registry().object_count(type_id), 3);

        // Drop one (using registry)
        unsafe {
            get_registry().drop_object(_c1);
        }

        // Check object count decreased
        assert_eq!(get_registry().object_count(type_id), 2);
    }
}
