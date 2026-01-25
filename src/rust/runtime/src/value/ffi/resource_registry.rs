//! Resource Registry FFI functions.
//!
//! Provides thread-local storage for tracking open resources to enable leak detection.
//! This is particularly useful for ensuring resources are properly cleaned up in tests.
//!
//! ## Usage Pattern
//!
//! ```ignore
//! use simple_runtime::value::ffi::resource_registry::*;
//! use std::ffi::CString;
//!
//! // Register a resource when opened
//! let name = CString::new("File").unwrap();
//! let location = CString::new("File.open(\"test.txt\")").unwrap();
//! let id = rt_resource_registry_register(name.as_ptr(), location.as_ptr());
//!
//! // ... use the resource ...
//!
//! // Unregister when closed
//! rt_resource_registry_unregister(id);
//!
//! // Check for leaks at the end of a test
//! let count = rt_resource_registry_count();
//! assert_eq!(count, 0, "Resource leaks detected!");
//! ```

use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::atomic::{AtomicI64, Ordering};
use std::ffi::{CStr, CString};
use std::os::raw::c_char;

/// Internal resource entry
#[derive(Clone, Debug)]
struct ResourceEntry {
    id: i64,
    resource_name: String,
    location: String,
    created_at: i64,
}

/// Global ID counter for unique resource IDs
static NEXT_RESOURCE_ID: AtomicI64 = AtomicI64::new(1);

thread_local! {
    /// Thread-local registry of open resources
    static RESOURCE_REGISTRY: RefCell<HashMap<i64, ResourceEntry>> = RefCell::new(HashMap::new());
}

// ============================================================================
// Registration Functions
// ============================================================================

/// Register a resource for leak tracking.
///
/// Returns a unique ID that must be passed to unregister when the resource is closed.
///
/// # Arguments
/// * `resource_name` - Name of the resource type (e.g., "File", "TcpStream")
/// * `location` - Source location or context where resource was created
///
/// # Returns
/// Unique ID for this resource registration
#[no_mangle]
pub extern "C" fn rt_resource_registry_register(
    resource_name: *const c_char,
    location: *const c_char,
) -> i64 {
    let resource_name = if resource_name.is_null() {
        "Unknown".to_string()
    } else {
        unsafe { CStr::from_ptr(resource_name) }
            .to_string_lossy()
            .to_string()
    };

    let location = if location.is_null() {
        "Unknown".to_string()
    } else {
        unsafe { CStr::from_ptr(location) }
            .to_string_lossy()
            .to_string()
    };

    let id = NEXT_RESOURCE_ID.fetch_add(1, Ordering::SeqCst);
    let created_at = crate::value::ffi::time::rt_time_now_unix_micros();

    let entry = ResourceEntry {
        id,
        resource_name,
        location,
        created_at,
    };

    RESOURCE_REGISTRY.with(|registry| {
        registry.borrow_mut().insert(id, entry);
    });

    id
}

/// Unregister a resource (call when the resource is closed).
///
/// # Arguments
/// * `id` - The ID returned from register
#[no_mangle]
pub extern "C" fn rt_resource_registry_unregister(id: i64) {
    RESOURCE_REGISTRY.with(|registry| {
        registry.borrow_mut().remove(&id);
    });
}

// ============================================================================
// Query Functions
// ============================================================================

/// Get the count of currently open resources.
///
/// # Returns
/// Number of resources currently tracked
#[no_mangle]
pub extern "C" fn rt_resource_registry_count() -> i64 {
    RESOURCE_REGISTRY.with(|registry| registry.borrow().len() as i64)
}

/// Check if any resources are still open (leaks).
///
/// # Returns
/// true if there are open resources, false otherwise
#[no_mangle]
pub extern "C" fn rt_resource_registry_has_leaks() -> bool {
    RESOURCE_REGISTRY.with(|registry| !registry.borrow().is_empty())
}

/// Get a leak report as a C string.
///
/// The returned string must be freed by the caller using rt_free_string.
///
/// # Returns
/// Pointer to a C string containing the leak report, or NULL if no leaks
#[no_mangle]
pub extern "C" fn rt_resource_registry_leak_report() -> *mut c_char {
    let entries: Vec<ResourceEntry> = RESOURCE_REGISTRY.with(|registry| {
        registry.borrow().values().cloned().collect()
    });

    if entries.is_empty() {
        return std::ptr::null_mut();
    }

    let mut report = format!("Resource Leaks Detected ({}):\n", entries.len());
    for entry in entries {
        report.push_str(&format!(
            "  - {} created at {}\n",
            entry.resource_name, entry.location
        ));
    }

    match CString::new(report) {
        Ok(cstr) => cstr.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

// ============================================================================
// Cleanup Functions
// ============================================================================

/// Clear all entries from the registry.
///
/// Use this to reset state between tests.
#[no_mangle]
pub extern "C" fn rt_resource_registry_clear() {
    RESOURCE_REGISTRY.with(|registry| {
        registry.borrow_mut().clear();
    });
}

/// Close all tracked resources (emergency cleanup).
///
/// Note: This only clears the registry. Actual resource cleanup depends on
/// the Resource implementations calling their close() methods.
#[no_mangle]
pub extern "C" fn rt_resource_registry_close_all() {
    // For now, just clear the registry.
    // In a future enhancement, we could store closures to call close() on each resource.
    RESOURCE_REGISTRY.with(|registry| {
        registry.borrow_mut().clear();
    });
}

// ============================================================================
// Memory Management
// ============================================================================

/// Free a string returned by rt_resource_registry_leak_report.
///
/// # Safety
/// The pointer must have been returned by rt_resource_registry_leak_report.
#[no_mangle]
pub extern "C" fn rt_resource_registry_free_string(ptr: *mut c_char) {
    if !ptr.is_null() {
        unsafe {
            let _ = CString::from_raw(ptr);
        }
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_and_unregister() {
        // Clear any existing entries
        rt_resource_registry_clear();

        let name = CString::new("File").unwrap();
        let location = CString::new("test.txt").unwrap();

        let id = rt_resource_registry_register(name.as_ptr(), location.as_ptr());
        assert!(id > 0);
        assert_eq!(rt_resource_registry_count(), 1);
        assert!(rt_resource_registry_has_leaks());

        rt_resource_registry_unregister(id);
        assert_eq!(rt_resource_registry_count(), 0);
        assert!(!rt_resource_registry_has_leaks());
    }

    #[test]
    fn test_multiple_resources() {
        rt_resource_registry_clear();

        let file1 = CString::new("File").unwrap();
        let loc1 = CString::new("file1.txt").unwrap();
        let file2 = CString::new("TcpStream").unwrap();
        let loc2 = CString::new("localhost:8080").unwrap();

        let id1 = rt_resource_registry_register(file1.as_ptr(), loc1.as_ptr());
        let id2 = rt_resource_registry_register(file2.as_ptr(), loc2.as_ptr());

        assert_eq!(rt_resource_registry_count(), 2);
        assert_ne!(id1, id2);

        rt_resource_registry_unregister(id1);
        assert_eq!(rt_resource_registry_count(), 1);

        rt_resource_registry_unregister(id2);
        assert_eq!(rt_resource_registry_count(), 0);
    }

    #[test]
    fn test_leak_report() {
        rt_resource_registry_clear();

        let report = rt_resource_registry_leak_report();
        assert!(report.is_null()); // No leaks

        let name = CString::new("Socket").unwrap();
        let location = CString::new("network.rs:42").unwrap();
        let _id = rt_resource_registry_register(name.as_ptr(), location.as_ptr());

        let report = rt_resource_registry_leak_report();
        assert!(!report.is_null());

        let report_str = unsafe { CStr::from_ptr(report) }.to_string_lossy();
        assert!(report_str.contains("Socket"));
        assert!(report_str.contains("network.rs:42"));

        rt_resource_registry_free_string(report);
        rt_resource_registry_clear();
    }
}
