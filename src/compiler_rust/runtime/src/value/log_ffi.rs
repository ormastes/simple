//! Logging FFI functions for Simple programs
//!
//! These functions provide logging functionality with levels 0-10.
//! Uses LogLevel from simple-hir-core for shared type definitions.

use crate::hir_core::LogLevel;
use std::collections::HashMap;
use std::sync::{Mutex, OnceLock};

use super::{rt_string_data, rt_string_len, RuntimeValue};

// ============================================================================
// Global State
// ============================================================================

/// Global log level (default: INFO = 4)
static GLOBAL_LEVEL: Mutex<u8> = Mutex::new(4);

/// Per-scope log levels
static SCOPE_LEVELS: OnceLock<Mutex<HashMap<String, u8>>> = OnceLock::new();

fn scope_levels() -> &'static Mutex<HashMap<String, u8>> {
    SCOPE_LEVELS.get_or_init(|| Mutex::new(HashMap::new()))
}

// ============================================================================
// Level Management
// ============================================================================

/// Set global log level (0-10)
#[no_mangle]
pub extern "C" fn rt_log_set_global_level(level: i64) {
    let level = level.clamp(0, 10) as u8;
    if let Ok(mut global) = GLOBAL_LEVEL.lock() {
        *global = level;
    }
}

/// Get global log level
#[no_mangle]
pub extern "C" fn rt_log_get_global_level() -> i64 {
    GLOBAL_LEVEL.lock().map(|g| *g as i64).unwrap_or(4)
}

/// Set log level for a specific scope
#[no_mangle]
pub extern "C" fn rt_log_set_scope_level(scope_ptr: *const u8, scope_len: u64, level: i64) {
    if scope_ptr.is_null() || scope_len == 0 {
        return;
    }
    let scope = unsafe {
        let slice = std::slice::from_raw_parts(scope_ptr, scope_len as usize);
        String::from_utf8_lossy(slice).to_string()
    };
    let level = level.clamp(0, 10) as u8;
    if let Ok(mut levels) = scope_levels().lock() {
        levels.insert(scope, level);
    }
}

/// Get log level for a specific scope (returns scope level or global if not set)
#[no_mangle]
pub extern "C" fn rt_log_get_scope_level(scope_ptr: *const u8, scope_len: u64) -> i64 {
    if scope_ptr.is_null() || scope_len == 0 {
        return rt_log_get_global_level();
    }
    let scope = unsafe {
        let slice = std::slice::from_raw_parts(scope_ptr, scope_len as usize);
        String::from_utf8_lossy(slice).to_string()
    };
    if let Ok(levels) = scope_levels().lock() {
        if let Some(&level) = levels.get(&scope) {
            return level as i64;
        }
    }
    rt_log_get_global_level()
}

/// Clear scope-specific log levels
#[no_mangle]
pub extern "C" fn rt_log_clear_scope_levels() {
    if let Ok(mut levels) = scope_levels().lock() {
        levels.clear();
    }
}

// ============================================================================
// Log Emission
// ============================================================================

/// Emit a log message with level and scope
///
/// # Arguments
/// - `level`: Log level (0-10)
/// - `scope_ptr`, `scope_len`: Scope name (e.g., "parser", "gc")
/// - `msg_ptr`, `msg_len`: Message to log
#[no_mangle]
pub extern "C" fn rt_log_emit(level: i64, scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    // Get current log level for scope
    let current_level = rt_log_get_scope_level(scope_ptr, scope_len);

    // Check if message should be logged
    if level > current_level {
        return;
    }

    // Extract scope string
    let scope = if scope_ptr.is_null() || scope_len == 0 {
        "app".to_string()
    } else {
        unsafe {
            let slice = std::slice::from_raw_parts(scope_ptr, scope_len as usize);
            String::from_utf8_lossy(slice).to_string()
        }
    };

    // Extract message string
    let msg = if msg_ptr.is_null() || msg_len == 0 {
        String::new()
    } else {
        unsafe {
            let slice = std::slice::from_raw_parts(msg_ptr, msg_len as usize);
            String::from_utf8_lossy(slice).to_string()
        }
    };

    // Get level name using hir-core LogLevel
    let log_level = LogLevel::from_u8(level as u8);
    let level_name = log_level.name().to_uppercase();

    // Format and print
    let prefix = match level {
        0 => return, // Off - don't log
        1 => "[FATAL]",
        2 => "[ERROR]",
        3 => "[WARN] ",
        4 => "[INFO] ",
        5 => "[DEBUG]",
        6 => "[TRACE]",
        7 => "[VERB] ",
        _ => "[LOG]  ",
    };

    // Use stderr for all log output
    eprintln!("{} [{}] {}", prefix, scope, msg);
}

/// Emit log message from RuntimeValue strings
#[no_mangle]
pub extern "C" fn rt_log_emit_rv(level: i64, scope: RuntimeValue, msg: RuntimeValue) {
    let scope_ptr = rt_string_data(scope);
    let scope_len = rt_string_len(scope) as u64;
    let msg_ptr = rt_string_data(msg);
    let msg_len = rt_string_len(msg) as u64;

    rt_log_emit(level, scope_ptr, scope_len, msg_ptr, msg_len);
}

// ============================================================================
// Convenience Functions
// ============================================================================

/// Log fatal error (level 1)
#[no_mangle]
pub extern "C" fn rt_log_fatal(scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    rt_log_emit(1, scope_ptr, scope_len, msg_ptr, msg_len);
}

/// Log error (level 2)
#[no_mangle]
pub extern "C" fn rt_log_error(scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    rt_log_emit(2, scope_ptr, scope_len, msg_ptr, msg_len);
}

/// Log warning (level 3)
#[no_mangle]
pub extern "C" fn rt_log_warn(scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    rt_log_emit(3, scope_ptr, scope_len, msg_ptr, msg_len);
}

/// Log info (level 4)
#[no_mangle]
pub extern "C" fn rt_log_info(scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    rt_log_emit(4, scope_ptr, scope_len, msg_ptr, msg_len);
}

/// Log debug (level 5)
#[no_mangle]
pub extern "C" fn rt_log_debug(scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    rt_log_emit(5, scope_ptr, scope_len, msg_ptr, msg_len);
}

/// Log trace (level 6)
#[no_mangle]
pub extern "C" fn rt_log_trace(scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    rt_log_emit(6, scope_ptr, scope_len, msg_ptr, msg_len);
}

/// Log verbose (level 7)
#[no_mangle]
pub extern "C" fn rt_log_verbose(scope_ptr: *const u8, scope_len: u64, msg_ptr: *const u8, msg_len: u64) {
    rt_log_emit(7, scope_ptr, scope_len, msg_ptr, msg_len);
}

// ============================================================================
// Log Level Info
// ============================================================================

/// Get log level name
#[no_mangle]
pub extern "C" fn rt_log_level_name(level: i64) -> *const u8 {
    let log_level = LogLevel::from_u8(level as u8);
    log_level.name().as_ptr()
}

/// Check if logging is enabled at level for scope
#[no_mangle]
pub extern "C" fn rt_log_is_enabled(level: i64, scope_ptr: *const u8, scope_len: u64) -> u8 {
    let current_level = rt_log_get_scope_level(scope_ptr, scope_len);
    if level <= current_level {
        1
    } else {
        0
    }
}

// ============================================================================
// Registry Cleanup
// ============================================================================

/// Clear log state for test isolation
pub fn clear_log_state() {
    if let Ok(mut global) = GLOBAL_LEVEL.lock() {
        *global = 4; // Reset to INFO
    }
    rt_log_clear_scope_levels();
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_global_level() {
        clear_log_state();

        // Default is INFO (4)
        assert_eq!(rt_log_get_global_level(), 4);

        // Set to DEBUG (5)
        rt_log_set_global_level(5);
        assert_eq!(rt_log_get_global_level(), 5);

        // Reset
        clear_log_state();
        assert_eq!(rt_log_get_global_level(), 4);
    }

    #[test]
    fn test_scope_level() {
        clear_log_state();

        let scope = b"parser";

        // Initially returns global level
        assert_eq!(rt_log_get_scope_level(scope.as_ptr(), scope.len() as u64), 4);

        // Set scope level
        rt_log_set_scope_level(scope.as_ptr(), scope.len() as u64, 6);
        assert_eq!(rt_log_get_scope_level(scope.as_ptr(), scope.len() as u64), 6);

        // Global still unchanged
        assert_eq!(rt_log_get_global_level(), 4);

        // Clear scope levels
        rt_log_clear_scope_levels();
        assert_eq!(rt_log_get_scope_level(scope.as_ptr(), scope.len() as u64), 4);
    }

    #[test]
    fn test_is_enabled() {
        clear_log_state();

        // At INFO level (4), ERROR (2) should be enabled
        assert_eq!(rt_log_is_enabled(2, std::ptr::null(), 0), 1);

        // At INFO level (4), DEBUG (5) should be disabled
        assert_eq!(rt_log_is_enabled(5, std::ptr::null(), 0), 0);

        // Set to DEBUG
        rt_log_set_global_level(5);
        assert_eq!(rt_log_is_enabled(5, std::ptr::null(), 0), 1);

        clear_log_state();
    }

    #[test]
    fn test_level_clamping() {
        clear_log_state();

        // Negative clamps to 0
        rt_log_set_global_level(-5);
        assert_eq!(rt_log_get_global_level(), 0);

        // Over 10 clamps to 10
        rt_log_set_global_level(100);
        assert_eq!(rt_log_get_global_level(), 10);

        clear_log_state();
    }
}
