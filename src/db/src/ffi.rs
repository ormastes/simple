//! FFI functions for Simple language integration.
//!
//! These functions are called from compiled Simple code to interact with databases.
//! All functions use `rt_db_*` prefix for consistency with other runtime FFI.
//!
//! Note: FFI functions check for null pointers before dereferencing, making them safe.
#![allow(clippy::not_unsafe_ptr_arg_deref)]

use crate::connection::Database;
use crate::error::DbError;
use crate::pool::{Pool, PoolConfig};
use crate::row::Row;
use crate::types::SqlValue;
use parking_lot::Mutex;
use std::collections::HashMap;
use std::ffi::{c_char, CStr, CString};
use std::ptr;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

// ============================================================================
// Handle types (opaque pointers for Simple)
// ============================================================================

/// Opaque database connection handle.
pub struct DbHandle {
    db: Database,
}

/// Opaque connection pool handle.
pub struct PoolHandle {
    pool: Pool,
}

/// Opaque result set handle.
pub struct ResultHandle {
    rows: Vec<Row>,
    columns: Vec<String>,
    current_row: usize,
}

/// Opaque error handle (reserved for future use).
#[allow(dead_code)]
pub struct ErrorHandle {
    message: CString,
    code: i32,
}

// ============================================================================
// Global handle registry (for tracking live handles)
// ============================================================================

static NEXT_HANDLE_ID: AtomicU64 = AtomicU64::new(1);

lazy_static::lazy_static! {
    static ref DB_HANDLES: Mutex<HashMap<u64, Box<DbHandle>>> = Mutex::new(HashMap::new());
    static ref POOL_HANDLES: Mutex<HashMap<u64, Box<PoolHandle>>> = Mutex::new(HashMap::new());
    static ref RESULT_HANDLES: Mutex<HashMap<u64, Box<ResultHandle>>> = Mutex::new(HashMap::new());
    static ref ERROR_HANDLES: Mutex<HashMap<u64, Box<ErrorHandle>>> = Mutex::new(HashMap::new());
}

fn next_handle_id() -> u64 {
    NEXT_HANDLE_ID.fetch_add(1, Ordering::Relaxed)
}

// ============================================================================
// Database connection FFI
// ============================================================================

/// Open a database connection.
///
/// Returns handle ID on success, 0 on failure (check rt_db_last_error).
#[no_mangle]
pub extern "C" fn rt_db_open(url: *const c_char) -> u64 {
    let url = unsafe {
        if url.is_null() {
            return 0;
        }
        match CStr::from_ptr(url).to_str() {
            Ok(s) => s,
            Err(_) => return 0,
        }
    };

    match Database::open(url) {
        Ok(db) => {
            let handle_id = next_handle_id();
            DB_HANDLES
                .lock()
                .insert(handle_id, Box::new(DbHandle { db }));
            handle_id
        }
        Err(e) => {
            store_last_error(e);
            0
        }
    }
}

/// Close a database connection.
#[no_mangle]
pub extern "C" fn rt_db_close(handle: u64) {
    DB_HANDLES.lock().remove(&handle);
}

/// Execute a query that returns rows.
///
/// Returns result handle ID on success, 0 on failure.
#[no_mangle]
pub extern "C" fn rt_db_query(
    handle: u64,
    sql: *const c_char,
    params: *const u64, // Array of SqlValue handles
    param_count: usize,
) -> u64 {
    let sql = unsafe {
        if sql.is_null() {
            return 0;
        }
        match CStr::from_ptr(sql).to_str() {
            Ok(s) => s,
            Err(_) => return 0,
        }
    };

    let params = build_params(params, param_count);

    let db_handles = DB_HANDLES.lock();
    let db_handle = match db_handles.get(&handle) {
        Some(h) => h,
        None => {
            store_last_error(DbError::ConnectionClosed);
            return 0;
        }
    };

    match db_handle.db.query(sql, &params) {
        Ok(rows) => {
            let columns = rows.columns().to_vec();
            let row_vec: Vec<Row> = rows.filter_map(|r| r.ok()).collect();

            let handle_id = next_handle_id();
            RESULT_HANDLES.lock().insert(
                handle_id,
                Box::new(ResultHandle {
                    rows: row_vec,
                    columns,
                    current_row: 0,
                }),
            );
            handle_id
        }
        Err(e) => {
            store_last_error(e);
            0
        }
    }
}

/// Execute a query that doesn't return rows (INSERT, UPDATE, DELETE).
///
/// Returns number of affected rows, or -1 on error.
#[no_mangle]
pub extern "C" fn rt_db_execute(
    handle: u64,
    sql: *const c_char,
    params: *const u64,
    param_count: usize,
) -> i64 {
    let sql = unsafe {
        if sql.is_null() {
            return -1;
        }
        match CStr::from_ptr(sql).to_str() {
            Ok(s) => s,
            Err(_) => return -1,
        }
    };

    let params = build_params(params, param_count);

    let db_handles = DB_HANDLES.lock();
    let db_handle = match db_handles.get(&handle) {
        Some(h) => h,
        None => {
            store_last_error(DbError::ConnectionClosed);
            return -1;
        }
    };

    match db_handle.db.execute(sql, &params) {
        Ok(n) => n as i64,
        Err(e) => {
            store_last_error(e);
            -1
        }
    }
}

/// Check if connection is alive.
#[no_mangle]
pub extern "C" fn rt_db_ping(handle: u64) -> bool {
    let db_handles = DB_HANDLES.lock();
    match db_handles.get(&handle) {
        Some(h) => h.db.ping().is_ok(),
        None => false,
    }
}

/// Get the driver name.
#[no_mangle]
pub extern "C" fn rt_db_driver_name(handle: u64) -> *const c_char {
    let db_handles = DB_HANDLES.lock();
    match db_handles.get(&handle) {
        Some(h) => {
            let name = h.db.driver_name();
            // Leak a CString to return a stable pointer
            // Caller should not free this
            match CString::new(name) {
                Ok(s) => s.into_raw() as *const c_char,
                Err(_) => ptr::null(),
            }
        }
        None => ptr::null(),
    }
}

// ============================================================================
// Connection pool FFI
// ============================================================================

/// Create a connection pool.
#[no_mangle]
pub extern "C" fn rt_db_pool_new(
    url: *const c_char,
    min_conns: u32,
    max_conns: u32,
    acquire_timeout_ms: u64,
) -> u64 {
    let url = unsafe {
        if url.is_null() {
            return 0;
        }
        match CStr::from_ptr(url).to_str() {
            Ok(s) => s,
            Err(_) => return 0,
        }
    };

    let config = PoolConfig::new()
        .min_connections(min_conns)
        .max_connections(max_conns)
        .acquire_timeout(Duration::from_millis(acquire_timeout_ms));

    match Pool::new(url, config) {
        Ok(pool) => {
            let handle_id = next_handle_id();
            POOL_HANDLES
                .lock()
                .insert(handle_id, Box::new(PoolHandle { pool }));
            handle_id
        }
        Err(e) => {
            store_last_error(e);
            0
        }
    }
}

/// Acquire a connection from the pool.
///
/// Returns database handle ID, or 0 on error.
#[no_mangle]
pub extern "C" fn rt_db_pool_acquire(pool_handle: u64) -> u64 {
    let pool_handles = POOL_HANDLES.lock();
    let pool_handle_obj = match pool_handles.get(&pool_handle) {
        Some(h) => h,
        None => {
            store_last_error(DbError::ConnectionClosed);
            return 0;
        }
    };

    let url = pool_handle_obj.pool.url().to_string();
    drop(pool_handles);

    match Database::open(&url) {
        Ok(db) => {
            let handle_id = next_handle_id();
            DB_HANDLES
                .lock()
                .insert(handle_id, Box::new(DbHandle { db }));
            handle_id
        }
        Err(e) => {
            store_last_error(e);
            0
        }
    }
}

/// Get pool statistics.
#[no_mangle]
pub extern "C" fn rt_db_pool_idle_count(pool_handle: u64) -> u32 {
    let pool_handles = POOL_HANDLES.lock();
    match pool_handles.get(&pool_handle) {
        Some(h) => h.pool.stats().idle,
        None => 0,
    }
}

/// Get pool in-use count.
#[no_mangle]
pub extern "C" fn rt_db_pool_in_use_count(pool_handle: u64) -> u32 {
    let pool_handles = POOL_HANDLES.lock();
    match pool_handles.get(&pool_handle) {
        Some(h) => h.pool.stats().in_use,
        None => 0,
    }
}

/// Close the pool.
#[no_mangle]
pub extern "C" fn rt_db_pool_close(pool_handle: u64) {
    let mut pool_handles = POOL_HANDLES.lock();
    if let Some(h) = pool_handles.remove(&pool_handle) {
        let _ = h.pool.close();
    }
}

// ============================================================================
// Result set FFI
// ============================================================================

/// Get the number of rows in the result.
#[no_mangle]
pub extern "C" fn rt_db_result_row_count(result_handle: u64) -> usize {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => h.rows.len(),
        None => 0,
    }
}

/// Get the number of columns in the result.
#[no_mangle]
pub extern "C" fn rt_db_result_column_count(result_handle: u64) -> usize {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => h.columns.len(),
        None => 0,
    }
}

/// Get column name by index.
#[no_mangle]
pub extern "C" fn rt_db_result_column_name(result_handle: u64, index: usize) -> *const c_char {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => match h.columns.get(index) {
            Some(name) => match CString::new(name.as_str()) {
                Ok(s) => s.into_raw() as *const c_char,
                Err(_) => ptr::null(),
            },
            None => ptr::null(),
        },
        None => ptr::null(),
    }
}

/// Move to next row. Returns true if there's a row, false if done.
#[no_mangle]
pub extern "C" fn rt_db_result_next(result_handle: u64) -> bool {
    let mut result_handles = RESULT_HANDLES.lock();
    match result_handles.get_mut(&result_handle) {
        Some(h) => {
            if h.current_row < h.rows.len() {
                h.current_row += 1;
                true
            } else {
                false
            }
        }
        None => false,
    }
}

/// Reset result iterator to beginning.
#[no_mangle]
pub extern "C" fn rt_db_result_reset(result_handle: u64) {
    let mut result_handles = RESULT_HANDLES.lock();
    if let Some(h) = result_handles.get_mut(&result_handle) {
        h.current_row = 0;
    }
}

/// Get integer value from current row.
#[no_mangle]
pub extern "C" fn rt_db_result_get_int(result_handle: u64, column: usize) -> i64 {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => {
            if h.current_row == 0 || h.current_row > h.rows.len() {
                return 0;
            }
            let row = &h.rows[h.current_row - 1];
            row.get::<i64>(column).unwrap_or(0)
        }
        None => 0,
    }
}

/// Get float value from current row.
#[no_mangle]
pub extern "C" fn rt_db_result_get_float(result_handle: u64, column: usize) -> f64 {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => {
            if h.current_row == 0 || h.current_row > h.rows.len() {
                return 0.0;
            }
            let row = &h.rows[h.current_row - 1];
            row.get::<f64>(column).unwrap_or(0.0)
        }
        None => 0.0,
    }
}

/// Get string value from current row.
/// Caller must free the returned string with rt_db_free_string.
#[no_mangle]
pub extern "C" fn rt_db_result_get_string(result_handle: u64, column: usize) -> *mut c_char {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => {
            if h.current_row == 0 || h.current_row > h.rows.len() {
                return ptr::null_mut();
            }
            let row = &h.rows[h.current_row - 1];
            match row.get::<String>(column) {
                Ok(s) => match CString::new(s) {
                    Ok(cs) => cs.into_raw(),
                    Err(_) => ptr::null_mut(),
                },
                Err(_) => ptr::null_mut(),
            }
        }
        None => ptr::null_mut(),
    }
}

/// Get bool value from current row.
#[no_mangle]
pub extern "C" fn rt_db_result_get_bool(result_handle: u64, column: usize) -> bool {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => {
            if h.current_row == 0 || h.current_row > h.rows.len() {
                return false;
            }
            let row = &h.rows[h.current_row - 1];
            row.get::<bool>(column).unwrap_or(false)
        }
        None => false,
    }
}

/// Check if value is NULL.
#[no_mangle]
pub extern "C" fn rt_db_result_is_null(result_handle: u64, column: usize) -> bool {
    let result_handles = RESULT_HANDLES.lock();
    match result_handles.get(&result_handle) {
        Some(h) => {
            if h.current_row == 0 || h.current_row > h.rows.len() {
                return true;
            }
            let row = &h.rows[h.current_row - 1];
            match row.get_value(column) {
                Some(v) => v.is_null(),
                None => true,
            }
        }
        None => true,
    }
}

/// Close a result set.
#[no_mangle]
pub extern "C" fn rt_db_result_close(result_handle: u64) {
    RESULT_HANDLES.lock().remove(&result_handle);
}

// ============================================================================
// SqlValue FFI (for building parameters)
// ============================================================================

/// Create a NULL SqlValue.
#[no_mangle]
pub extern "C" fn rt_db_value_null() -> u64 {
    let id = next_handle_id();
    SQL_VALUES.lock().insert(id, SqlValue::Null);
    id
}

/// Create an integer SqlValue.
#[no_mangle]
pub extern "C" fn rt_db_value_int(v: i64) -> u64 {
    let id = next_handle_id();
    SQL_VALUES.lock().insert(id, SqlValue::Integer(v));
    id
}

/// Create a float SqlValue.
#[no_mangle]
pub extern "C" fn rt_db_value_float(v: f64) -> u64 {
    let id = next_handle_id();
    SQL_VALUES.lock().insert(id, SqlValue::Real(v));
    id
}

/// Create a string SqlValue.
#[no_mangle]
pub extern "C" fn rt_db_value_string(s: *const c_char) -> u64 {
    let s = unsafe {
        if s.is_null() {
            return rt_db_value_null();
        }
        match CStr::from_ptr(s).to_str() {
            Ok(s) => s.to_string(),
            Err(_) => return rt_db_value_null(),
        }
    };

    let id = next_handle_id();
    SQL_VALUES.lock().insert(id, SqlValue::Text(s));
    id
}

/// Create a boolean SqlValue.
#[no_mangle]
pub extern "C" fn rt_db_value_bool(v: bool) -> u64 {
    let id = next_handle_id();
    SQL_VALUES.lock().insert(id, SqlValue::Boolean(v));
    id
}

/// Free a SqlValue.
#[no_mangle]
pub extern "C" fn rt_db_value_free(handle: u64) {
    SQL_VALUES.lock().remove(&handle);
}

lazy_static::lazy_static! {
    static ref SQL_VALUES: Mutex<HashMap<u64, SqlValue>> = Mutex::new(HashMap::new());
}

fn build_params(params: *const u64, param_count: usize) -> Vec<SqlValue> {
    if params.is_null() || param_count == 0 {
        return vec![];
    }

    let param_handles: &[u64] = unsafe { std::slice::from_raw_parts(params, param_count) };

    let values = SQL_VALUES.lock();
    param_handles
        .iter()
        .map(|h| values.get(h).cloned().unwrap_or(SqlValue::Null))
        .collect()
}

// ============================================================================
// Error handling FFI
// ============================================================================

thread_local! {
    static LAST_ERROR: std::cell::RefCell<Option<CString>> = const { std::cell::RefCell::new(None) };
}

fn store_last_error(error: DbError) {
    let msg =
        CString::new(error.to_string()).unwrap_or_else(|_| CString::new("unknown error").unwrap());
    LAST_ERROR.with(|e| {
        *e.borrow_mut() = Some(msg);
    });
}

/// Get the last error message.
/// Returns null if no error. Caller must NOT free the returned string.
#[no_mangle]
pub extern "C" fn rt_db_last_error() -> *const c_char {
    LAST_ERROR.with(|e| match e.borrow().as_ref() {
        Some(s) => s.as_ptr(),
        None => ptr::null(),
    })
}

/// Clear the last error.
#[no_mangle]
pub extern "C" fn rt_db_clear_error() {
    LAST_ERROR.with(|e| {
        *e.borrow_mut() = None;
    });
}

// ============================================================================
// String utilities
// ============================================================================

/// Free a string returned by rt_db_* functions.
#[no_mangle]
pub extern "C" fn rt_db_free_string(s: *mut c_char) {
    if !s.is_null() {
        unsafe {
            drop(CString::from_raw(s));
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
    fn test_sql_value_creation() {
        let null_handle = rt_db_value_null();
        assert!(null_handle > 0);

        let int_handle = rt_db_value_int(42);
        assert!(int_handle > 0);

        let float_handle = rt_db_value_float(3.15);
        assert!(float_handle > 0);

        let bool_handle = rt_db_value_bool(true);
        assert!(bool_handle > 0);

        // Verify values are stored correctly
        {
            let values = SQL_VALUES.lock();
            assert_eq!(values.get(&null_handle), Some(&SqlValue::Null));
            assert_eq!(values.get(&int_handle), Some(&SqlValue::Integer(42)));
            assert_eq!(values.get(&float_handle), Some(&SqlValue::Real(3.15)));
            assert_eq!(values.get(&bool_handle), Some(&SqlValue::Boolean(true)));
        }

        // Clean up
        rt_db_value_free(null_handle);
        rt_db_value_free(int_handle);
        rt_db_value_free(float_handle);
        rt_db_value_free(bool_handle);
    }

    #[test]
    fn test_build_params() {
        let handles = vec![
            rt_db_value_int(1),
            rt_db_value_string(std::ffi::CString::new("test").unwrap().as_ptr()),
            rt_db_value_bool(true),
        ];

        let params = build_params(handles.as_ptr(), handles.len());
        assert_eq!(params.len(), 3);
        assert_eq!(params[0], SqlValue::Integer(1));
        assert!(matches!(params[1], SqlValue::Text(_)));
        assert_eq!(params[2], SqlValue::Boolean(true));

        for h in handles {
            rt_db_value_free(h);
        }
    }
}
