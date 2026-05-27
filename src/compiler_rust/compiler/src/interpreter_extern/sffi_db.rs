//! SFFI Fast Database Operations
//!
//! Interpreter-mode dispatch wrappers for rt_db_* fast in-memory database
//! functions. These implement the same logic as runtime_db.c but in Rust,
//! so the interpreter can call them without dlsym.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::collections::HashMap;
use std::sync::Mutex;

// ============================================================================
// Internal table storage (mirrors runtime_db.c layout)
// ============================================================================

#[derive(Clone, Debug)]
enum ColValue {
    Unset,
    Int(i64),
    Text(String),
}

#[derive(Clone, Debug)]
struct DbRow {
    pk_text: String,
    values: Vec<ColValue>,
    alive: bool,
}

struct DbTable {
    _name: String,
    num_cols: i64,
    _pk_col: i64,
    rows: Vec<DbRow>,
    alive_count: i64,
    pk_index: HashMap<String, usize>,
    scan_results: Vec<i64>,
}

static TABLES: std::sync::LazyLock<Mutex<Vec<Option<DbTable>>>> =
    std::sync::LazyLock::new(|| Mutex::new(Vec::new()));

// ============================================================================
// Helpers
// ============================================================================

fn arg_int(args: &[Value], idx: usize, fn_name: &str) -> Result<i64, CompileError> {
    args.get(idx)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("{fn_name} expects argument at index {idx}"),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_int()
}

fn arg_str(args: &[Value], idx: usize, fn_name: &str) -> Result<String, CompileError> {
    args.get(idx)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("{fn_name} expects argument at index {idx}"),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })
        .map(|v| match v {
            Value::Str(s) => s.clone(),
            Value::Int(n) => format!("{n}"),
            _ => format!("{v:?}"),
        })
}

// ============================================================================
// rt_db_table_create(name, num_cols, pk_col) -> handle
// ============================================================================

pub fn rt_db_table_create_fn(args: &[Value]) -> Result<Value, CompileError> {
    for (i, arg) in args.iter().enumerate() {
        eprintln!("[sffi_db]   arg[{}] = {:?}", i, arg);
    }
    let name = arg_str(args, 0, "rt_db_table_create")?;
    eprintln!("[sffi_db] name={}", name);
    let num_cols = arg_int(args, 1, "rt_db_table_create")?;
    eprintln!("[sffi_db] num_cols={}", num_cols);
    let pk_col = arg_int(args, 2, "rt_db_table_create")?;
    eprintln!("[sffi_db] pk_col={}", pk_col);

    if num_cols <= 0 || num_cols > 64 || pk_col < 0 || pk_col >= num_cols {
        return Ok(Value::Int(-1));
    }

    let table = DbTable {
        _name: name,
        num_cols,
        _pk_col: pk_col,
        rows: Vec::with_capacity(256),
        alive_count: 0,
        pk_index: HashMap::with_capacity(256),
        scan_results: Vec::new(),
    };

    let mut tables = TABLES.lock().unwrap();
    // Find a free slot or push new
    for (i, slot) in tables.iter_mut().enumerate() {
        if slot.is_none() {
            *slot = Some(table);
            eprintln!("[sffi_db] returning handle {}", i);
            return Ok(Value::Int(i as i64));
        }
    }
    let handle = tables.len();
    tables.push(Some(table));
    eprintln!("[sffi_db] returning handle {}", handle);
    Ok(Value::Int(handle as i64))
}

// ============================================================================
// rt_db_table_destroy(handle)
// ============================================================================

pub fn rt_db_table_destroy_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_table_destroy")? as usize;
    let mut tables = TABLES.lock().unwrap();
    if handle < tables.len() {
        tables[handle] = None;
    }
    Ok(Value::Nil)
}

// ============================================================================
// rt_db_put(table, pk_text, num_values) -> row_index
// ============================================================================

pub fn rt_db_put_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_put")? as usize;
    let pk = arg_str(args, 1, "rt_db_put")?;
    let _num_values = arg_int(args, 2, "rt_db_put")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Int(-1)),
    };

    // Check if PK already exists
    if let Some(&existing) = t.pk_index.get(&pk) {
        return Ok(Value::Int(existing as i64));
    }

    let row_idx = t.rows.len();
    let row = DbRow {
        pk_text: pk.clone(),
        values: vec![ColValue::Unset; t.num_cols as usize],
        alive: true,
    };
    t.rows.push(row);
    t.pk_index.insert(pk, row_idx);
    t.alive_count += 1;
    Ok(Value::Int(row_idx as i64))
}

// ============================================================================
// rt_db_put_value_int(table, row, col, value)
// ============================================================================

pub fn rt_db_put_value_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_put_value_int")? as usize;
    let row = arg_int(args, 1, "rt_db_put_value_int")? as usize;
    let col = arg_int(args, 2, "rt_db_put_value_int")? as usize;
    let value = arg_int(args, 3, "rt_db_put_value_int")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Nil),
    };
    if row < t.rows.len() && col < t.num_cols as usize && t.rows[row].alive {
        t.rows[row].values[col] = ColValue::Int(value);
    }
    Ok(Value::Nil)
}

// ============================================================================
// rt_db_put_value_text(table, row, col, value)
// ============================================================================

pub fn rt_db_put_value_text_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_put_value_text")? as usize;
    let row = arg_int(args, 1, "rt_db_put_value_text")? as usize;
    let col = arg_int(args, 2, "rt_db_put_value_text")? as usize;
    let value = arg_str(args, 3, "rt_db_put_value_text")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Nil),
    };
    if row < t.rows.len() && col < t.num_cols as usize && t.rows[row].alive {
        t.rows[row].values[col] = ColValue::Text(value);
    }
    Ok(Value::Nil)
}

// ============================================================================
// rt_db_get(table, pk_text) -> row_index or -1
// ============================================================================

pub fn rt_db_get_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_get")? as usize;
    let pk = arg_str(args, 1, "rt_db_get")?;

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => return Ok(Value::Int(-1)),
    };

    match t.pk_index.get(&pk) {
        Some(&idx) if idx < t.rows.len() && t.rows[idx].alive => Ok(Value::Int(idx as i64)),
        _ => Ok(Value::Int(-1)),
    }
}

// ============================================================================
// rt_db_get_int(table, row, col) -> i64
// ============================================================================

pub fn rt_db_get_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_get_int")? as usize;
    let row = arg_int(args, 1, "rt_db_get_int")? as usize;
    let col = arg_int(args, 2, "rt_db_get_int")? as usize;

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => return Ok(Value::Int(0)),
    };
    if row >= t.rows.len() || col >= t.num_cols as usize || !t.rows[row].alive {
        return Ok(Value::Int(0));
    }
    match &t.rows[row].values[col] {
        ColValue::Int(v) => Ok(Value::Int(*v)),
        _ => Ok(Value::Int(0)),
    }
}

// ============================================================================
// rt_db_get_text(table, row, col) -> text
// ============================================================================

pub fn rt_db_get_text_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_get_text")? as usize;
    let row = arg_int(args, 1, "rt_db_get_text")? as usize;
    let col = arg_int(args, 2, "rt_db_get_text")? as usize;

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => return Ok(Value::Str(String::new())),
    };
    if row >= t.rows.len() || col >= t.num_cols as usize || !t.rows[row].alive {
        return Ok(Value::Str(String::new()));
    }
    match &t.rows[row].values[col] {
        ColValue::Text(s) => Ok(Value::Str(s.clone())),
        _ => Ok(Value::Str(String::new())),
    }
}

// ============================================================================
// rt_db_scan_range(table, col, low, high) -> count
// ============================================================================

pub fn rt_db_scan_range_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_scan_range")? as usize;
    let col = arg_int(args, 1, "rt_db_scan_range")? as usize;
    let low = arg_int(args, 2, "rt_db_scan_range")?;
    let high = arg_int(args, 3, "rt_db_scan_range")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Int(0)),
    };
    if col >= t.num_cols as usize {
        return Ok(Value::Int(0));
    }

    t.scan_results.clear();
    for (i, row) in t.rows.iter().enumerate() {
        if !row.alive {
            continue;
        }
        if let ColValue::Int(v) = &row.values[col] {
            if *v >= low && *v <= high {
                t.scan_results.push(i as i64);
            }
        }
    }
    Ok(Value::Int(t.scan_results.len() as i64))
}

// ============================================================================
// rt_db_scan_result(table, result_idx) -> row_index
// ============================================================================

pub fn rt_db_scan_result_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_scan_result")? as usize;
    let result_idx = arg_int(args, 1, "rt_db_scan_result")? as usize;

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => return Ok(Value::Int(-1)),
    };
    if result_idx >= t.scan_results.len() {
        return Ok(Value::Int(-1));
    }
    Ok(Value::Int(t.scan_results[result_idx]))
}

// ============================================================================
// rt_db_delete(table, pk_text) -> 0/1
// ============================================================================

pub fn rt_db_delete_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_delete")? as usize;
    let pk = arg_str(args, 1, "rt_db_delete")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Int(0)),
    };

    if let Some(idx) = t.pk_index.remove(&pk) {
        if idx < t.rows.len() && t.rows[idx].alive {
            t.rows[idx].alive = false;
            t.alive_count -= 1;
            return Ok(Value::Int(1));
        }
    }
    Ok(Value::Int(0))
}

// ============================================================================
// rt_db_row_count(table) -> i64
// ============================================================================

pub fn rt_db_row_count_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_row_count")? as usize;

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => return Ok(Value::Int(0)),
    };
    Ok(Value::Int(t.alive_count))
}

// ============================================================================
// rt_db_col_count(table) -> i64
// ============================================================================

pub fn rt_db_col_count_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_col_count")? as usize;

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => return Ok(Value::Int(0)),
    };
    Ok(Value::Int(t.num_cols))
}
