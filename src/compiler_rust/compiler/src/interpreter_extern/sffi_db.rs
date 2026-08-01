//! SFFI Fast Database Operations
//!
//! Interpreter-mode dispatch wrappers for rt_db_* fast in-memory database
//! functions. These implement the same logic as runtime_db.c but in Rust,
//! so the interpreter can call them without dlsym.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::collections::HashMap;
use std::fs;
use std::path::Path;
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

static TABLES: std::sync::LazyLock<Mutex<Vec<Option<DbTable>>>> = std::sync::LazyLock::new(|| Mutex::new(Vec::new()));

// ============================================================================
// Minimal embedded SQLite facade for interpreter mode
// ============================================================================

#[derive(Clone, Debug)]
enum SqlValue {
    Null,
    Int(i64),
    Float(f64),
    Text(String),
}

impl SqlValue {
    fn as_text(&self) -> String {
        match self {
            SqlValue::Null => String::new(),
            SqlValue::Int(v) => v.to_string(),
            SqlValue::Float(v) => v.to_string(),
            SqlValue::Text(v) => v.clone(),
        }
    }

    fn as_int(&self) -> i64 {
        match self {
            SqlValue::Int(v) => *v,
            SqlValue::Float(v) => *v as i64,
            SqlValue::Text(v) => v.parse().unwrap_or(0),
            SqlValue::Null => 0,
        }
    }

    fn as_float(&self) -> f64 {
        match self {
            SqlValue::Float(v) => *v,
            SqlValue::Int(v) => *v as f64,
            SqlValue::Text(v) => v.parse().unwrap_or(0.0),
            SqlValue::Null => 0.0,
        }
    }

    fn type_name(&self) -> &'static str {
        match self {
            SqlValue::Null => "null",
            SqlValue::Int(_) => "integer",
            SqlValue::Float(_) => "float",
            SqlValue::Text(_) => "text",
        }
    }
}

#[derive(Clone, Debug)]
struct SqlTable {
    columns: Vec<String>,
    rows: Vec<Vec<SqlValue>>,
    next_id: i64,
}

#[derive(Clone, Debug, Default)]
struct SqlDatabase {
    tables: HashMap<String, SqlTable>,
}

#[derive(Clone, Debug)]
struct SqlConn {
    path: String,
    db: SqlDatabase,
    last_insert_rowid: i64,
    changes: i64,
    error: String,
}

#[derive(Clone, Debug)]
enum SqlStmtKind {
    Query,
    Insert {
        conn: usize,
        table: String,
        columns: Vec<String>,
        executed: bool,
    },
}

#[derive(Clone, Debug)]
struct SqlStmt {
    columns: Vec<String>,
    rows: Vec<Vec<SqlValue>>,
    cursor: usize,
    current: Option<Vec<SqlValue>>,
    binds: HashMap<usize, SqlValue>,
    kind: SqlStmtKind,
}

static SQLITE_CONNS: std::sync::LazyLock<Mutex<Vec<Option<SqlConn>>>> =
    std::sync::LazyLock::new(|| Mutex::new(Vec::new()));
static SQLITE_STMTS: std::sync::LazyLock<Mutex<Vec<Option<SqlStmt>>>> =
    std::sync::LazyLock::new(|| Mutex::new(Vec::new()));
static SQLITE_FILES: std::sync::LazyLock<Mutex<HashMap<String, SqlDatabase>>> =
    std::sync::LazyLock::new(|| Mutex::new(HashMap::new()));

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
            Value::Str(s) => s.as_ref().clone(),
            Value::Int(n) => format!("{n}"),
            _ => format!("{v:?}"),
        })
}

fn sqlite_escape(value: &str) -> String {
    value
        .replace('\\', "\\\\")
        .replace('\t', "\\t")
        .replace('\n', "\\n")
        .replace('\r', "\\r")
}

fn sqlite_unescape(value: &str) -> String {
    let mut out = String::new();
    let mut chars = value.chars();
    while let Some(ch) = chars.next() {
        if ch == '\\' {
            match chars.next() {
                Some('t') => out.push('\t'),
                Some('n') => out.push('\n'),
                Some('r') => out.push('\r'),
                Some('\\') => out.push('\\'),
                Some(other) => {
                    out.push('\\');
                    out.push(other);
                }
                None => out.push('\\'),
            }
        } else {
            out.push(ch);
        }
    }
    out
}

fn sqlite_serialize_value(value: &SqlValue) -> String {
    match value {
        SqlValue::Null => "N".to_string(),
        SqlValue::Int(v) => format!("I:{v}"),
        SqlValue::Float(v) => format!("F:{v}"),
        SqlValue::Text(v) => format!("T:{}", sqlite_escape(v)),
    }
}

fn sqlite_deserialize_value(value: &str) -> SqlValue {
    if value == "N" {
        return SqlValue::Null;
    }
    if let Some(rest) = value.strip_prefix("I:") {
        return SqlValue::Int(rest.parse().unwrap_or(0));
    }
    if let Some(rest) = value.strip_prefix("F:") {
        return SqlValue::Float(rest.parse().unwrap_or(0.0));
    }
    if let Some(rest) = value.strip_prefix("T:") {
        return SqlValue::Text(sqlite_unescape(rest));
    }
    SqlValue::Text(sqlite_unescape(value))
}

fn sqlite_load_file(path: &str) -> Option<SqlDatabase> {
    let text = fs::read_to_string(path).ok()?;
    let mut lines = text.lines();
    if lines.next() != Some("SIMPLE_SQLITE_FACADE_V1") {
        return None;
    }
    let mut db = SqlDatabase::default();
    for line in lines {
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.is_empty() {
            continue;
        }
        if parts[0] == "table" && parts.len() >= 5 {
            let name = sqlite_unescape(parts[1]);
            let next_id = parts[2].parse().unwrap_or(1);
            let col_count = parts[3].parse::<usize>().unwrap_or(0);
            let mut columns = Vec::new();
            for idx in 0..col_count {
                if let Some(col) = parts.get(4 + idx) {
                    columns.push(sqlite_unescape(col));
                }
            }
            db.tables.insert(
                name,
                SqlTable {
                    columns,
                    rows: Vec::new(),
                    next_id,
                },
            );
        } else if parts[0] == "row" && parts.len() >= 4 {
            let name = sqlite_unescape(parts[1]);
            let value_count = parts[2].parse::<usize>().unwrap_or(0);
            let mut row = Vec::new();
            for idx in 0..value_count {
                if let Some(value) = parts.get(3 + idx) {
                    row.push(sqlite_deserialize_value(value));
                }
            }
            if let Some(table) = db.tables.get_mut(&name) {
                table.rows.push(row);
            }
        }
    }
    Some(db)
}

fn sqlite_store_file(path: &str, db: &SqlDatabase) {
    if path == ":memory:" || path.is_empty() {
        return;
    }
    let mut out = String::from("SIMPLE_SQLITE_FACADE_V1\n");
    let mut names: Vec<&String> = db.tables.keys().collect();
    names.sort();
    for name in names {
        let table = &db.tables[name];
        out.push_str("table\t");
        out.push_str(&sqlite_escape(name));
        out.push('\t');
        out.push_str(&table.next_id.to_string());
        out.push('\t');
        out.push_str(&table.columns.len().to_string());
        for column in &table.columns {
            out.push('\t');
            out.push_str(&sqlite_escape(column));
        }
        out.push('\n');
        for row in &table.rows {
            out.push_str("row\t");
            out.push_str(&sqlite_escape(name));
            out.push('\t');
            out.push_str(&row.len().to_string());
            for value in row {
                out.push('\t');
                out.push_str(&sqlite_serialize_value(value));
            }
            out.push('\n');
        }
    }
    if let Some(parent) = Path::new(path).parent() {
        if !parent.as_os_str().is_empty() {
            let _ = fs::create_dir_all(parent);
        }
    }
    let _ = fs::write(path, out);
}

// ============================================================================
// rt_db_table_create(name, num_cols, pk_col) -> handle
// ============================================================================

pub fn rt_db_table_create_fn(args: &[Value]) -> Result<Value, CompileError> {
    let name = arg_str(args, 0, "rt_db_table_create")?;
    let num_cols = arg_int(args, 1, "rt_db_table_create")?;
    let pk_col = arg_int(args, 2, "rt_db_table_create")?;

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
    use std::io::Write;
    let _ = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open("/tmp/sffi_db_trace.log")
        .map(|mut f| {
            let _ = writeln!(
                f,
                "put_value_int: h={handle} row={row} col={col} val={value} args={:?}",
                args
            );
        });

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => {
            let _ = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open("/tmp/sffi_db_trace.log")
                .map(|mut f| {
                    let _ = writeln!(f, "put_value_int: table not found for handle={handle}");
                });
            return Ok(Value::Nil);
        }
    };
    if row < t.rows.len() && col < t.num_cols as usize && t.rows[row].alive {
        t.rows[row].values[col] = ColValue::Int(value);
        let _ = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open("/tmp/sffi_db_trace.log")
            .map(|mut f| {
                let _ = writeln!(f, "put_value_int: stored OK");
            });
    } else {
        let _ = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open("/tmp/sffi_db_trace.log")
            .map(|mut f| {
                let _ = writeln!(
                    f,
                    "put_value_int: bounds check failed row={row} rows_len={} col={col} num_cols={} alive={}",
                    t.rows.len(),
                    t.num_cols,
                    t.rows.get(row).map(|r| r.alive).unwrap_or(false)
                );
            });
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
    use std::io::Write;
    let _ = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open("/tmp/sffi_db_trace.log")
        .map(|mut f| {
            let _ = writeln!(f, "get_int: h={handle} row={row} col={col} args={:?}", args);
        });

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => {
            let _ = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open("/tmp/sffi_db_trace.log")
                .map(|mut f| {
                    let _ = writeln!(f, "get_int: table not found");
                });
            return Ok(Value::Int(0));
        }
    };
    if row >= t.rows.len() || col >= t.num_cols as usize || !t.rows[row].alive {
        let _ = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open("/tmp/sffi_db_trace.log")
            .map(|mut f| {
                let _ = writeln!(f, "get_int: bounds check failed");
            });
        return Ok(Value::Int(0));
    }
    let result = match &t.rows[row].values[col] {
        ColValue::Int(v) => {
            let _ = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open("/tmp/sffi_db_trace.log")
                .map(|mut f| {
                    let _ = writeln!(f, "get_int: returning {v}");
                });
            Ok(Value::Int(*v))
        }
        other => {
            let _ = std::fs::OpenOptions::new()
                .create(true)
                .append(true)
                .open("/tmp/sffi_db_trace.log")
                .map(|mut f| {
                    let _ = writeln!(f, "get_int: col value is {:?}, returning 0", other);
                });
            Ok(Value::Int(0))
        }
    };
    result
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
        None => return Ok(Value::text(String::new())),
    };
    if row >= t.rows.len() || col >= t.num_cols as usize || !t.rows[row].alive {
        return Ok(Value::text(String::new()));
    }
    match &t.rows[row].values[col] {
        ColValue::Text(s) => Ok(Value::text(s.clone())),
        _ => Ok(Value::text(String::new())),
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

// ============================================================================
// rt_db_put_row3(handle, pk, type_mask, v0, v1, v2) -> row_index
// type_mask bits: 0=int, 1=text per column (cols 0,1,2)
// ============================================================================

pub fn rt_db_put_row3_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_put_row3")? as usize;
    let pk = arg_str(args, 1, "rt_db_put_row3")?;
    let type_mask = arg_int(args, 2, "rt_db_put_row3")?;
    let v0 = arg_int(args, 3, "rt_db_put_row3")?;
    let v1 = arg_int(args, 4, "rt_db_put_row3")?;
    let v2 = arg_int(args, 5, "rt_db_put_row3")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Int(-1)),
    };
    if t.num_cols < 3 {
        return Ok(Value::Int(-1));
    }

    if let Some(&existing) = t.pk_index.get(&pk) {
        return Ok(Value::Int(existing as i64));
    }

    let row_idx = t.rows.len();
    let mut values = vec![ColValue::Unset; t.num_cols as usize];
    let vals = [v0, v1, v2];
    for i in 0..3 {
        if (type_mask >> i) & 1 == 1 {
            values[i] = ColValue::Text(format!("{}", vals[i]));
        } else {
            values[i] = ColValue::Int(vals[i]);
        }
    }
    let row = DbRow {
        pk_text: pk.clone(),
        values,
        alive: true,
    };
    t.rows.push(row);
    t.pk_index.insert(pk, row_idx);
    t.alive_count += 1;
    Ok(Value::Int(row_idx as i64))
}

// ============================================================================
// rt_db_get_int_by_pk(handle, pk, col, default_val) -> i64
// ============================================================================

pub fn rt_db_get_int_by_pk_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_get_int_by_pk")? as usize;
    let pk = arg_str(args, 1, "rt_db_get_int_by_pk")?;
    let col = arg_int(args, 2, "rt_db_get_int_by_pk")? as usize;
    let default_val = arg_int(args, 3, "rt_db_get_int_by_pk")?;

    let tables = TABLES.lock().unwrap();
    let t = match tables.get(handle).and_then(|s| s.as_ref()) {
        Some(t) => t,
        None => return Ok(Value::Int(default_val)),
    };
    match t.pk_index.get(&pk) {
        Some(&idx) if idx < t.rows.len() && t.rows[idx].alive && col < t.num_cols as usize => {
            match &t.rows[idx].values[col] {
                ColValue::Int(v) => Ok(Value::Int(*v)),
                _ => Ok(Value::Int(default_val)),
            }
        }
        _ => Ok(Value::Int(default_val)),
    }
}

// ============================================================================
// rt_db_update_int(handle, pk, col, value) -> 0/1
// ============================================================================

pub fn rt_db_update_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_update_int")? as usize;
    let pk = arg_str(args, 1, "rt_db_update_int")?;
    let col = arg_int(args, 2, "rt_db_update_int")? as usize;
    let value = arg_int(args, 3, "rt_db_update_int")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Int(0)),
    };
    match t.pk_index.get(&pk) {
        Some(&idx) if idx < t.rows.len() && t.rows[idx].alive && col < t.num_cols as usize => {
            t.rows[idx].values[col] = ColValue::Int(value);
            Ok(Value::Int(1))
        }
        _ => Ok(Value::Int(0)),
    }
}

// ============================================================================
// rt_db_update_text(handle, pk, col, value) -> 0/1
// ============================================================================

pub fn rt_db_update_text_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_update_text")? as usize;
    let pk = arg_str(args, 1, "rt_db_update_text")?;
    let col = arg_int(args, 2, "rt_db_update_text")? as usize;
    let value = arg_str(args, 3, "rt_db_update_text")?;

    let mut tables = TABLES.lock().unwrap();
    let t = match tables.get_mut(handle).and_then(|s| s.as_mut()) {
        Some(t) => t,
        None => return Ok(Value::Int(0)),
    };
    match t.pk_index.get(&pk) {
        Some(&idx) if idx < t.rows.len() && t.rows[idx].alive && col < t.num_cols as usize => {
            t.rows[idx].values[col] = ColValue::Text(value);
            Ok(Value::Int(1))
        }
        _ => Ok(Value::Int(0)),
    }
}

// ============================================================================
// Integer-PK variants — convert int to string key internally
// ============================================================================

pub fn rt_db_iput3_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_iput3")? as usize;
    let pk_int = arg_int(args, 1, "rt_db_iput3")?;
    let v0 = arg_int(args, 2, "rt_db_iput3")?;
    let v1 = arg_int(args, 3, "rt_db_iput3")?;
    let v2 = arg_int(args, 4, "rt_db_iput3")?;
    let pk = format!("{pk_int}");
    let str_args = vec![
        Value::Int(handle as i64),
        Value::text(pk),
        Value::Int(0),
        Value::Int(v0),
        Value::Int(v1),
        Value::Int(v2),
    ];
    rt_db_put_row3_fn(&str_args)
}

pub fn rt_db_iget_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_iget_int")? as usize;
    let pk_int = arg_int(args, 1, "rt_db_iget_int")?;
    let col = arg_int(args, 2, "rt_db_iget_int")?;
    let default_val = arg_int(args, 3, "rt_db_iget_int")?;
    let pk = format!("{pk_int}");
    let str_args = vec![
        Value::Int(handle as i64),
        Value::text(pk),
        Value::Int(col),
        Value::Int(default_val),
    ];
    rt_db_get_int_by_pk_fn(&str_args)
}

pub fn rt_db_iupdate_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_iupdate_int")? as usize;
    let pk_int = arg_int(args, 1, "rt_db_iupdate_int")?;
    let col = arg_int(args, 2, "rt_db_iupdate_int")?;
    let value = arg_int(args, 3, "rt_db_iupdate_int")?;
    let pk = format!("{pk_int}");
    let str_args = vec![
        Value::Int(handle as i64),
        Value::text(pk),
        Value::Int(col),
        Value::Int(value),
    ];
    rt_db_update_int_fn(&str_args)
}

pub fn rt_db_idelete_fn(args: &[Value]) -> Result<Value, CompileError> {
    let handle = arg_int(args, 0, "rt_db_idelete")? as usize;
    let pk_int = arg_int(args, 1, "rt_db_idelete")?;
    let pk = format!("{pk_int}");
    let str_args = vec![Value::Int(handle as i64), Value::text(pk)];
    rt_db_delete_fn(&str_args)
}

fn arg_float(args: &[Value], idx: usize, fn_name: &str) -> Result<f64, CompileError> {
    args.get(idx)
        .ok_or_else(|| {
            CompileError::semantic_with_context(
                format!("{fn_name} expects argument at index {idx}"),
                ErrorContext::new().with_code(codes::ARGUMENT_COUNT_MISMATCH),
            )
        })?
        .as_float()
}

fn sqlite_handle_to_index(handle: i64) -> Option<usize> {
    if handle <= 0 {
        None
    } else {
        Some((handle - 1) as usize)
    }
}

fn sqlite_alloc_conn(conn: SqlConn) -> i64 {
    let mut conns = SQLITE_CONNS.lock().unwrap();
    for (idx, slot) in conns.iter_mut().enumerate() {
        if slot.is_none() {
            *slot = Some(conn);
            return (idx + 1) as i64;
        }
    }
    conns.push(Some(conn));
    conns.len() as i64
}

fn sqlite_alloc_stmt(stmt: SqlStmt) -> i64 {
    let mut stmts = SQLITE_STMTS.lock().unwrap();
    for (idx, slot) in stmts.iter_mut().enumerate() {
        if slot.is_none() {
            *slot = Some(stmt);
            return (idx + 1) as i64;
        }
    }
    stmts.push(Some(stmt));
    stmts.len() as i64
}

fn sqlite_set_error(conn: &mut SqlConn, message: impl Into<String>) -> i64 {
    conn.error = message.into();
    conn.changes = 0;
    0
}

fn sqlite_split_statements(sql: &str) -> Vec<String> {
    sql.split(';')
        .map(str::trim)
        .filter(|part| !part.is_empty())
        .map(ToOwned::to_owned)
        .collect()
}

fn sqlite_unquote_literal(value: &str) -> String {
    let trimmed = value.trim();
    if trimmed.len() >= 2 && trimmed.starts_with('\'') && trimmed.ends_with('\'') {
        return trimmed[1..trimmed.len() - 1].replace("''", "'");
    }
    trimmed.to_string()
}

fn sqlite_parse_create(sql: &str) -> Option<(String, Vec<String>)> {
    let lower = sql.to_ascii_lowercase();
    if !lower.starts_with("create table") {
        return None;
    }
    let open = sql.find('(')?;
    let close = sql.rfind(')')?;
    let before = sql[..open].trim();
    let table = before.split_whitespace().last()?.trim_matches('"').to_string();
    let columns = sql[open + 1..close]
        .split(',')
        .filter_map(|part| part.split_whitespace().next())
        .map(|name| name.trim_matches('"').to_string())
        .filter(|name| !name.is_empty())
        .collect::<Vec<_>>();
    Some((table, columns))
}

fn sqlite_parse_insert(sql: &str) -> Option<(String, Vec<String>)> {
    let lower = sql.to_ascii_lowercase();
    if !lower.starts_with("insert into ") {
        return None;
    }
    let open = sql.find('(')?;
    let close = sql[open + 1..].find(')')? + open + 1;
    let table = sql["INSERT INTO ".len()..open].trim().to_string();
    let columns = sql[open + 1..close]
        .split(',')
        .map(|part| part.trim().to_string())
        .filter(|name| !name.is_empty())
        .collect::<Vec<_>>();
    Some((table, columns))
}

fn sqlite_like(value: &str, pattern: &str) -> bool {
    if pattern == "%" {
        return true;
    }
    let needle = pattern.trim_matches('%');
    if pattern.starts_with('%') && pattern.ends_with('%') {
        value.contains(needle)
    } else if pattern.starts_with('%') {
        value.ends_with(needle)
    } else if pattern.ends_with('%') {
        value.starts_with(needle)
    } else {
        value == needle
    }
}

fn sqlite_execute_statement(conn: &mut SqlConn, sql: &str) -> i64 {
    let lower = sql.to_ascii_lowercase();
    conn.error.clear();
    if let Some((table_name, columns)) = sqlite_parse_create(sql) {
        conn.db.tables.entry(table_name.clone()).or_insert(SqlTable {
            columns,
            rows: Vec::new(),
            next_id: 1,
        });
        conn.changes = 0;
        return 1;
    }
    if lower.starts_with("delete from ") {
        let table_name = sql["DELETE FROM ".len()..].split_whitespace().next().unwrap_or("");
        if let Some(table) = conn.db.tables.get_mut(table_name) {
            conn.changes = table.rows.len() as i64;
            table.rows.clear();
            table.next_id = 1;
            return 1;
        }
        return sqlite_set_error(conn, format!("table not found: {table_name}"));
    }
    if let Some((table, columns)) = sqlite_parse_insert(sql) {
        let values_part = lower
            .find("values")
            .and_then(|idx| sql[idx..].find('(').map(|open| idx + open + 1));
        let values_end = sql.rfind(')');
        if let (Some(start), Some(end)) = (values_part, values_end) {
            let values = sql[start..end]
                .split(',')
                .map(|part| SqlValue::Text(sqlite_unquote_literal(part)))
                .collect::<Vec<_>>();
            return sqlite_insert_row(conn, &table, &columns, &values);
        }
    }
    sqlite_set_error(conn, format!("unsupported SQL: {sql}"))
}

fn sqlite_insert_row(conn: &mut SqlConn, table_name: &str, columns: &[String], values: &[SqlValue]) -> i64 {
    let table = match conn.db.tables.get_mut(table_name) {
        Some(table) => table,
        None => {
            conn.error = format!("table not found: {table_name}");
            conn.changes = 0;
            return 0;
        }
    };
    let mut row = vec![SqlValue::Null; table.columns.len()];
    if let Some(id_idx) = table.columns.iter().position(|name| name == "id") {
        row[id_idx] = SqlValue::Int(table.next_id);
    }
    for (idx, column) in columns.iter().enumerate() {
        if let Some(col_idx) = table.columns.iter().position(|name| name == column) {
            row[col_idx] = values.get(idx).cloned().unwrap_or(SqlValue::Null);
        }
    }
    conn.last_insert_rowid = table.next_id;
    table.next_id += 1;
    table.rows.push(row);
    conn.changes = 1;
    conn.error.clear();
    1
}

fn sqlite_select_rows(db: &SqlDatabase, sql: &str) -> Option<(Vec<String>, Vec<Vec<SqlValue>>)> {
    let lower = sql.to_ascii_lowercase();
    if lower.starts_with("select count(*) from sqlite_master") {
        let needle = "name=";
        let name = lower
            .find(needle)
            .map(|idx| sqlite_unquote_literal(&sql[idx + needle.len()..]))
            .unwrap_or_default();
        let exists = db.tables.contains_key(&name);
        return Some((
            vec!["COUNT(*)".to_string()],
            vec![vec![SqlValue::Int(if exists { 1 } else { 0 })]],
        ));
    }
    if lower.starts_with("select count(*) from ") {
        let table_name = sql["SELECT COUNT(*) FROM ".len()..]
            .split_whitespace()
            .next()
            .unwrap_or("");
        let count = db.tables.get(table_name).map(|table| table.rows.len()).unwrap_or(0);
        return Some((vec!["COUNT(*)".to_string()], vec![vec![SqlValue::Int(count as i64)]]));
    }
    if !lower.starts_with("select ") {
        return None;
    }
    let from_idx = lower.find(" from ")?;
    let cols_part = &sql["SELECT ".len()..from_idx];
    let after_from = &sql[from_idx + " from ".len()..];
    let table_name = after_from.split_whitespace().next()?;
    let table = db.tables.get(table_name)?;
    let columns = cols_part
        .split(',')
        .map(|part| part.trim().to_string())
        .collect::<Vec<_>>();
    let selected_indices = columns
        .iter()
        .filter_map(|name| table.columns.iter().position(|col| col == name))
        .collect::<Vec<_>>();
    let like_pattern = if let Some(where_idx) = lower.find(" where ") {
        let where_part = &sql[where_idx..];
        where_part
            .find("LIKE")
            .or_else(|| where_part.find("like"))
            .and_then(|idx| {
                let after = &where_part[idx + "LIKE".len()..];
                Some(sqlite_unquote_literal(after.split(" OR ").next().unwrap_or(after)))
            })
    } else {
        None
    };
    let mut rows = Vec::new();
    for row in &table.rows {
        if let Some(pattern) = &like_pattern {
            let matches = row.iter().any(|value| sqlite_like(&value.as_text(), pattern));
            if !matches {
                continue;
            }
        }
        rows.push(selected_indices.iter().map(|idx| row[*idx].clone()).collect());
    }
    Some((columns, rows))
}

pub fn rt_sqlite_open_fn(args: &[Value]) -> Result<Value, CompileError> {
    let path = arg_str(args, 0, "rt_sqlite_open")?;
    let db = SQLITE_FILES
        .lock()
        .unwrap()
        .get(&path)
        .cloned()
        .or_else(|| sqlite_load_file(&path))
        .unwrap_or_default();
    Ok(Value::Int(sqlite_alloc_conn(SqlConn {
        path,
        db,
        last_insert_rowid: 0,
        changes: 0,
        error: String::new(),
    })))
}

pub fn rt_sqlite_open_memory_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(sqlite_alloc_conn(SqlConn {
        path: ":memory:".to_string(),
        db: SqlDatabase::default(),
        last_insert_rowid: 0,
        changes: 0,
        error: String::new(),
    })))
}

pub fn rt_sqlite_close_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_close")?) else {
        return Ok(Value::Int(0));
    };
    let mut conns = SQLITE_CONNS.lock().unwrap();
    if let Some(Some(conn)) = conns.get(idx) {
        if conn.path != ":memory:" {
            SQLITE_FILES.lock().unwrap().insert(conn.path.clone(), conn.db.clone());
            sqlite_store_file(&conn.path, &conn.db);
        }
    }
    if idx < conns.len() {
        conns[idx] = None;
        return Ok(Value::Int(1));
    }
    Ok(Value::Int(0))
}

pub fn rt_sqlite_execute_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_execute")?) else {
        return Ok(Value::Int(0));
    };
    let sql = arg_str(args, 1, "rt_sqlite_execute")?;
    let mut conns = SQLITE_CONNS.lock().unwrap();
    let Some(Some(conn)) = conns.get_mut(idx) else {
        return Ok(Value::Int(0));
    };
    Ok(Value::Int(sqlite_execute_statement(conn, &sql)))
}

pub fn rt_sqlite_execute_batch_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_execute_batch")?) else {
        return Ok(Value::Int(0));
    };
    let sql = arg_str(args, 1, "rt_sqlite_execute_batch")?;
    let mut conns = SQLITE_CONNS.lock().unwrap();
    let Some(Some(conn)) = conns.get_mut(idx) else {
        return Ok(Value::Int(0));
    };
    for statement in sqlite_split_statements(&sql) {
        if sqlite_execute_statement(conn, &statement) != 1 {
            return Ok(Value::Int(0));
        }
    }
    Ok(Value::Int(1))
}

pub fn rt_sqlite_query_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_query")?) else {
        return Ok(Value::Int(0));
    };
    let sql = arg_str(args, 1, "rt_sqlite_query")?;
    let conns = SQLITE_CONNS.lock().unwrap();
    let Some(Some(conn)) = conns.get(idx) else {
        return Ok(Value::Int(0));
    };
    let Some((columns, rows)) = sqlite_select_rows(&conn.db, &sql) else {
        return Ok(Value::Int(0));
    };
    Ok(Value::Int(sqlite_alloc_stmt(SqlStmt {
        columns,
        rows,
        cursor: 0,
        current: None,
        binds: HashMap::new(),
        kind: SqlStmtKind::Query,
    })))
}

pub fn rt_sqlite_prepare_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(conn_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_prepare")?) else {
        return Ok(Value::Int(0));
    };
    let sql = arg_str(args, 1, "rt_sqlite_prepare")?;
    let Some((table, columns)) = sqlite_parse_insert(&sql) else {
        return Ok(Value::Int(0));
    };
    Ok(Value::Int(sqlite_alloc_stmt(SqlStmt {
        columns: Vec::new(),
        rows: Vec::new(),
        cursor: 0,
        current: None,
        binds: HashMap::new(),
        kind: SqlStmtKind::Insert {
            conn: conn_idx,
            table,
            columns,
            executed: false,
        },
    })))
}

pub fn rt_sqlite_query_next_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_query_next")?) else {
        return Ok(Value::Int(0));
    };
    let mut stmts = SQLITE_STMTS.lock().unwrap();
    let Some(Some(stmt)) = stmts.get_mut(stmt_idx) else {
        return Ok(Value::Int(0));
    };
    match &mut stmt.kind {
        SqlStmtKind::Query => {
            if stmt.cursor >= stmt.rows.len() {
                stmt.current = None;
                Ok(Value::Int(0))
            } else {
                stmt.current = Some(stmt.rows[stmt.cursor].clone());
                stmt.cursor += 1;
                Ok(Value::Int(1))
            }
        }
        SqlStmtKind::Insert {
            conn,
            table,
            columns,
            executed,
        } => {
            if *executed {
                return Ok(Value::Int(0));
            }
            let values = (1..=columns.len())
                .map(|idx| stmt.binds.get(&idx).cloned().unwrap_or(SqlValue::Null))
                .collect::<Vec<_>>();
            let mut conns = SQLITE_CONNS.lock().unwrap();
            let Some(Some(conn)) = conns.get_mut(*conn) else {
                return Ok(Value::Int(0));
            };
            *executed = true;
            Ok(Value::Int(sqlite_insert_row(conn, table, columns, &values)))
        }
    }
}

pub fn rt_sqlite_query_done_fn(args: &[Value]) -> Result<Value, CompileError> {
    rt_sqlite_finalize_fn(args)
}

pub fn rt_sqlite_column_count_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_column_count")?) else {
        return Ok(Value::Int(0));
    };
    let stmts = SQLITE_STMTS.lock().unwrap();
    let count = stmts
        .get(idx)
        .and_then(|slot| slot.as_ref())
        .map(|stmt| stmt.columns.len())
        .unwrap_or(0);
    Ok(Value::Int(count as i64))
}

pub fn rt_sqlite_column_name_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_column_name")?) else {
        return Ok(Value::text(String::new()));
    };
    let col_idx = arg_int(args, 1, "rt_sqlite_column_name")? as usize;
    let stmts = SQLITE_STMTS.lock().unwrap();
    let value = stmts
        .get(stmt_idx)
        .and_then(|slot| slot.as_ref())
        .and_then(|stmt| stmt.columns.get(col_idx))
        .cloned()
        .unwrap_or_default();
    Ok(Value::text(value))
}

fn sqlite_column_value(stmt: &SqlStmt, idx: usize) -> SqlValue {
    stmt.current
        .as_ref()
        .and_then(|row| row.get(idx))
        .cloned()
        .unwrap_or(SqlValue::Null)
}

pub fn rt_sqlite_column_text_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_column_text")?) else {
        return Ok(Value::text(String::new()));
    };
    let col_idx = arg_int(args, 1, "rt_sqlite_column_text")? as usize;
    let stmts = SQLITE_STMTS.lock().unwrap();
    let value = stmts
        .get(stmt_idx)
        .and_then(|slot| slot.as_ref())
        .map(|stmt| sqlite_column_value(stmt, col_idx).as_text())
        .unwrap_or_default();
    Ok(Value::text(value))
}

pub fn rt_sqlite_column_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_column_int")?) else {
        return Ok(Value::Int(0));
    };
    let col_idx = arg_int(args, 1, "rt_sqlite_column_int")? as usize;
    let stmts = SQLITE_STMTS.lock().unwrap();
    let value = stmts
        .get(stmt_idx)
        .and_then(|slot| slot.as_ref())
        .map(|stmt| sqlite_column_value(stmt, col_idx).as_int())
        .unwrap_or(0);
    Ok(Value::Int(value))
}

pub fn rt_sqlite_column_float_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_column_float")?) else {
        return Ok(Value::Float(0.0));
    };
    let col_idx = arg_int(args, 1, "rt_sqlite_column_float")? as usize;
    let stmts = SQLITE_STMTS.lock().unwrap();
    let value = stmts
        .get(stmt_idx)
        .and_then(|slot| slot.as_ref())
        .map(|stmt| sqlite_column_value(stmt, col_idx).as_float())
        .unwrap_or(0.0);
    Ok(Value::Float(value))
}

pub fn rt_sqlite_column_type_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_column_type")?) else {
        return Ok(Value::text("null".to_string()));
    };
    let col_idx = arg_int(args, 1, "rt_sqlite_column_type")? as usize;
    let stmts = SQLITE_STMTS.lock().unwrap();
    let value = stmts
        .get(stmt_idx)
        .and_then(|slot| slot.as_ref())
        .map(|stmt| sqlite_column_value(stmt, col_idx).type_name().to_string())
        .unwrap_or_else(|| "null".to_string());
    Ok(Value::text(value))
}

pub fn rt_sqlite_bind_text_fn(args: &[Value]) -> Result<Value, CompileError> {
    sqlite_bind(
        args,
        "rt_sqlite_bind_text",
        SqlValue::Text(arg_str(args, 2, "rt_sqlite_bind_text")?),
    )
}

pub fn rt_sqlite_bind_int_fn(args: &[Value]) -> Result<Value, CompileError> {
    sqlite_bind(
        args,
        "rt_sqlite_bind_int",
        SqlValue::Int(arg_int(args, 2, "rt_sqlite_bind_int")?),
    )
}

pub fn rt_sqlite_bind_float_fn(args: &[Value]) -> Result<Value, CompileError> {
    sqlite_bind(
        args,
        "rt_sqlite_bind_float",
        SqlValue::Float(arg_float(args, 2, "rt_sqlite_bind_float")?),
    )
}

pub fn rt_sqlite_bind_null_fn(args: &[Value]) -> Result<Value, CompileError> {
    sqlite_bind(args, "rt_sqlite_bind_null", SqlValue::Null)
}

fn sqlite_bind(args: &[Value], fn_name: &str, value: SqlValue) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, fn_name)?) else {
        return Ok(Value::Int(0));
    };
    let bind_idx = arg_int(args, 1, fn_name)? as usize;
    let mut stmts = SQLITE_STMTS.lock().unwrap();
    let Some(Some(stmt)) = stmts.get_mut(stmt_idx) else {
        return Ok(Value::Int(0));
    };
    stmt.binds.insert(bind_idx, value);
    Ok(Value::Int(1))
}

pub fn rt_sqlite_reset_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_reset")?) else {
        return Ok(Value::Int(0));
    };
    let mut stmts = SQLITE_STMTS.lock().unwrap();
    let Some(Some(stmt)) = stmts.get_mut(stmt_idx) else {
        return Ok(Value::Int(0));
    };
    stmt.cursor = 0;
    stmt.current = None;
    if let SqlStmtKind::Insert { executed, .. } = &mut stmt.kind {
        *executed = false;
    }
    Ok(Value::Int(1))
}

pub fn rt_sqlite_finalize_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(stmt_idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_finalize")?) else {
        return Ok(Value::Nil);
    };
    let mut stmts = SQLITE_STMTS.lock().unwrap();
    if stmt_idx < stmts.len() {
        stmts[stmt_idx] = None;
    }
    Ok(Value::Nil)
}

pub fn rt_sqlite_begin_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1))
}

pub fn rt_sqlite_commit_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1))
}

pub fn rt_sqlite_rollback_fn(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1))
}

pub fn rt_sqlite_last_insert_rowid_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_last_insert_rowid")?) else {
        return Ok(Value::Int(0));
    };
    let conns = SQLITE_CONNS.lock().unwrap();
    let value = conns
        .get(idx)
        .and_then(|slot| slot.as_ref())
        .map(|conn| conn.last_insert_rowid)
        .unwrap_or(0);
    Ok(Value::Int(value))
}

pub fn rt_sqlite_changes_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_changes")?) else {
        return Ok(Value::Int(0));
    };
    let conns = SQLITE_CONNS.lock().unwrap();
    let value = conns
        .get(idx)
        .and_then(|slot| slot.as_ref())
        .map(|conn| conn.changes)
        .unwrap_or(0);
    Ok(Value::Int(value))
}

pub fn rt_sqlite_error_message_fn(args: &[Value]) -> Result<Value, CompileError> {
    let Some(idx) = sqlite_handle_to_index(arg_int(args, 0, "rt_sqlite_error_message")?) else {
        return Ok(Value::text("Invalid connection".to_string()));
    };
    let conns = SQLITE_CONNS.lock().unwrap();
    let value = conns
        .get(idx)
        .and_then(|slot| slot.as_ref())
        .map(|conn| conn.error.clone())
        .unwrap_or_default();
    Ok(Value::text(value))
}
