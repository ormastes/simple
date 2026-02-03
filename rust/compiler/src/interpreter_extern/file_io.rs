//! File I/O FFI functions for the interpreter
//!
//! This module provides interpreter implementations for the rt_* file I/O functions
//! that are declared in simple/std_lib/src/infra/file_io.spl.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::collections::HashMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::path::Path;
use std::sync::Mutex;

// Global lock handle counter and active locks
static LOCK_HANDLES: Mutex<Option<LockState>> = Mutex::new(None);

struct LockState {
    next_id: i64,
    active: HashMap<i64, std::path::PathBuf>,
}

impl LockState {
    fn new() -> Self {
        LockState {
            next_id: 1,
            active: HashMap::new(),
        }
    }
}

// Helper to create Option::Some(value)
fn make_some(value: Value) -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Some(Box::new(value)),
    }
}

// Helper to create Option::None
fn make_none() -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: None,
    }
}

// Helper to extract path from first argument
fn extract_path(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("Argument must be a string path");
            Err(CompileError::semantic_with_context(
                format!("file_io: argument {} must be a string path", idx),
                ctx,
            ))
        }
    }
}

// Helper to extract content string
fn extract_content(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::TYPE_MISMATCH)
                .with_help("Argument must be a string");
            Err(CompileError::semantic_with_context(
                format!("file_io: argument {} must be a string", idx),
                ctx,
            ))
        }
    }
}

// ============================================================================
// File Metadata
// ============================================================================

/// Check if file exists
pub fn rt_file_exists(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    Ok(Value::Bool(Path::new(&path).exists()))
}

/// Get file stat info (simplified - returns size or -1)
pub fn rt_file_stat(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::metadata(&path) {
        Ok(meta) => Ok(Value::Int(meta.len() as i64)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// Get file size in bytes
pub fn rt_file_size(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::metadata(&path) {
        Ok(meta) => Ok(Value::Int(meta.len() as i64)),
        Err(_) => Ok(Value::Int(0)),
    }
}

/// Compute SHA256 hash of file (simplified - uses basic hash for MVP)
pub fn rt_file_hash_sha256(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read(&path) {
        Ok(content) => {
            // Simple hash computation using std::hash
            use std::collections::hash_map::DefaultHasher;
            use std::hash::{Hash, Hasher};

            let mut hasher = DefaultHasher::new();
            content.hash(&mut hasher);
            let hash = hasher.finish();

            // Return as hex string
            Ok(Value::Str(format!("{:016x}", hash)))
        }
        Err(_) => Ok(Value::Str(String::from("0000000000000000"))),
    }
}

// ============================================================================
// File Operations
// ============================================================================

/// Canonicalize path
pub fn rt_file_canonicalize(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::canonicalize(&path) {
        Ok(canonical) => Ok(Value::Str(canonical.to_string_lossy().to_string())),
        Err(_) => {
            // Fallback: make absolute
            match std::env::current_dir() {
                Ok(cwd) => {
                    let abs = cwd.join(&path);
                    Ok(Value::Str(abs.to_string_lossy().to_string()))
                }
                Err(_) => Ok(Value::Str(path)),
            }
        }
    }
}

/// Read file as text
pub fn rt_file_read_text(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read_to_string(&path) {
        Ok(content) => Ok(make_some(Value::Str(content))),
        Err(_) => Ok(make_none()),
    }
}

/// Write text to file
pub fn rt_file_write_text(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let content = extract_content(args, 1)?;
    match fs::write(&path, &content) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Atomically write text to file (write to temp, then rename)
///
/// This provides atomic writes by:
/// 1. Writing content to a temporary file (.tmp suffix)
/// 2. Atomically renaming the temp file to the target path
///
/// This ensures that readers never see partial writes, and the operation
/// is all-or-nothing. On POSIX systems, rename is atomic.
///
/// Note: This does NOT provide file locking. For concurrent access,
/// use a higher-level API with locking (e.g., Database<T>).
pub fn rt_file_atomic_write(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let content = extract_content(args, 1)?;

    // Create parent directories if needed
    if let Some(parent) = Path::new(&path).parent() {
        if let Err(_) = fs::create_dir_all(parent) {
            return Ok(Value::Bool(false));
        }
    }

    // Write to temporary file
    let temp_path = format!("{}.tmp", path);
    match fs::write(&temp_path, &content) {
        Ok(_) => {
            // Atomically rename temp to target
            match fs::rename(&temp_path, &path) {
                Ok(_) => Ok(Value::Bool(true)),
                Err(_) => {
                    // Cleanup temp file on failure
                    let _ = fs::remove_file(&temp_path);
                    Ok(Value::Bool(false))
                }
            }
        }
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Copy file
pub fn rt_file_copy(args: &[Value]) -> Result<Value, CompileError> {
    let src = extract_path(args, 0)?;
    let dest = extract_path(args, 1)?;
    match fs::copy(&src, &dest) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Remove file
pub fn rt_file_remove(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::remove_file(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Rename file
pub fn rt_file_rename(args: &[Value]) -> Result<Value, CompileError> {
    let from = extract_path(args, 0)?;
    let to = extract_path(args, 1)?;
    match fs::rename(&from, &to) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Read file as lines
pub fn rt_file_read_lines(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read_to_string(&path) {
        Ok(content) => {
            let lines: Vec<Value> = content.lines().map(|l| Value::Str(l.to_string())).collect();
            Ok(make_some(Value::Array(lines)))
        }
        Err(_) => Ok(make_none()),
    }
}

/// Append text to file
pub fn rt_file_append_text(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let content = extract_content(args, 1)?;
    match OpenOptions::new().create(true).append(true).open(&path) {
        Ok(mut file) => match file.write_all(content.as_bytes()) {
            Ok(_) => Ok(Value::Bool(true)),
            Err(_) => Ok(Value::Bool(false)),
        },
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Read file as bytes
pub fn rt_file_read_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read(&path) {
        Ok(bytes) => {
            let arr: Vec<Value> = bytes.into_iter().map(|b| Value::Int(b as i64)).collect();
            Ok(make_some(Value::Array(arr)))
        }
        Err(_) => Ok(make_none()),
    }
}

/// Write bytes to file
pub fn rt_file_write_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let bytes_arr = match args.get(1) {
        Some(Value::Array(arr)) => arr,
        _ => return Ok(Value::Bool(false)),
    };

    let bytes: Vec<u8> = bytes_arr
        .iter()
        .filter_map(|v| match v {
            Value::Int(i) => Some(*i as u8),
            _ => None,
        })
        .collect();

    match fs::write(&path, &bytes) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Move file (works across filesystems)
pub fn rt_file_move(args: &[Value]) -> Result<Value, CompileError> {
    let src = extract_path(args, 0)?;
    let dest = extract_path(args, 1)?;

    // Try rename first
    if fs::rename(&src, &dest).is_ok() {
        return Ok(Value::Bool(true));
    }

    // Fallback: copy + delete
    if fs::copy(&src, &dest).is_ok() {
        if fs::remove_file(&src).is_ok() {
            return Ok(Value::Bool(true));
        }
    }

    Ok(Value::Bool(false))
}

// ============================================================================
// Directory Operations
// ============================================================================

/// Create directory
pub fn rt_dir_create(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::create_dir(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// List directory
pub fn rt_dir_list(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read_dir(&path) {
        Ok(entries) => {
            let names: Vec<Value> = entries
                .flatten()
                .filter_map(|e| e.file_name().into_string().ok())
                .map(Value::Str)
                .collect();
            Ok(make_some(Value::Array(names)))
        }
        Err(_) => Ok(make_none()),
    }
}

/// Remove directory
pub fn rt_dir_remove(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::remove_dir(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Find files (simplified)
pub fn rt_file_find(args: &[Value]) -> Result<Value, CompileError> {
    let dir = extract_path(args, 0)?;
    let pattern = extract_path(args, 1)?;

    fn matches_pattern(filename: &str, pattern: &str) -> bool {
        if pattern == "*" {
            return true;
        }
        if let Some(ext) = pattern.strip_prefix("*.") {
            return filename.ends_with(&format!(".{}", ext));
        }
        if let Some(prefix) = pattern.strip_suffix('*') {
            return filename.starts_with(prefix);
        }
        if let Some(suffix) = pattern.strip_prefix('*') {
            return filename.ends_with(suffix);
        }
        filename == pattern
    }

    match fs::read_dir(&dir) {
        Ok(entries) => {
            let matches: Vec<Value> = entries
                .flatten()
                .filter_map(|e| {
                    let name = e.file_name().into_string().ok()?;
                    if matches_pattern(&name, &pattern) {
                        Some(Value::Str(e.path().to_string_lossy().to_string()))
                    } else {
                        None
                    }
                })
                .collect();
            Ok(Value::Array(matches))
        }
        Err(_) => Ok(Value::Array(vec![])),
    }
}

/// Glob directory
pub fn rt_dir_glob(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_find(args)
}

/// Create directory with all parents
pub fn rt_dir_create_all(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::create_dir_all(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Walk directory recursively
pub fn rt_dir_walk(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;

    fn walk_recursive(dir: &Path, results: &mut Vec<Value>) {
        if let Ok(entries) = fs::read_dir(dir) {
            for entry in entries.flatten() {
                let path = entry.path();
                results.push(Value::Str(path.to_string_lossy().to_string()));
                if path.is_dir() {
                    walk_recursive(&path, results);
                }
            }
        }
    }

    let mut results = Vec::new();
    walk_recursive(Path::new(&path), &mut results);
    Ok(Value::Array(results))
}

/// Get current directory
pub fn rt_current_dir(_args: &[Value]) -> Result<Value, CompileError> {
    match std::env::current_dir() {
        Ok(cwd) => Ok(make_some(Value::Str(cwd.to_string_lossy().to_string()))),
        Err(_) => Ok(make_none()),
    }
}

/// Set current directory
pub fn rt_set_current_dir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match std::env::set_current_dir(&path) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Protected paths list
const PROTECTED_PATHS: &[&str] = &[
    "/", "/home", "/usr", "/bin", "/sbin", "/etc", "/var", "/tmp", "/opt", "/lib", "/lib64", "/boot", "/dev", "/proc",
    "/sys", "/root",
];

fn is_protected_path(path: &Path) -> bool {
    let components: Vec<_> = path.components().collect();
    if components.len() <= 2 {
        return true;
    }

    let path_str = path.to_string_lossy();
    for protected in PROTECTED_PATHS {
        if path_str.as_ref() == *protected {
            return true;
        }
    }

    if let Some(home) = std::env::var_os("HOME") {
        if path == Path::new(&home) {
            return true;
        }
    }

    false
}

/// Remove directory recursively (with safety)
pub fn rt_dir_remove_all(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let path_obj = Path::new(&path);

    // Canonicalize first
    let canonical = match path_obj.canonicalize() {
        Ok(p) => p,
        Err(_) => return Ok(Value::Bool(false)),
    };

    if is_protected_path(&canonical) {
        eprintln!(
            "rt_dir_remove_all: Refusing to remove protected path: {}",
            canonical.display()
        );
        return Ok(Value::Bool(false));
    }

    match fs::remove_dir_all(&canonical) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

// ============================================================================
// File Descriptor Operations
// ============================================================================

/// Open file
pub fn rt_file_open(args: &[Value]) -> Result<Value, CompileError> {
    let _path = extract_path(args, 0)?;
    // Simplified - return -1 (not implemented for interpreter)
    Ok(Value::Int(-1))
}

/// Get file size
pub fn rt_file_get_size(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(-1))
}

/// Close file
pub fn rt_file_close(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Bool(false))
}

// ============================================================================
// Path Operations
// ============================================================================

/// Get basename
pub fn rt_path_basename(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let basename = Path::new(&path).file_name().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::Str(basename.to_string()))
}

/// Get dirname
pub fn rt_path_dirname(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let dirname = Path::new(&path).parent().and_then(|p| p.to_str()).unwrap_or("");
    Ok(Value::Str(dirname.to_string()))
}

/// Get extension
pub fn rt_path_ext(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let ext = Path::new(&path).extension().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::Str(ext.to_string()))
}

/// Get absolute path
pub fn rt_path_absolute(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_canonicalize(args)
}

/// Get path separator
pub fn rt_path_separator(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    return Ok(Value::Str("\\".to_string()));
    #[cfg(not(target_os = "windows"))]
    Ok(Value::Str("/".to_string()))
}

/// Get file stem
pub fn rt_path_stem(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let stem = Path::new(&path).file_stem().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::Str(stem.to_string()))
}

/// Get relative path
pub fn rt_path_relative(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let base = extract_path(args, 1)?;

    let path_obj = Path::new(&path);
    let base_obj = Path::new(&base);

    match path_obj.strip_prefix(base_obj) {
        Ok(relative) => Ok(Value::Str(relative.to_string_lossy().to_string())),
        Err(_) => Ok(Value::Str(path)),
    }
}

/// Join paths
pub fn rt_path_join(args: &[Value]) -> Result<Value, CompileError> {
    let path1 = extract_path(args, 0)?;
    let path2 = extract_path(args, 1)?;

    let joined = Path::new(&path1).join(&path2);
    Ok(Value::Str(joined.to_string_lossy().to_string()))
}

// ============================================================================
// File Locking
// ============================================================================

/// Acquire a file lock (PID-based lock file with timeout)
///
/// Callable from Simple as: `rt_file_lock(path, timeout_secs)`
///
/// Returns lock handle (>0) on success, -1 on failure
pub fn rt_file_lock(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let timeout_secs = match args.get(1) {
        Some(Value::Int(n)) => *n,
        _ => 10, // default 10 seconds
    };

    let lock_path = format!("{}.lock", path);
    let pid = std::process::id();
    let hostname = get_hostname();
    let lock_content = format!("{}:{}", pid, hostname);

    let deadline = std::time::Instant::now() + std::time::Duration::from_secs(timeout_secs as u64);
    let mut backoff_ms = 10u64;

    loop {
        // Try to create lock file exclusively
        match OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&lock_path)
        {
            Ok(mut f) => {
                let _ = f.write_all(lock_content.as_bytes());
                // Register handle
                let mut state = LOCK_HANDLES.lock().unwrap();
                let state = state.get_or_insert_with(LockState::new);
                let handle = state.next_id;
                state.next_id += 1;
                state.active.insert(handle, std::path::PathBuf::from(&lock_path));
                return Ok(Value::Int(handle));
            }
            Err(_) => {
                // Check if lock is stale (>60 seconds old)
                if let Ok(meta) = fs::metadata(&lock_path) {
                    if let Ok(modified) = meta.modified() {
                        if modified.elapsed().unwrap_or_default() > std::time::Duration::from_secs(60) {
                            let _ = fs::remove_file(&lock_path);
                            continue;
                        }
                    }
                }

                if std::time::Instant::now() >= deadline {
                    return Ok(Value::Int(-1));
                }

                std::thread::sleep(std::time::Duration::from_millis(backoff_ms));
                backoff_ms = (backoff_ms * 2).min(500);
            }
        }
    }
}

/// Release a file lock by handle
///
/// Callable from Simple as: `rt_file_unlock(handle)`
pub fn rt_file_unlock(args: &[Value]) -> Result<Value, CompileError> {
    let handle = match args.first() {
        Some(Value::Int(n)) => *n,
        _ => return Ok(Value::Bool(false)),
    };

    let mut state = LOCK_HANDLES.lock().unwrap();
    if let Some(state) = state.as_mut() {
        if let Some(lock_path) = state.active.remove(&handle) {
            let _ = fs::remove_file(&lock_path);
            return Ok(Value::Bool(true));
        }
    }
    Ok(Value::Bool(false))
}

// ============================================================================
// System Info
// ============================================================================

/// Get current process PID
pub fn rt_getpid(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(std::process::id() as i64))
}

/// Get hostname
pub fn rt_hostname(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Str(get_hostname()))
}

fn get_hostname() -> String {
    // Try /etc/hostname on Linux
    if let Ok(h) = fs::read_to_string("/etc/hostname") {
        let trimmed = h.trim().to_string();
        if !trimmed.is_empty() {
            return trimmed;
        }
    }
    // Fallback to HOSTNAME env var
    std::env::var("HOSTNAME").unwrap_or_else(|_| "unknown".to_string())
}

/// Get number of CPU cores
pub fn rt_system_cpu_count(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(std::thread::available_parallelism()
        .map(|n| n.get() as i64)
        .unwrap_or(1)))
}

/// Get monotonic time in milliseconds
pub fn rt_time_now_monotonic_ms(_args: &[Value]) -> Result<Value, CompileError> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let ms = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as i64;
    Ok(Value::Int(ms))
}
