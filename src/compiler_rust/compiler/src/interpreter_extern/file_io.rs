//! File I/O SFFI functions for the interpreter
//!
//! This module provides interpreter implementations for the rt_* file I/O functions
//! that are declared in simple/std_lib/src/infra/file_io.spl.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Value;
use std::collections::HashMap;
use std::fs::{self, OpenOptions};
use std::io::{Read, Seek, SeekFrom, Write};
use std::path::Path;
use std::sync::{LazyLock, Mutex};

// Global lock handle counter and active locks
static LOCK_HANDLES: Mutex<Option<LockState>> = Mutex::new(None);
static SYMBOL_INTERNER: LazyLock<Mutex<SymbolInterner>> = LazyLock::new(|| Mutex::new(SymbolInterner::new()));

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

struct SymbolInterner {
    next_id: i64,
    ids: HashMap<String, i64>,
}

impl SymbolInterner {
    fn new() -> Self {
        SymbolInterner {
            next_id: 1,
            ids: HashMap::new(),
        }
    }

    fn intern(&mut self, value: &str) -> i64 {
        if let Some(id) = self.ids.get(value) {
            return *id;
        }
        let id = self.next_id;
        self.next_id += 1;
        self.ids.insert(value.to_string(), id);
        id
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
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
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
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
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

/// Check if path is a directory
pub fn rt_file_is_dir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    Ok(Value::Bool(Path::new(&path).is_dir()))
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
            let digest = ring::digest::digest(&ring::digest::SHA256, &content);
            let hex = digest
                .as_ref()
                .iter()
                .map(|byte| format!("{:02x}", byte))
                .collect::<String>();
            Ok(Value::text(hex))
        }
        Err(_) => Ok(Value::text(String::new())),
    }
}

// ============================================================================
// File Operations
// ============================================================================

/// Canonicalize path
pub fn rt_file_canonicalize(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::canonicalize(&path) {
        Ok(canonical) => Ok(Value::text(canonical.to_string_lossy().to_string())),
        Err(_) => {
            // Fallback: make absolute
            match std::env::current_dir() {
                Ok(cwd) => {
                    let abs = cwd.join(&path);
                    Ok(Value::text(abs.to_string_lossy().to_string()))
                }
                Err(_) => Ok(Value::text(path)),
            }
        }
    }
}

/// Read file as text
///
/// Returns plain `Value::Str` (not Option-wrapped) to match the runtime
/// `rt_file_read_text` ABI and the `extern fn rt_file_read_text(path: text) -> text`
/// declarations used throughout the codebase. Returns an empty string on failure.
pub fn rt_file_read_text(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read_to_string(&path) {
        Ok(content) => {
            // Normalize CRLF → LF so indentation-sensitive parsing works on all platforms
            let content = if content.contains('\r') {
                content.replace('\r', "")
            } else {
                content
            };
            Ok(Value::text(content))
        }
        Err(_) => Ok(Value::text(String::new())),
    }
}

/// Read file through the mmap-named API.
///
/// The interpreter does not expose raw mapped memory, so it preserves the
/// Simple-level API contract by returning the file text directly. Native
/// codegen links this symbol to the runtime mmap implementation.
pub fn rt_file_mmap_read_text(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_read_text(args)
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

/// Synchronize file contents and metadata with durable storage.
pub fn rt_file_fsync(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match OpenOptions::new().read(true).open(&path) {
        Ok(file) => Ok(Value::Bool(file.sync_all().is_ok())),
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Interpreter fallback for the runtime cached fsync entrypoint.
pub fn rt_file_fsync_cached(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_fsync(args)
}

/// CRC32 checksum of a text string. Returns the checksum as i64.
pub fn rt_crc32_text(args: &[Value]) -> Result<Value, CompileError> {
    let text = extract_content(args, 0)?;
    let mut crc: u32 = 0xFFFFFFFF;
    for &b in text.as_bytes() {
        crc ^= b as u32;
        for _ in 0..8 {
            crc = (crc >> 1) ^ (0xEDB88320 & (0u32.wrapping_sub(crc & 1)));
        }
    }
    Ok(Value::Int((crc ^ 0xFFFFFFFF) as i64))
}

/// Atomically create a file (O_EXCL semantics). Returns false if the file already exists.
pub fn rt_file_create_excl(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let content = extract_content(args, 1)?;
    match OpenOptions::new()
        .write(true)
        .create_new(true) // O_CREAT | O_EXCL
        .open(&path)
    {
        Ok(mut file) => {
            let ok = file.write_all(content.as_bytes()).is_ok();
            Ok(Value::Bool(ok))
        }
        Err(_) => Ok(Value::Bool(false)),
    }
}

/// Write text at an absolute byte offset without rewriting the full file.
pub fn rt_file_write_text_at(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let offset = match args.get(1) {
        Some(Value::Int(n)) if *n >= 0 => *n as u64,
        _ => return Ok(Value::Int(-1)),
    };
    let content = extract_content(args, 2)?;
    let mut file = match OpenOptions::new().create(true).write(true).truncate(false).open(&path) {
        Ok(file) => file,
        Err(_) => return Ok(Value::Int(-1)),
    };
    if file.seek(SeekFrom::Start(offset)).is_err() {
        return Ok(Value::Int(-1));
    }
    match file.write_all(content.as_bytes()) {
        Ok(_) => Ok(Value::Int(content.len() as i64)),
        Err(_) => Ok(Value::Int(-1)),
    }
}

/// Read text at an absolute byte offset without reading the full file.
pub fn rt_file_read_text_at(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let offset = match args.get(1) {
        Some(Value::Int(n)) if *n >= 0 => *n as u64,
        _ => return Ok(Value::text(String::new())),
    };
    let size = match args.get(2) {
        Some(Value::Int(n)) if *n >= 0 => *n as usize,
        _ => return Ok(Value::text(String::new())),
    };
    let mut file = match OpenOptions::new().read(true).open(&path) {
        Ok(file) => file,
        Err(_) => return Ok(Value::text(String::new())),
    };
    if file.seek(SeekFrom::Start(offset)).is_err() {
        return Ok(Value::text(String::new()));
    }
    let mut buf = vec![0u8; size];
    match file.read(&mut buf) {
        Ok(n) => {
            buf.truncate(n);
            Ok(Value::text(String::from_utf8_lossy(&buf).to_string()))
        }
        Err(_) => Ok(Value::text(String::new())),
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
        if fs::create_dir_all(parent).is_err() {
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
            let lines: Vec<Value> = content.lines().map(|l| Value::text(l.to_string())).collect();
            Ok(make_some(Value::array(lines)))
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

/// Read file as bytes.
///
/// Returns a bare `Value::Array` on success and `Value::Nil` on failure --
/// NOT an `Option::Some`/`None`-wrapped enum. Most `.spl` callers declare
/// this extern as returning a plain (non-optional) `[u8]` and consume the
/// result directly (e.g. `src/compiler/70.backend/backend/
/// llvm_backend_tools.spl`, `src/app/office/pptx_export.spl`) -- an
/// `Option`-wrapped return left those call sites holding a boxed enum where
/// a raw array was expected (see bug doc
/// native_build_fresh_seed_optionwrap_landmine_2026-07-18.md). This mirrors
/// the fix already applied to the sibling `rt_string_bytes_fn` (bug
/// seed_flat_registry_len_i64_2026-07-17): a handful of `.spl` files declare
/// this as `[u8]?` and consume it via `match ...: Some(value): ... nil: ...`
/// (e.g. `src/lib/nogc_sync_mut/sfm/container.spl`) -- those call sites will
/// no longer match the `Some(value)` arm against a bare array; `nil:` still
/// matches `Value::Nil` correctly (`Value::is_nil_like`). Not touched by
/// native (non-interpreted) compilation: natively compiled code calls the
/// C runtime symbol directly (`src/runtime/runtime_native.c`), never this
/// interpreter-only extern binding.
pub fn rt_file_read_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    match fs::read(&path) {
        Ok(bytes) => {
            let arr: Vec<Value> = bytes.into_iter().map(|b| Value::Int(b as i64)).collect();
            Ok(Value::array(arr))
        }
        Err(_) => Ok(Value::Nil),
    }
}

/// Read file bytes through the mmap-named API in interpreter mode.
pub fn rt_file_mmap_read_bytes(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_read_bytes(args)
}

/// Identity function the optimizer must not see through.
///
/// B6 (compiler_bugs_for_crypto_2026-04-25.md): Cranelift can't fold or
/// branch-eliminate through an external call, so wrapping a value in
/// `rt_black_box(x)` keeps it opaque. Used by constant-time crypto code
/// (e.g., `ct_eq` final compare, ML-KEM rejection sampling, Curve25519
/// conditional swap) to prevent the compiler from rewriting an
/// XOR-accumulate loop into an early-exit branch on `diff != 0`.
pub fn rt_black_box(args: &[Value]) -> Result<Value, CompileError> {
    Ok(args.first().cloned().unwrap_or(Value::Nil))
}

/// Allocate a zero-filled `[u8]` of the given length in O(len) C-side.
///
/// B2 (compiler_bugs_for_crypto_2026-04-25.md): the interpreter's
/// `[u8].push` loop is quadratic on multi-MiB buffers. Crypto KAT loaders
/// call `rt_bytes_alloc(n)` instead of building byte buffers via
/// per-element push, sidestepping interpreter dispatch overhead.
pub fn rt_bytes_alloc(args: &[Value]) -> Result<Value, CompileError> {
    let len = match args.first() {
        Some(Value::Int(n)) => *n,
        _ => return Ok(Value::array(vec![])),
    };
    if len <= 0 {
        return Ok(Value::array(vec![]));
    }
    let arr: Vec<Value> = vec![Value::Int(0); len as usize];
    Ok(Value::array(arr))
}

fn typed_alloc_len(args: &[Value]) -> Option<usize> {
    match args.first() {
        Some(Value::Int(n)) if *n > 0 => Some(*n as usize),
        _ => None,
    }
}

/// Allocate a zero-filled `[f64]` for interpreter-mode numeric buffers.
pub fn rt_f64_array_alloc(args: &[Value]) -> Result<Value, CompileError> {
    let Some(len) = typed_alloc_len(args) else {
        return Ok(Value::array(vec![]));
    };
    Ok(Value::array(vec![Value::Float(0.0); len]))
}

/// Allocate a zero-filled `[f32]` for interpreter-mode numeric buffers.
pub fn rt_f32_array_alloc(args: &[Value]) -> Result<Value, CompileError> {
    let Some(len) = typed_alloc_len(args) else {
        return Ok(Value::array(vec![]));
    };
    Ok(Value::array(vec![Value::Float32(0.0); len]))
}

/// Allocate a zero-filled `[i64]` for interpreter-mode numeric buffers.
pub fn rt_i64_array_alloc(args: &[Value]) -> Result<Value, CompileError> {
    let Some(len) = typed_alloc_len(args) else {
        return Ok(Value::array(vec![]));
    };
    Ok(Value::array(vec![Value::Int(0); len]))
}

/// Allocate a zero-filled `[i32]` for interpreter-mode numeric buffers.
pub fn rt_i32_array_alloc(args: &[Value]) -> Result<Value, CompileError> {
    let Some(len) = typed_alloc_len(args) else {
        return Ok(Value::array(vec![]));
    };
    Ok(Value::array(vec![Value::Int(0); len]))
}

/// Intern a text value and return a stable process-local numeric symbol id.
pub fn rt_intern_symbol(args: &[Value]) -> Result<Value, CompileError> {
    let value = match args.first() {
        Some(Value::Str(value)) => value.as_str(),
        _ => "",
    };
    let mut interner = SYMBOL_INTERNER.lock().map_err(|_| {
        CompileError::semantic_with_context(
            "rt_intern_symbol: interner lock poisoned".to_string(),
            ErrorContext::new().with_code(codes::INVALID_OPERATION),
        )
    })?;
    Ok(Value::Int(interner.intern(value)))
}

/// Parse SMF relocation entries from a raw byte buffer at native speed.
///
/// Signature (Simple side):
///   extern fn rt_smf_parse_relocs(data: [u8], sections_off: i64,
///                                  section_count: i64, smf_data_offset: i64) -> [i64]
///
/// Returns a flat [i64] array: 4 elements per reloc entry in order
///   [offset, symbol_index, reloc_type, addend, offset, symbol_index, ...]
///
/// Each reloc entry in the SMF Reloc section (type 5) is 24 bytes:
///   offset(8 LE) | sym_idx(4 LE) | type(1) | pad(3) | addend(8 LE)
///
/// Returns an empty array if no Reloc section is found or inputs are invalid.
/// This bypasses the O(N²) interpreter push loop for 100k+ entry tables.
pub fn rt_smf_parse_relocs(args: &[Value]) -> Result<Value, CompileError> {
    // Extract the [u8] data array
    let data_vals = match args.first() {
        Some(Value::Array(a)) => a.as_ref().clone(),
        _ => return Ok(Value::array(vec![])),
    };
    let data: Vec<u8> = data_vals
        .iter()
        .map(|v| match v {
            Value::Int(n) => *n as u8,
            _ => 0u8,
        })
        .collect();

    let sections_off = match args.get(1) {
        Some(Value::Int(n)) => *n as usize,
        _ => return Ok(Value::array(vec![])),
    };
    let section_count = match args.get(2) {
        Some(Value::Int(n)) => *n as usize,
        _ => return Ok(Value::array(vec![])),
    };
    let smf_data_offset = match args.get(3) {
        Some(Value::Int(n)) => *n as usize,
        _ => return Ok(Value::array(vec![])),
    };

    let section_entry_size: usize = 56;
    let reloc_entry_size: usize = 24;
    let data_len = data.len();

    let read_u64_le = |buf: &[u8], off: usize| -> u64 {
        if off + 8 > buf.len() {
            return 0;
        }
        u64::from_le_bytes([
            buf[off],
            buf[off + 1],
            buf[off + 2],
            buf[off + 3],
            buf[off + 4],
            buf[off + 5],
            buf[off + 6],
            buf[off + 7],
        ])
    };
    let read_u32_le = |buf: &[u8], off: usize| -> u32 {
        if off + 4 > buf.len() {
            return 0;
        }
        u32::from_le_bytes([buf[off], buf[off + 1], buf[off + 2], buf[off + 3]])
    };

    for i in 0..section_count {
        let entry_off = sections_off + i * section_entry_size;
        let entry_end = entry_off + section_entry_size;
        if entry_end > data_len {
            continue;
        }
        let sec_type = data[entry_off] as u32;
        if sec_type != 5 {
            continue;
        }
        // Found RelTab section (type 5)
        let sec_offset_raw = read_u64_le(&data, entry_off + 8) as usize;
        let sec_offset = if smf_data_offset > 0 {
            smf_data_offset + sec_offset_raw
        } else {
            sec_offset_raw
        };
        let sec_size = read_u64_le(&data, entry_off + 16) as usize;
        if sec_offset + sec_size > data_len {
            return Ok(Value::array(vec![]));
        }
        let entry_count = sec_size / reloc_entry_size;
        // Pre-allocate: 4 i64 values per entry
        let mut result: Vec<Value> = Vec::with_capacity(entry_count * 4);
        for j in 0..entry_count {
            let e_off = sec_offset + j * reloc_entry_size;
            let r_offset = read_u64_le(&data, e_off) as i64;
            let r_sym_idx = read_u32_le(&data, e_off + 8) as i64;
            let r_type = data[e_off + 12] as i64;
            let r_addend = read_u64_le(&data, e_off + 16) as i64;
            result.push(Value::Int(r_offset));
            result.push(Value::Int(r_sym_idx));
            result.push(Value::Int(r_type));
            result.push(Value::Int(r_addend));
        }
        return Ok(Value::array(result));
    }
    Ok(Value::array(vec![]))
}

/// Parse SMF relocation entries by reading the file at a given path.
///
/// Signature (Simple side):
///   extern fn rt_smf_relocs_from_path(path: text, sections_off: i64,
///                                      section_count: i64, smf_data_offset: i64) -> [i64]
///
/// Returns a flat [i64] array: 4 elements per reloc entry in order
///   [offset, symbol_index, reloc_type, addend, ...]
///
/// This bypasses the O(N) Value→u8 conversion that makes rt_smf_parse_relocs
/// time out in interpreter mode for large (>1 MB) SMF files.
pub fn rt_smf_relocs_from_path(args: &[Value]) -> Result<Value, CompileError> {
    let path = match args.first() {
        Some(Value::Str(s)) => s.clone(),
        _ => return Ok(Value::array(vec![])),
    };
    let sections_off = match args.get(1) {
        Some(Value::Int(n)) => *n as usize,
        _ => return Ok(Value::array(vec![])),
    };
    let section_count = match args.get(2) {
        Some(Value::Int(n)) => *n as usize,
        _ => return Ok(Value::array(vec![])),
    };
    let smf_data_offset = match args.get(3) {
        Some(Value::Int(n)) => *n as usize,
        _ => return Ok(Value::array(vec![])),
    };

    let data = match std::fs::read(&*path) {
        Ok(d) => d,
        Err(_) => return Ok(Value::array(vec![])),
    };

    let section_entry_size: usize = 56;
    let reloc_entry_size: usize = 24;
    let data_len = data.len();

    let read_u64_le = |buf: &[u8], off: usize| -> u64 {
        if off + 8 > buf.len() {
            return 0;
        }
        u64::from_le_bytes([
            buf[off],
            buf[off + 1],
            buf[off + 2],
            buf[off + 3],
            buf[off + 4],
            buf[off + 5],
            buf[off + 6],
            buf[off + 7],
        ])
    };
    let read_u32_le = |buf: &[u8], off: usize| -> u32 {
        if off + 4 > buf.len() {
            return 0;
        }
        u32::from_le_bytes([buf[off], buf[off + 1], buf[off + 2], buf[off + 3]])
    };

    for i in 0..section_count {
        let entry_off = sections_off + i * section_entry_size;
        let entry_end = entry_off + section_entry_size;
        if entry_end > data_len {
            continue;
        }
        let sec_type = data[entry_off] as u32;
        if sec_type != 5 {
            continue;
        }
        // Found RelTab section (type 5)
        let sec_offset_raw = read_u64_le(&data, entry_off + 8) as usize;
        let sec_offset = if smf_data_offset > 0 {
            smf_data_offset + sec_offset_raw
        } else {
            sec_offset_raw
        };
        let sec_size = read_u64_le(&data, entry_off + 16) as usize;
        if sec_offset + sec_size > data_len {
            return Ok(Value::array(vec![]));
        }
        let entry_count = sec_size / reloc_entry_size;
        let mut result: Vec<Value> = Vec::with_capacity(entry_count * 4);
        for j in 0..entry_count {
            let e_off = sec_offset + j * reloc_entry_size;
            let r_offset = read_u64_le(&data, e_off) as i64;
            let r_sym_idx = read_u32_le(&data, e_off + 8) as i64;
            let r_type = data[e_off + 12] as i64;
            let r_addend = read_u64_le(&data, e_off + 16) as i64;
            result.push(Value::Int(r_offset));
            result.push(Value::Int(r_sym_idx));
            result.push(Value::Int(r_type));
            result.push(Value::Int(r_addend));
        }
        return Ok(Value::array(result));
    }
    Ok(Value::array(vec![]))
}

/// Create a byte array from a raw memory pointer
pub fn rt_bytes_from_raw(args: &[Value]) -> Result<Value, CompileError> {
    let ptr = match args.first() {
        Some(Value::Int(n)) => *n,
        _ => return Ok(Value::array(vec![])),
    };
    let len = match args.get(1) {
        Some(Value::Int(n)) => *n,
        _ => return Ok(Value::array(vec![])),
    };
    if ptr == 0 || len <= 0 {
        return Ok(Value::array(vec![]));
    }
    let src = ptr as usize as *const u8;
    let slice = unsafe { std::slice::from_raw_parts(src, len as usize) };
    let arr: Vec<Value> = slice.iter().map(|&b| Value::Int(b as i64)).collect();
    Ok(Value::array(arr))
}

/// Create a [u32] array from a raw pointer to count little-endian u32 values.
/// One-call return-value marshalling for GPU framebuffer readbacks.
pub fn rt_u32s_from_raw(args: &[Value]) -> Result<Value, CompileError> {
    let ptr = match args.first() {
        Some(Value::Int(n)) => *n,
        _ => return Ok(Value::array(vec![])),
    };
    let count = match args.get(1) {
        Some(Value::Int(n)) => *n,
        _ => return Ok(Value::array(vec![])),
    };
    if ptr == 0 || count <= 0 {
        return Ok(Value::array(vec![]));
    }
    let src = ptr as usize as *const u32;
    let slice = unsafe { std::slice::from_raw_parts(src, count as usize) };
    let arr: Vec<Value> = slice.iter().map(|&v| Value::Int(v as i64)).collect();
    Ok(Value::array(arr))
}

/// Write a `[u32]` array into a raw host pointer as `count` little-endian u32
/// values, in one call. Inverse of `rt_u32s_from_raw`: one-call argument
/// marshalling for GPU framebuffer uploads (draw_image / blit packing).
///
/// Replaces the per-pixel `rt_ptr_write_i32` loop, which under the tree-walking
/// interpreter costs one FFI round-trip per pixel (~480K calls for one 800x600
/// frame — minutes of pure dispatch overhead). Here the whole array is copied
/// natively.
///
/// `rt_write_u32s_to_raw(ptr: i64, arr: [u32]) -> i64` — returns the number of
/// u32 values written, or 0 on error (null ptr / non-array arg). Each element
/// is masked to its low 32 bits and stored little-endian, matching the byte
/// layout the per-pixel `rt_ptr_write_i32(ptr, i*4, v)` loop produced.
pub fn rt_write_u32s_to_raw(args: &[Value]) -> Result<Value, CompileError> {
    let ptr = match args.first() {
        Some(Value::Int(n)) => *n,
        _ => return Ok(Value::Int(0)),
    };
    if ptr == 0 {
        return Ok(Value::Int(0));
    }
    let items: &[Value] = match args.get(1) {
        Some(Value::Array(arr)) => arr,
        Some(Value::FrozenArray(arr)) => arr,
        Some(Value::FixedSizeArray { data, .. }) => data,
        _ => return Ok(Value::Int(0)),
    };
    let dst = ptr as usize as *mut u8;
    let mut written: i64 = 0;
    for (i, v) in items.iter().enumerate() {
        let word: u32 = match v {
            Value::Int(n) => (*n as u64 & 0xFFFF_FFFF) as u32,
            Value::UInt { value, .. } => (*value & 0xFFFF_FFFF) as u32,
            _ => 0,
        };
        let bytes = word.to_le_bytes();
        unsafe {
            let base = dst.add(i * 4);
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), base, 4);
        }
        written += 1;
    }
    Ok(Value::Int(written))
}

/// Write bytes to file
///
/// Handles both `Value::Int(i)` (plain integer byte) and
/// `Value::UInt { value, width: 8 }` (u8-typed values from `as u8` casts in
/// compression/encoding code). Previously only matched `Int`, silently dropping
/// all UInt-tagged elements and producing truncated output (observed: single-byte
/// zstd frames). Fix: map both variants to their u8 representation.
pub fn rt_file_write_bytes(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let bytes_arr = match args.get(1) {
        Some(Value::Array(arr)) => arr,
        Some(Value::FrozenArray(arr)) => arr,
        Some(Value::FixedSizeArray { data, .. }) => {
            let bytes: Vec<u8> = data
                .iter()
                .map(|v| match v {
                    Value::Int(i) => *i as u8,
                    Value::UInt { value, .. } => *value as u8,
                    _ => 0u8,
                })
                .collect();
            return match fs::write(&path, &bytes) {
                Ok(_) => Ok(Value::Bool(true)),
                Err(_) => Ok(Value::Bool(false)),
            };
        }
        _ => return Ok(Value::Bool(false)),
    };

    let bytes: Vec<u8> = bytes_arr
        .iter()
        .map(|v| match v {
            Value::Int(i) => *i as u8,
            Value::UInt { value, .. } => *value as u8,
            _ => 0u8,
        })
        .collect();

    match fs::write(&path, &bytes) {
        Ok(_) => Ok(Value::Bool(true)),
        Err(_) => Ok(Value::Bool(false)),
    }
}

pub fn rt_file_wrap_smf_dynlib(args: &[Value]) -> Result<Value, CompileError> {
    let input_path = extract_path(args, 0)?;
    let output_path = extract_path(args, 1)?;
    let arch_code = match args.get(2) {
        Some(Value::Int(n)) => (*n).clamp(0, 255) as u8,
        Some(Value::UInt { value, .. }) => (*value).min(255) as u8,
        _ => 0,
    };
    let mut out = match fs::read(&input_path) {
        Ok(bytes) if !bytes.is_empty() => bytes,
        _ => return Ok(Value::Bool(false)),
    };
    let stub_len = out.len() as u32;
    out.reserve(128);
    out.extend_from_slice(&[83, 77, 70, 0]);
    while out.len() < stub_len as usize + 52 {
        out.push(0);
    }
    out.extend_from_slice(&stub_len.to_le_bytes());
    out.extend_from_slice(&stub_len.to_le_bytes());
    out.push(2);
    out.push(arch_code);
    out.push(0);
    while out.len() < stub_len as usize + 128 {
        out.push(0);
    }
    Ok(Value::Bool(fs::write(&output_path, out).is_ok()))
}

pub fn rt_file_extract_smf_dynlib(args: &[Value]) -> Result<Value, CompileError> {
    let input_path = extract_path(args, 0)?;
    let output_path = extract_path(args, 1)?;
    let bytes = match fs::read(&input_path) {
        Ok(bytes) if bytes.len() >= 128 => bytes,
        _ => return Ok(Value::Bool(false)),
    };
    let header_offset = bytes.len() - 128;
    if bytes[header_offset..header_offset + 4] != [83, 77, 70, 0] {
        return Ok(Value::Bool(false));
    }
    let stub_size = u32::from_le_bytes([
        bytes[header_offset + 52],
        bytes[header_offset + 53],
        bytes[header_offset + 54],
        bytes[header_offset + 55],
    ]) as usize;
    if bytes[header_offset + 60] != 2 || stub_size == 0 || stub_size > header_offset {
        return Ok(Value::Bool(false));
    }
    let stub = &bytes[..stub_size];
    let has_elf = stub.len() >= 4 && stub[0..4] == [0x7F, 0x45, 0x4C, 0x46];
    let has_macho = stub.len() >= 4
        && ((stub[0] == 0xFE && stub[1] == 0xED && stub[2] == 0xFA && (stub[3] == 0xCE || stub[3] == 0xCF))
            || ((stub[0] == 0xCE || stub[0] == 0xCF) && stub[1] == 0xFA && stub[2] == 0xED && stub[3] == 0xFE)
            || (stub[0] == 0xCA && stub[1] == 0xFE && stub[2] == 0xBA && stub[3] == 0xBE)
            || (stub[0] == 0xBE && stub[1] == 0xBA && stub[2] == 0xFE && stub[3] == 0xCA));
    if !has_elf && !has_macho {
        return Ok(Value::Bool(false));
    }
    Ok(Value::Bool(fs::write(&output_path, stub).is_ok()))
}

/// Truncate (or zero-extend) file at `path` to exactly `size` bytes.
///
/// IF-13 wave-4d: the interpreter cannot build a multi-MiB byte buffer in
/// reasonable time. Disk-image bakes use this to write the structural prefix
/// (BPB+FATs+root dir+payload) and let the kernel zero-fill the remainder.
pub fn rt_file_truncate(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    // Handles both `Value::Int(n)` (plain integer) and `Value::UInt { value, .. }`
    // (u64-typed values from `u64` literals / `as u64` casts, as used by disk-image
    // builders). Previously only matched `Int`, so a boxed u64 size arg silently
    // fell through to `Bool(false)` with no error, no set_len -- see
    // doc/08_tracking/bug/disk_image_fat32_builder_defects.md #2.
    let size: u64 = match args.get(1) {
        Some(Value::Int(n)) => *n as u64,
        Some(Value::UInt { value, .. }) => *value,
        other => {
            return Err(CompileError::semantic(format!(
                "rt_file_truncate() expects (path: text, size: u64), got size arg {:?}",
                other
            )));
        }
    };
    // I/O failures (missing dir, permissions, disk full, ...) stay as `Bool(false)`
    // rather than a hard error: callers such as disk_image.spl's `build()` already
    // handle a `false` return with their own fallback/Err path. Only the arg-type
    // mismatch above (a genuine programming bug, not a runtime condition) hard-errors.
    let file = match OpenOptions::new().write(true).create(true).truncate(false).open(&path) {
        Ok(f) => f,
        Err(_) => return Ok(Value::Bool(false)),
    };
    match file.set_len(size) {
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
    if fs::copy(&src, &dest).is_ok() && fs::remove_file(&src).is_ok() {
        return Ok(Value::Bool(true));
    }

    Ok(Value::Bool(false))
}

#[cfg(test)]
mod tests {
    use super::*;

    // Regression coverage for the P2 interpreter-over-count bug
    // (doc/08_tracking/bug/dir_walk_native_runtime_parity_2026-07-16.md,
    // "## Interpreter over-count (P2)"): this and the symlink test below both
    // pin down that `rt_dir_walk` pushes only non-directory entries and
    // recurses into directories WITHOUT also pushing the directory itself.
    // Pre-fix (before a6822a52dee), the loop unconditionally pushed every
    // `read_dir` entry (files AND directories) and then separately recursed
    // into directories, double-counting every directory in the tree — for a
    // real tree with N subdirectories that inflates the count by exactly N
    // (observed: `src/app/cli`, 76 files + 4 subdirs = the reported 80).
    #[cfg(unix)]
    #[test]
    fn dir_walk_emits_links_once_without_following_directory_cycles() {
        use std::os::unix::fs::symlink;

        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        std::fs::write(root.join("regular.spl"), "").expect("regular file");
        std::fs::create_dir(root.join("nested")).expect("nested directory");
        std::fs::write(root.join("nested/child.spl"), "").expect("nested file");
        std::fs::create_dir(root.join("x.spl")).expect("directory with source suffix");
        symlink(root.join("regular.spl"), root.join("file-link.spl")).expect("file symlink");
        symlink(root, root.join("nested/back")).expect("cycle symlink");

        let result = rt_dir_walk(&[Value::text(root.to_string_lossy().to_string())]).expect("walk");
        let Value::Array(paths) = result else {
            panic!("dir walk did not return an array");
        };
        let mut relative: Vec<String> = paths
            .iter()
            .map(|path| match path {
                Value::Str(value) => std::path::Path::new(value.as_str())
                    .strip_prefix(root)
                    .expect("path under fixture")
                    .to_string_lossy()
                    .to_string(),
                other => panic!("non-text walk entry: {other:?}"),
            })
            .collect();
        relative.sort();
        assert_eq!(
            relative,
            vec![
                "file-link.spl".to_string(),
                "nested/back".to_string(),
                "nested/child.spl".to_string(),
                "regular.spl".to_string(),
            ]
        );
    }

    /// Symlink-free variant of the fixture above: N nested subdirectories with
    /// files inside must yield exactly the file count, never file_count + N.
    /// This is the literal shape of the `src/app/cli` ground-truth repro (0
    /// symlinks, 4 subdirectories, 76 files) that exposed the pre-fix bug.
    #[test]
    fn dir_walk_counts_files_only_not_directories_themselves() {
        let dir = tempfile::tempdir().expect("tempdir");
        let root = dir.path();
        std::fs::write(root.join("top.spl"), "").expect("top-level file");
        for name in ["a", "b", "c", "d"] {
            let sub = root.join(name);
            std::fs::create_dir(&sub).expect("subdir");
            std::fs::write(sub.join("child.spl"), "").expect("nested file");
        }

        let result = rt_dir_walk(&[Value::text(root.to_string_lossy().to_string())]).expect("walk");
        let Value::Array(paths) = result else {
            panic!("dir walk did not return an array");
        };
        // 1 top-level file + 4 subdirs * 1 file each = 5 files total; the 4
        // subdirectory paths themselves must NOT appear in the result.
        assert_eq!(paths.len(), 5, "directories must be recursed-into, not counted as entries");
    }

    #[test]
    fn write_text_at_creates_and_appends_without_rewrite() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("append.txt");
        let path = path.to_string_lossy().to_string();

        let first = rt_file_write_text_at(&[Value::text(path.clone()), Value::Int(0), Value::text("abc".to_string())])
            .expect("first write");
        let second = rt_file_write_text_at(&[Value::text(path.clone()), Value::Int(3), Value::text("def".to_string())])
            .expect("second write");

        assert_eq!(first, Value::Int(3));
        assert_eq!(second, Value::Int(3));
        assert_eq!(std::fs::read_to_string(path).expect("read"), "abcdef");
    }

    #[test]
    fn truncate_accepts_boxed_u64_size_arg() {
        // disk_image.spl (a `u64`-typed disk-image builder) calls
        // rt_file_truncate(path, size_mb * 1024u64 * 1024u64); the size arg
        // arrives as the boxed `Value::UInt { value, width: 64 }` form, not
        // `Value::Int`. Previously this silently fell through to
        // `Bool(false)` with no error and no set_len -- see
        // doc/08_tracking/bug/disk_image_fat32_builder_defects.md #2.
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("truncate_boxed.bin");
        std::fs::write(&path, b"abc").expect("seed write");
        let path = path.to_string_lossy().to_string();

        let ok = rt_file_truncate(&[Value::text(path.clone()), Value::UInt { value: 4096, width: 64 }])
            .expect("truncate with boxed u64 size");
        assert_eq!(ok, Value::Bool(true));
        assert_eq!(std::fs::metadata(&path).expect("metadata").len(), 4096);
    }

    #[test]
    fn truncate_accepts_plain_int_size_arg() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("truncate_int.bin");
        std::fs::write(&path, b"abc").expect("seed write");
        let path = path.to_string_lossy().to_string();

        let ok = rt_file_truncate(&[Value::text(path.clone()), Value::Int(2048)]).expect("truncate with int size");
        assert_eq!(ok, Value::Bool(true));
        assert_eq!(std::fs::metadata(&path).expect("metadata").len(), 2048);
    }

    #[test]
    fn truncate_errors_on_non_integer_size_arg() {
        // A genuinely bad arg (wrong type) should hard-error, not silently
        // return Bool(false).
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("truncate_bad.bin");
        std::fs::write(&path, b"abc").expect("seed write");
        let path = path.to_string_lossy().to_string();

        let result = rt_file_truncate(&[Value::text(path), Value::text("not-a-size".to_string())]);
        assert!(result.is_err());
    }

    #[test]
    fn fsync_reports_existing_and_missing_file() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("sync.txt");
        std::fs::write(&path, "durable").expect("write");
        let path = path.to_string_lossy().to_string();

        let ok = rt_file_fsync(&[Value::text(path)]).expect("fsync");
        assert_eq!(ok, Value::Bool(true));

        let missing = dir.path().join("missing.txt").to_string_lossy().to_string();
        let fail = rt_file_fsync(&[Value::text(missing)]).expect("missing fsync");
        assert_eq!(fail, Value::Bool(false));
    }

    #[test]
    fn mmap_named_text_and_bytes_match_read_contract() {
        let dir = tempfile::tempdir().expect("tempdir");
        let path = dir.path().join("fixture.txt");
        std::fs::write(&path, "simple mmap").expect("write");
        let path = path.to_string_lossy().to_string();

        let text = rt_file_mmap_read_text(&[Value::text(path.clone())]).expect("mmap text");
        let bytes = rt_file_mmap_read_bytes(&[Value::text(path)]).expect("mmap bytes");

        assert_eq!(text, Value::text("simple mmap".to_string()));
        // rt_file_read_bytes (and its mmap-named alias) returns a bare
        // Value::Array on success, not an Option::Some-wrapped enum -- see
        // bug native_build_fresh_seed_optionwrap_landmine_2026-07-18.md.
        // Most `.spl` callers declare this extern as returning a plain
        // (non-optional) `[u8]` and use the result directly; an
        // Option-wrapped return left those call sites holding a boxed enum
        // where a raw array was expected.
        match bytes {
            Value::Array(values) => assert_eq!(values.len(), 11),
            other => panic!("unexpected bytes value: {other:?}"),
        }
    }
}

// ============================================================================
// Directory Operations
// ============================================================================

/// Check if directory exists
pub fn rt_dir_exists(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    Ok(Value::Bool(std::path::Path::new(&path).is_dir()))
}

/// Create directory
pub fn rt_dir_create(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let recursive = matches!(args.get(1), Some(Value::Bool(true)));
    let result = if recursive {
        fs::create_dir_all(&path)
    } else {
        fs::create_dir(&path)
    };
    match result {
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
                .map(Value::text)
                .collect();
            Ok(Value::array(names))
        }
        Err(_) => Ok(Value::array(vec![])),
    }
}

/// Remove directory
pub fn rt_dir_remove(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let recursive = matches!(args.get(1), Some(Value::Bool(true)));
    let result = if recursive {
        fs::remove_dir_all(&path)
    } else {
        fs::remove_dir(&path)
    };
    match result {
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
                        Some(Value::text(e.path().to_string_lossy().to_string()))
                    } else {
                        None
                    }
                })
                .collect();
            Ok(Value::array(matches))
        }
        Err(_) => Ok(Value::array(vec![])),
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
                let Ok(file_type) = entry.file_type() else {
                    continue;
                };
                if file_type.is_dir() {
                    walk_recursive(&path, results);
                } else {
                    results.push(Value::text(path.to_string_lossy().to_string()));
                }
            }
        }
    }

    let mut results = Vec::new();
    walk_recursive(Path::new(&path), &mut results);
    Ok(Value::array(results))
}

/// Get current directory (returns Option<text>)
pub fn rt_current_dir(_args: &[Value]) -> Result<Value, CompileError> {
    match std::env::current_dir() {
        Ok(cwd) => Ok(make_some(Value::text(cwd.to_string_lossy().to_string()))),
        Err(_) => Ok(make_none()),
    }
}

/// Get current directory (returns plain text, for snpm compatibility)
pub fn rt_get_cwd(_args: &[Value]) -> Result<Value, CompileError> {
    match std::env::current_dir() {
        Ok(cwd) => Ok(Value::text(cwd.to_string_lossy().to_string())),
        Err(_) => Ok(Value::text(String::new())),
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
    Ok(Value::text(basename.to_string()))
}

/// Get dirname
pub fn rt_path_dirname(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let dirname = Path::new(&path).parent().and_then(|p| p.to_str()).unwrap_or("");
    Ok(Value::text(dirname.to_string()))
}

/// Get extension
pub fn rt_path_ext(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let ext = Path::new(&path).extension().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::text(ext.to_string()))
}

/// Get absolute path
pub fn rt_path_absolute(args: &[Value]) -> Result<Value, CompileError> {
    rt_file_canonicalize(args)
}

/// Get path separator
pub fn rt_path_separator(_args: &[Value]) -> Result<Value, CompileError> {
    #[cfg(target_os = "windows")]
    return Ok(Value::text("\\".to_string()));
    #[cfg(not(target_os = "windows"))]
    Ok(Value::text("/".to_string()))
}

/// Get file stem
pub fn rt_path_stem(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let stem = Path::new(&path).file_stem().and_then(|s| s.to_str()).unwrap_or("");
    Ok(Value::text(stem.to_string()))
}

/// Get relative path
pub fn rt_path_relative(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let base = extract_path(args, 1)?;

    let path_obj = Path::new(&path);
    let base_obj = Path::new(&base);

    match path_obj.strip_prefix(base_obj) {
        Ok(relative) => Ok(Value::text(relative.to_string_lossy().to_string())),
        Err(_) => Ok(Value::text(path)),
    }
}

/// Join paths
pub fn rt_path_join(args: &[Value]) -> Result<Value, CompileError> {
    let path1 = extract_path(args, 0)?;
    let path2 = extract_path(args, 1)?;

    let joined = Path::new(&path1).join(&path2);
    Ok(Value::text(joined.to_string_lossy().to_string()))
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
        match OpenOptions::new().write(true).create_new(true).open(&lock_path) {
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

/// Host target architecture code for backend selection:
/// 0 = x86_64, 1 = aarch64, 2 = riscv64. Unknown architectures fall back to 0
/// (the compiler's default host target), keeping the result in the 0..=2 range
/// the backend selector expects.
pub fn rt_get_host_target_code(_args: &[Value]) -> Result<Value, CompileError> {
    let code = match std::env::consts::ARCH {
        "x86_64" => 0,
        "aarch64" | "arm64" => 1,
        "riscv64" => 2,
        _ => 0,
    };
    Ok(Value::Int(code))
}

/// Check if a process with given PID exists
pub fn rt_process_exists(args: &[Value]) -> Result<Value, CompileError> {
    if args.len() != 1 {
        return Err(CompileError::semantic(
            "rt_process_exists() expects 1 argument (pid: i64)",
        ));
    }

    let pid = match &args[0] {
        Value::Int(i) => *i,
        _ => return Err(CompileError::semantic("rt_process_exists() expects i64 argument")),
    };

    // On Unix systems, check /proc/<pid> directory
    #[cfg(unix)]
    {
        let proc_path = format!("/proc/{}", pid);
        let exists = std::path::Path::new(&proc_path).exists();
        Ok(Value::Bool(exists))
    }

    #[cfg(not(unix))]
    {
        // Fallback for non-Unix: always return true
        // This is conservative - assume process might exist
        Ok(Value::Bool(true))
    }
}

/// Get hostname
pub fn rt_hostname(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::text(get_hostname()))
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
    Ok(Value::Int(
        std::thread::available_parallelism()
            .map(|n| n.get() as i64)
            .unwrap_or(1),
    ))
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

// ========================================================================
// POSIX-style file I/O externs (matching C runtime signatures in runtime.c)
// ========================================================================

pub fn rt_mkdir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        let mode = if args.len() > 1 {
            match &args[1] {
                Value::Int(m) => *m as u32,
                _ => 0o755,
            }
        } else {
            0o755
        };
        let mut builder = fs::DirBuilder::new();
        builder.mode(mode);
        match builder.create(&path) {
            Ok(_) => Ok(Value::Int(0)),
            Err(e) => Ok(Value::Int(-(errno_from_io_error(&e)))),
        }
    }
    #[cfg(not(unix))]
    {
        match fs::create_dir(&path) {
            Ok(_) => Ok(Value::Int(0)),
            Err(e) => Ok(Value::Int(-(errno_from_io_error(&e)))),
        }
    }
}

pub fn rt_remove(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let p = Path::new(&path);
    let result = if p.is_dir() {
        fs::remove_dir(p)
    } else {
        fs::remove_file(p)
    };
    match result {
        Ok(_) => Ok(Value::Int(0)),
        Err(e) => Ok(Value::Int(-(errno_from_io_error(&e)))),
    }
}

struct StatHandle {
    size: i64,
    mtime: i64,
    is_dir: bool,
    is_file: bool,
    is_symlink: bool,
    readonly: bool,
    created: i64,
}

static STAT_HANDLES: std::sync::Mutex<Vec<Option<StatHandle>>> = std::sync::Mutex::new(Vec::new());

fn stat_path_is_symlink(path: &str) -> bool {
    let meta = match fs::symlink_metadata(path) {
        Ok(meta) => meta,
        Err(_) => return false,
    };
    #[cfg(windows)]
    {
        use std::os::windows::fs::MetadataExt;
        return meta.file_attributes() & 0x400 != 0;
    }
    #[cfg(not(windows))]
    meta.file_type().is_symlink()
}

#[cfg(any(target_os = "macos", target_os = "freebsd", windows))]
fn stat_created_seconds(meta: &fs::Metadata) -> i64 {
    use std::time::UNIX_EPOCH;
    meta.created()
        .ok()
        .and_then(|time| time.duration_since(UNIX_EPOCH).ok())
        .map(|duration| duration.as_secs() as i64)
        .unwrap_or(0)
}

#[cfg(not(any(target_os = "macos", target_os = "freebsd", windows)))]
fn stat_created_seconds(_meta: &fs::Metadata) -> i64 {
    0
}

pub fn rt_stat_open(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let meta = match fs::metadata(&path) {
        Ok(m) => m,
        Err(_) => return Ok(Value::Int(0)),
    };
    let mtime = {
        use std::time::UNIX_EPOCH;
        meta.modified()
            .ok()
            .and_then(|t| t.duration_since(UNIX_EPOCH).ok())
            .map(|d| d.as_secs() as i64)
            .unwrap_or(0)
    };
    let handle = StatHandle {
        size: meta.len() as i64,
        mtime,
        is_dir: meta.is_dir(),
        is_file: meta.is_file(),
        is_symlink: stat_path_is_symlink(&path),
        readonly: meta.permissions().readonly(),
        created: stat_created_seconds(&meta),
    };
    let mut handles = STAT_HANDLES.lock().unwrap();
    for (i, slot) in handles.iter_mut().enumerate() {
        if slot.is_none() {
            *slot = Some(handle);
            return Ok(Value::Int((i + 1) as i64));
        }
    }
    handles.push(Some(handle));
    Ok(Value::Int(handles.len() as i64))
}

pub fn rt_file_stat_size(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Int(0));
    };
    let handles = STAT_HANDLES.lock().unwrap();
    Ok(Value::Int(
        handles.get(h).and_then(|s| s.as_ref()).map(|s| s.size).unwrap_or(0),
    ))
}

pub fn rt_file_stat_mtime(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Int(0));
    };
    let handles = STAT_HANDLES.lock().unwrap();
    Ok(Value::Int(
        handles.get(h).and_then(|s| s.as_ref()).map(|s| s.mtime).unwrap_or(0),
    ))
}

pub fn rt_file_stat_is_dir(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Bool(false));
    };
    let handles = STAT_HANDLES.lock().unwrap();
    Ok(Value::Bool(
        handles
            .get(h)
            .and_then(|s| s.as_ref())
            .map(|s| s.is_dir)
            .unwrap_or(false),
    ))
}

pub fn rt_file_stat_is_file(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Bool(false));
    };
    let handles = STAT_HANDLES.lock().unwrap();
    Ok(Value::Bool(
        handles
            .get(h)
            .and_then(|s| s.as_ref())
            .map(|s| s.is_file)
            .unwrap_or(false),
    ))
}

pub fn rt_file_stat_is_symlink(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Bool(false));
    };
    let handles = STAT_HANDLES.lock().unwrap();
    Ok(Value::Bool(
        handles
            .get(h)
            .and_then(|s| s.as_ref())
            .map(|s| s.is_symlink)
            .unwrap_or(false),
    ))
}

pub fn rt_file_stat_readonly(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Bool(false));
    };
    let handles = STAT_HANDLES.lock().unwrap();
    Ok(Value::Bool(
        handles
            .get(h)
            .and_then(|s| s.as_ref())
            .map(|s| s.readonly)
            .unwrap_or(false),
    ))
}

pub fn rt_file_stat_created(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Int(0));
    };
    let handles = STAT_HANDLES.lock().unwrap();
    Ok(Value::Int(
        handles.get(h).and_then(|s| s.as_ref()).map(|s| s.created).unwrap_or(0),
    ))
}

pub fn rt_file_stat_free(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Int(0));
    };
    let mut handles = STAT_HANDLES.lock().unwrap();
    if h < handles.len() {
        handles[h] = None;
    }
    Ok(Value::Int(0))
}

struct DirListing {
    entries: Vec<String>,
}

static DIR_HANDLES: std::sync::Mutex<Vec<Option<DirListing>>> = std::sync::Mutex::new(Vec::new());

pub fn rt_readdir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let entries: Vec<String> = match fs::read_dir(&path) {
        Ok(rd) => rd.flatten().filter_map(|e| e.file_name().into_string().ok()).collect(),
        Err(_) => return Ok(Value::Int(0)),
    };
    let listing = DirListing { entries };
    let mut handles = DIR_HANDLES.lock().unwrap();
    for (i, slot) in handles.iter_mut().enumerate() {
        if slot.is_none() {
            *slot = Some(listing);
            return Ok(Value::Int((i + 1) as i64));
        }
    }
    handles.push(Some(listing));
    Ok(Value::Int(handles.len() as i64))
}

pub fn rt_readdir_count(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Int(0));
    };
    let handles = DIR_HANDLES.lock().unwrap();
    Ok(Value::Int(
        handles
            .get(h)
            .and_then(|s| s.as_ref())
            .map(|s| s.entries.len() as i64)
            .unwrap_or(0),
    ))
}

pub fn rt_readdir_entry(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::text(String::new()));
    };
    let idx = if let Value::Int(v) = &args[1] {
        *v as usize
    } else {
        return Ok(Value::text(String::new()));
    };
    let handles = DIR_HANDLES.lock().unwrap();
    let entry = handles
        .get(h)
        .and_then(|s| s.as_ref())
        .and_then(|s| s.entries.get(idx))
        .cloned()
        .unwrap_or_default();
    Ok(Value::text(entry))
}

pub fn rt_readdir_free(args: &[Value]) -> Result<Value, CompileError> {
    let h = if let Value::Int(v) = &args[0] {
        (*v - 1) as usize
    } else {
        return Ok(Value::Int(0));
    };
    let mut handles = DIR_HANDLES.lock().unwrap();
    if h < handles.len() {
        handles[h] = None;
    }
    Ok(Value::Int(0))
}

fn errno_from_io_error(e: &std::io::Error) -> i64 {
    match e.kind() {
        std::io::ErrorKind::NotFound => 2,
        std::io::ErrorKind::PermissionDenied => 13,
        std::io::ErrorKind::AlreadyExists => 17,
        _ => 5, // EIO
    }
}
