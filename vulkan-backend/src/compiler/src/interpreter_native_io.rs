// Native I/O implementations for the interpreter
//
// This module provides implementations for extern functions declared in:
// - simple/std_lib/src/host/async_nogc/io/fs.spl (filesystem operations)
// - simple/std_lib/src/host/async_nogc/io/term.spl (terminal I/O)
//
// Note: This file is include!'d into interpreter.rs, so it inherits imports from there.

use std::fs::{File, OpenOptions};
use std::io::{self, ErrorKind, Read, Seek, SeekFrom, Write};
use std::sync::atomic::{AtomicI64, Ordering};

//==============================================================================
// File Handle Pool
//==============================================================================

static NEXT_HANDLE_ID: AtomicI64 = AtomicI64::new(100); // Start at 100 to avoid stdin/stdout/stderr

thread_local! {
    static FILE_HANDLES: RefCell<HashMap<i64, File>> = RefCell::new(HashMap::new());
    #[cfg(unix)]
    static ORIGINAL_TERMIOS: RefCell<Option<libc::termios>> = const { RefCell::new(None) };
}

fn allocate_handle(file: File) -> i64 {
    let id = NEXT_HANDLE_ID.fetch_add(1, Ordering::SeqCst);
    FILE_HANDLES.with(|handles| {
        handles.borrow_mut().insert(id, file);
    });
    id
}

fn with_handle<F, R>(id: i64, f: F) -> Result<R, io::Error>
where
    F: FnOnce(&mut File) -> io::Result<R>,
{
    FILE_HANDLES.with(|handles| {
        let mut handles = handles.borrow_mut();
        match handles.get_mut(&id) {
            Some(file) => f(file),
            None => Err(io::Error::new(ErrorKind::InvalidInput, "invalid file handle")),
        }
    })
}

fn release_handle(id: i64) -> bool {
    FILE_HANDLES.with(|handles| handles.borrow_mut().remove(&id).is_some())
}

/// Helper to create an Option::Some value
fn make_option_some(value: Value) -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "Some".to_string(),
        payload: Some(Box::new(value)),
    }
}

/// Helper to create an Option::None value
fn make_option_none() -> Value {
    Value::Enum {
        enum_name: "Option".to_string(),
        variant: "None".to_string(),
        payload: None,
    }
}

/// Helper to create an optional timestamp field from SystemTime
fn make_timestamp_option(time_result: io::Result<std::time::SystemTime>) -> Value {
    match time_result {
        Ok(time) => {
            if let Ok(duration) = time.duration_since(std::time::UNIX_EPOCH) {
                make_option_some(Value::Int(duration.as_nanos() as i64))
            } else {
                make_option_none()
            }
        }
        Err(_) => make_option_none(),
    }
}

//==============================================================================
// IoError Helpers
//==============================================================================

fn make_io_error(err: io::Error) -> Value {
    let variant = match err.kind() {
        ErrorKind::NotFound => "NotFound",
        ErrorKind::PermissionDenied => "PermissionDenied",
        ErrorKind::AlreadyExists => "AlreadyExists",
        ErrorKind::InvalidInput => "InvalidPath",
        ErrorKind::IsADirectory => "IsDirectory",
        ErrorKind::NotADirectory => "NotDirectory",
        ErrorKind::DirectoryNotEmpty => "DirectoryNotEmpty",
        ErrorKind::ReadOnlyFilesystem => "ReadOnly",
        ErrorKind::StorageFull => "OutOfSpace",
        ErrorKind::Interrupted => "Interrupted",
        ErrorKind::TimedOut => "TimedOut",
        ErrorKind::ConnectionRefused => "ConnectionRefused",
        ErrorKind::ConnectionReset => "ConnectionReset",
        ErrorKind::BrokenPipe => "BrokenPipe",
        ErrorKind::WouldBlock => "WouldBlock",
        ErrorKind::InvalidData => "InvalidData",
        ErrorKind::UnexpectedEof => "UnexpectedEof",
        _ => {
            return Value::Enum {
                enum_name: "IoError".to_string(),
                variant: "Other".to_string(),
                payload: Some(Box::new(Value::Str(err.to_string()))),
            };
        }
    };

    Value::Enum {
        enum_name: "IoError".to_string(),
        variant: variant.to_string(),
        payload: None,
    }
}

fn io_ok(val: Value) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Ok".to_string(),
        payload: Some(Box::new(val)),
    }
}

fn io_err(err: io::Error) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Some(Box::new(make_io_error(err))),
    }
}

fn io_err_msg(msg: &str) -> Value {
    Value::Enum {
        enum_name: "Result".to_string(),
        variant: "Err".to_string(),
        payload: Some(Box::new(Value::Enum {
            enum_name: "IoError".to_string(),
            variant: "Other".to_string(),
            payload: Some(Box::new(Value::Str(msg.to_string()))),
        })),
    }
}

//==============================================================================
// Value Extraction Helpers
//==============================================================================

fn extract_path(args: &[Value], idx: usize) -> Result<String, CompileError> {
    args.get(idx)
        .and_then(|v| match v {
            Value::Str(s) => Some(s.clone()),
            Value::Symbol(s) => Some(s.clone()),
            // Unit types and other string-like values
            _ => None,
        })
        .ok_or_else(|| CompileError::Semantic(format!("argument {} must be a path string", idx)))
}

fn extract_bytes(args: &[Value], idx: usize) -> Result<Vec<u8>, CompileError> {
    match args.get(idx) {
        Some(Value::Array(arr)) => {
            let mut bytes = Vec::with_capacity(arr.len());
            for v in arr {
                match v {
                    Value::Int(i) => bytes.push(*i as u8),
                    _ => {
                        return Err(CompileError::Semantic(
                            "byte array must contain integers".into(),
                        ))
                    }
                }
            }
            Ok(bytes)
        }
        Some(Value::Str(s)) => Ok(s.as_bytes().to_vec()),
        _ => Err(CompileError::Semantic(format!(
            "argument {} must be bytes or string",
            idx
        ))),
    }
}

fn extract_bool(args: &[Value], idx: usize) -> bool {
    args.get(idx).map(|v| v.truthy()).unwrap_or(false)
}

fn extract_int(args: &[Value], idx: usize) -> Result<i64, CompileError> {
    args.get(idx)
        .and_then(|v| v.as_int().ok())
        .ok_or_else(|| CompileError::Semantic(format!("argument {} must be an integer", idx)))
}

fn extract_open_mode(args: &[Value], idx: usize) -> Result<String, CompileError> {
    match args.get(idx) {
        Some(Value::Enum { variant, .. }) => Ok(variant.clone()),
        Some(Value::Str(s)) => Ok(s.clone()),
        _ => Err(CompileError::Semantic(format!(
            "argument {} must be an OpenMode",
            idx
        ))),
    }
}

//==============================================================================
// Filesystem Operations
//==============================================================================

pub fn native_fs_read(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;

    match std::fs::read(&path) {
        Ok(bytes) => {
            let arr: Vec<Value> = bytes.into_iter().map(|b| Value::Int(b as i64)).collect();
            Ok(io_ok(Value::Array(arr)))
        }
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_write(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let data = extract_bytes(args, 1)?;

    match std::fs::write(&path, &data) {
        Ok(()) => Ok(io_ok(Value::Int(data.len() as i64))),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_append(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let data = extract_bytes(args, 1)?;

    match OpenOptions::new().append(true).create(true).open(&path) {
        Ok(mut file) => match file.write_all(&data) {
            Ok(()) => Ok(io_ok(Value::Int(data.len() as i64))),
            Err(e) => Ok(io_err(e)),
        },
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_create_dir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let recursive = extract_bool(args, 1);

    let result = if recursive {
        std::fs::create_dir_all(&path)
    } else {
        std::fs::create_dir(&path)
    };

    match result {
        Ok(()) => Ok(io_ok(Value::Nil)),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_remove_file(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;

    match std::fs::remove_file(&path) {
        Ok(()) => Ok(io_ok(Value::Nil)),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_remove_dir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let recursive = extract_bool(args, 1);

    let result = if recursive {
        std::fs::remove_dir_all(&path)
    } else {
        std::fs::remove_dir(&path)
    };

    match result {
        Ok(()) => Ok(io_ok(Value::Nil)),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_rename(args: &[Value]) -> Result<Value, CompileError> {
    let from = extract_path(args, 0)?;
    let to = extract_path(args, 1)?;

    match std::fs::rename(&from, &to) {
        Ok(()) => Ok(io_ok(Value::Nil)),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_copy(args: &[Value]) -> Result<Value, CompileError> {
    let from = extract_path(args, 0)?;
    let to = extract_path(args, 1)?;

    match std::fs::copy(&from, &to) {
        Ok(bytes) => Ok(io_ok(Value::Int(bytes as i64))),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_metadata(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;

    match std::fs::metadata(&path) {
        Ok(meta) => {
            let mut fields = HashMap::new();
            fields.insert("size".to_string(), Value::Int(meta.len() as i64));
            fields.insert(
                "readonly".to_string(),
                Value::Bool(meta.permissions().readonly()),
            );

            // File type
            let file_type = if meta.is_file() {
                "File"
            } else if meta.is_dir() {
                "Directory"
            } else if meta.file_type().is_symlink() {
                "Symlink"
            } else {
                "Other"
            };
            fields.insert(
                "file_type".to_string(),
                Value::Enum {
                    enum_name: "FileType".to_string(),
                    variant: file_type.to_string(),
                    payload: None,
                },
            );

            // Timestamps (as Option)
            fields.insert("modified".to_string(), make_timestamp_option(meta.modified()));
            fields.insert("created".to_string(), make_timestamp_option(meta.created()));
            fields.insert("accessed".to_string(), make_timestamp_option(meta.accessed()));

            // Permissions (Unix mode)
            #[cfg(unix)]
            {
                use std::os::unix::fs::PermissionsExt;
                fields.insert(
                    "permissions".to_string(),
                    Value::Int(meta.permissions().mode() as i64),
                );
            }
            #[cfg(not(unix))]
            {
                fields.insert("permissions".to_string(), Value::Int(0o644));
            }

            Ok(io_ok(Value::Object {
                class: "FileMetadata".to_string(),
                fields,
            }))
        }
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_fs_read_dir(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;

    match std::fs::read_dir(&path) {
        Ok(entries) => {
            let mut dir_entries = Vec::new();
            for entry in entries.flatten() {
                let mut fields = HashMap::new();
                fields.insert(
                    "path".to_string(),
                    Value::Str(entry.path().to_string_lossy().to_string()),
                );
                fields.insert(
                    "name".to_string(),
                    Value::Str(entry.file_name().to_string_lossy().to_string()),
                );

                // Determine file type
                let ft = entry.file_type().ok();
                let file_type = match ft {
                    Some(t) if t.is_file() => "File",
                    Some(t) if t.is_dir() => "Directory",
                    Some(t) if t.is_symlink() => "Symlink",
                    _ => "Other",
                };
                fields.insert(
                    "file_type".to_string(),
                    Value::Enum {
                        enum_name: "FileType".to_string(),
                        variant: file_type.to_string(),
                        payload: None,
                    },
                );

                dir_entries.push(Value::Object {
                    class: "DirEntry".to_string(),
                    fields,
                });
            }

            // Return DirEntries struct
            let mut result_fields = HashMap::new();
            result_fields.insert("entries".to_string(), Value::Array(dir_entries));
            result_fields.insert("index".to_string(), Value::Int(0));

            Ok(io_ok(Value::Object {
                class: "DirEntries".to_string(),
                fields: result_fields,
            }))
        }
        Err(e) => Ok(io_err(e)),
    }
}

//==============================================================================
// File Handle Operations
//==============================================================================

pub fn native_fs_open(args: &[Value]) -> Result<Value, CompileError> {
    let path = extract_path(args, 0)?;
    let mode = extract_open_mode(args, 1)?;

    let mut opts = OpenOptions::new();

    match mode.as_str() {
        "Read" => {
            opts.read(true);
        }
        "Write" => {
            opts.write(true).create(true).truncate(true);
        }
        "Append" => {
            opts.append(true).create(true);
        }
        "ReadWrite" => {
            opts.read(true).write(true);
        }
        "Create" => {
            opts.write(true).create(true);
        }
        "CreateNew" => {
            opts.write(true).create_new(true);
        }
        "Truncate" => {
            opts.write(true).truncate(true);
        }
        _ => return Ok(io_err_msg(&format!("unknown open mode: {}", mode))),
    }

    match opts.open(&path) {
        Ok(file) => {
            let handle = allocate_handle(file);
            Ok(io_ok(Value::Int(handle)))
        }
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_file_read(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0)?;
    let len = extract_int(args, 2).unwrap_or(4096) as usize;

    match with_handle(handle, |file| {
        let mut buf = vec![0u8; len];
        let n = file.read(&mut buf)?;
        buf.truncate(n);
        Ok(buf)
    }) {
        Ok(bytes) => {
            let arr: Vec<Value> = bytes.into_iter().map(|b| Value::Int(b as i64)).collect();
            Ok(io_ok(Value::Int(arr.len() as i64)))
        }
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_file_write(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0)?;
    let data = extract_bytes(args, 1)?;

    match with_handle(handle, |file| {
        file.write_all(&data)?;
        Ok(data.len())
    }) {
        Ok(n) => Ok(io_ok(Value::Int(n as i64))),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_file_flush(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0)?;

    match with_handle(handle, |file| file.flush()) {
        Ok(()) => Ok(io_ok(Value::Nil)),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_file_seek(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0)?;

    // Extract SeekFrom enum
    let seek_from = match args.get(1) {
        Some(Value::Enum {
            variant, payload, ..
        }) => {
            let pos = payload
                .as_ref()
                .and_then(|p| p.as_int().ok())
                .unwrap_or(0);
            match variant.as_str() {
                "Start" => SeekFrom::Start(pos as u64),
                "End" => SeekFrom::End(pos),
                "Current" => SeekFrom::Current(pos),
                _ => return Ok(io_err_msg("invalid SeekFrom variant")),
            }
        }
        _ => return Ok(io_err_msg("seek requires SeekFrom enum")),
    };

    match with_handle(handle, |file| file.seek(seek_from)) {
        Ok(pos) => Ok(io_ok(Value::Int(pos as i64))),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_file_sync(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0)?;

    match with_handle(handle, |file| file.sync_all()) {
        Ok(()) => Ok(io_ok(Value::Nil)),
        Err(e) => Ok(io_err(e)),
    }
}

pub fn native_file_close(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0)?;

    if release_handle(handle) {
        Ok(io_ok(Value::Nil))
    } else {
        Ok(io_err(io::Error::new(
            ErrorKind::InvalidInput,
            "invalid file handle",
        )))
    }
}

//==============================================================================
// Terminal Operations
//==============================================================================

pub fn native_stdin(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0)) // stdin handle is always 0
}

pub fn native_stdout(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(1)) // stdout handle is always 1
}

pub fn native_stderr(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(2)) // stderr handle is always 2
}

pub fn native_is_tty(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(1);

    #[cfg(unix)]
    {
        use std::os::unix::io::AsRawFd;
        let is_tty = match handle {
            0 => unsafe { libc::isatty(std::io::stdin().as_raw_fd()) != 0 },
            1 => unsafe { libc::isatty(std::io::stdout().as_raw_fd()) != 0 },
            2 => unsafe { libc::isatty(std::io::stderr().as_raw_fd()) != 0 },
            _ => false,
        };
        Ok(Value::Bool(is_tty))
    }

    #[cfg(not(unix))]
    {
        // On Windows, assume TTY for standard handles
        Ok(Value::Bool(handle >= 0 && handle <= 2))
    }
}

#[cfg(unix)]
pub fn native_enable_raw_mode(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(0);

    if handle != 0 {
        return Ok(Value::Int(-2)); // Not stdin
    }

    use std::os::unix::io::AsRawFd;
    let fd = std::io::stdin().as_raw_fd();

    unsafe {
        let mut termios: libc::termios = std::mem::zeroed();
        if libc::tcgetattr(fd, &mut termios) != 0 {
            return Ok(Value::Int(-1));
        }

        // Save original termios
        ORIGINAL_TERMIOS.with(|orig| {
            *orig.borrow_mut() = Some(termios);
        });

        // Disable canonical mode and echo
        termios.c_lflag &= !(libc::ICANON | libc::ECHO | libc::ISIG | libc::IEXTEN);
        termios.c_iflag &= !(libc::IXON | libc::ICRNL | libc::BRKINT | libc::INPCK | libc::ISTRIP);
        termios.c_oflag &= !libc::OPOST;
        termios.c_cflag |= libc::CS8;
        termios.c_cc[libc::VMIN] = 1;
        termios.c_cc[libc::VTIME] = 0;

        if libc::tcsetattr(fd, libc::TCSAFLUSH, &termios) != 0 {
            return Ok(Value::Int(-1));
        }
    }

    Ok(Value::Int(0))
}

#[cfg(not(unix))]
pub fn native_enable_raw_mode(_args: &[Value]) -> Result<Value, CompileError> {
    // Windows raw mode not implemented yet
    Ok(Value::Int(-2))
}

#[cfg(unix)]
pub fn native_disable_raw_mode(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(0);

    if handle != 0 {
        return Ok(Value::Int(-2));
    }

    use std::os::unix::io::AsRawFd;
    let fd = std::io::stdin().as_raw_fd();

    ORIGINAL_TERMIOS.with(|orig| {
        if let Some(termios) = *orig.borrow() {
            unsafe {
                if libc::tcsetattr(fd, libc::TCSAFLUSH, &termios) != 0 {
                    return Ok(Value::Int(-1));
                }
            }
            *orig.borrow_mut() = None;
        }
        Ok(Value::Int(0))
    })
}

#[cfg(not(unix))]
pub fn native_disable_raw_mode(_args: &[Value]) -> Result<Value, CompileError> {
    Ok(Value::Int(0))
}

#[cfg(unix)]
pub fn native_get_term_size(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(1);

    use std::os::unix::io::AsRawFd;
    let fd = match handle {
        0 => std::io::stdin().as_raw_fd(),
        1 => std::io::stdout().as_raw_fd(),
        2 => std::io::stderr().as_raw_fd(),
        _ => return Ok(Value::Int(-2)),
    };

    unsafe {
        let mut winsize: libc::winsize = std::mem::zeroed();
        if libc::ioctl(fd, libc::TIOCGWINSZ, &mut winsize) != 0 {
            return Ok(Value::Int(-1));
        }

        // Return as tuple (rows, cols)
        Ok(Value::Array(vec![
            Value::Int(winsize.ws_row as i64),
            Value::Int(winsize.ws_col as i64),
        ]))
    }
}

#[cfg(not(unix))]
pub fn native_get_term_size(_args: &[Value]) -> Result<Value, CompileError> {
    // Default size for non-Unix
    Ok(Value::Array(vec![Value::Int(24), Value::Int(80)]))
}

pub fn native_term_write(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(1);

    // Get data - can be string or bytes with pointer/len
    let data = if let Some(Value::Str(s)) = args.get(1) {
        s.as_bytes().to_vec()
    } else {
        // For ptr/len style calls, we just write to stdout/stderr directly
        let s = args
            .get(1)
            .map(|v| v.to_display_string())
            .unwrap_or_default();
        s.into_bytes()
    };

    let result = match handle {
        1 => std::io::stdout().write_all(&data),
        2 => std::io::stderr().write_all(&data),
        _ => return Ok(Value::Int(-2)),
    };

    match result {
        Ok(()) => Ok(Value::Int(data.len() as i64)),
        Err(e) => Ok(Value::Int(-(e.raw_os_error().unwrap_or(1) as i64))),
    }
}

pub fn native_term_read(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(0);
    let len = extract_int(args, 2).unwrap_or(1) as usize;

    if handle != 0 {
        return Ok(Value::Int(-2)); // Can only read from stdin
    }

    let mut buffer = vec![0u8; len];
    match std::io::stdin().read(&mut buffer) {
        Ok(n) => Ok(Value::Int(n as i64)),
        Err(e) => Ok(Value::Int(-(e.raw_os_error().unwrap_or(1) as i64))),
    }
}

#[cfg(unix)]
fn poll_stdin(timeout_ms: i32) -> Result<i32, i32> {
    use std::os::unix::io::AsRawFd;
    let fd = std::io::stdin().as_raw_fd();
    
    unsafe {
        let mut pfd = libc::pollfd {
            fd,
            events: libc::POLLIN,
            revents: 0,
        };
        
        let ret = libc::poll(&mut pfd, 1, timeout_ms);
        if ret < 0 {
            Err(-1)
        } else {
            Ok(ret)
        }
    }
}

#[cfg(unix)]
pub fn native_term_read_timeout(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(0);
    let len = extract_int(args, 2).unwrap_or(1) as usize;
    let timeout_ms = extract_int(args, 3).unwrap_or(1000) as i32;

    if handle != 0 {
        return Ok(Value::Int(-2));
    }

    match poll_stdin(timeout_ms) {
        Err(code) => Ok(Value::Int(code as i64)),
        Ok(0) => Ok(Value::Int(-3)), // Timeout
        Ok(_) => {
            let mut buffer = vec![0u8; len];
            match std::io::stdin().read(&mut buffer) {
                Ok(n) => Ok(Value::Int(n as i64)),
                Err(e) => Ok(Value::Int(-(e.raw_os_error().unwrap_or(1) as i64))),
            }
        }
    }
}

#[cfg(not(unix))]
pub fn native_term_read_timeout(args: &[Value]) -> Result<Value, CompileError> {
    // Fall back to blocking read on non-Unix
    native_term_read(args)
}

pub fn native_term_flush(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(1);

    let result = match handle {
        1 => std::io::stdout().flush(),
        2 => std::io::stderr().flush(),
        _ => return Ok(Value::Int(-2)),
    };

    match result {
        Ok(()) => Ok(Value::Int(0)),
        Err(e) => Ok(Value::Int(-(e.raw_os_error().unwrap_or(1) as i64))),
    }
}

#[cfg(unix)]
pub fn native_term_poll(args: &[Value]) -> Result<Value, CompileError> {
    let handle = extract_int(args, 0).unwrap_or(0);
    let timeout_ms = extract_int(args, 1).unwrap_or(0) as i32;

    if handle != 0 {
        return Ok(Value::Int(-2));
    }

    match poll_stdin(timeout_ms) {
        Err(code) => Ok(Value::Int(code as i64)),
        Ok(ret) => Ok(Value::Int(if ret > 0 { 1 } else { 0 })),
    }
}

#[cfg(not(unix))]
pub fn native_term_poll(_args: &[Value]) -> Result<Value, CompileError> {
    // On non-Unix, assume input is always available
    Ok(Value::Int(1))
}
