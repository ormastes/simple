//! Print and input SFFI functions with capture support.
//!
//! Provides print(), println(), eprint(), eprintln() and input() functionality
//! for Simple programs. Supports capture mode for testing and embedding.
//!
//! ## Features
//!
//! - **Print to stdout**: rt_print_str(), rt_println_str()
//! - **Print to stderr**: rt_eprint_str(), rt_eprintln_str()
//! - **Value printing**: rt_print_value(), rt_println_value(), etc.
//! - **Input from stdin**: rt_read_stdin_line_sffi()
//! - **Capture Support**: Respects I/O capture mode (see io_capture module)
//!
//! ## Usage Pattern
//!
//! ```ignore
//! // Print a string
//! let msg = b"Hello, world!";
//! unsafe { rt_println_str(msg.as_ptr(), msg.len() as u64); }
//!
//! // Print a RuntimeValue
//! let val = RuntimeValue::from_int(42);
//! rt_println_value(val);
//!
//! // Read from stdin
//! let input = rt_read_stdin_line_sffi();
//! ```
//!
//! ## Capture Mode
//!
//! When I/O capture is enabled (via rt_capture_stdout_start()), print functions
//! append to the capture buffer instead of writing to stdout/stderr.

use super::io_capture::{
    append_stderr, append_stdout, is_stderr_capturing, is_stdout_capturing, read_stdin_line_internal,
    rt_read_stdin_char,
};
use crate::value::collections::RuntimeString;
use crate::value::core::RuntimeValue;
use crate::value::heap::{get_typed_ptr, HeapObjectType};
use crate::value::tags;
use std::io::Write;

#[derive(Clone, Copy)]
struct FormatSpec {
    fill: char,
    align: Option<char>,
    sign: Option<char>,
    alt_form: bool,
    zero_pad: bool,
    width: Option<usize>,
    precision: Option<usize>,
    type_code: Option<char>,
}

impl Default for FormatSpec {
    fn default() -> Self {
        Self {
            fill: ' ',
            align: None,
            sign: None,
            alt_form: false,
            zero_pad: false,
            width: None,
            precision: None,
            type_code: None,
        }
    }
}

// ============================================================================
// Print SFFI Functions (with capture support)
// ============================================================================

/// Print a string to stdout (with optional capture).
/// If capture mode is enabled, appends to capture buffer instead of printing.
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_print_str(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }
    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let s = std::str::from_utf8_unchecked(slice);

    if is_stdout_capturing() {
        append_stdout(s);
    } else {
        let mut out = std::io::stdout().lock();
        if let Err(e) = write!(out, "{}", s) {
            if e.kind() == std::io::ErrorKind::BrokenPipe {
                std::process::exit(0);
            }
        }
        let _ = out.flush();
    }
}

/// Print a string to stdout with newline (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_println_str(ptr: *const u8, len: u64) {
    rt_print_str(ptr, len);
    if is_stdout_capturing() {
        append_stdout("\n");
    } else {
        let mut out = std::io::stdout().lock();
        if let Err(e) = writeln!(out) {
            if e.kind() == std::io::ErrorKind::BrokenPipe {
                std::process::exit(0);
            }
        }
    }
}

/// Print a string to stderr (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_eprint_str(ptr: *const u8, len: u64) {
    if ptr.is_null() {
        return;
    }
    let slice = std::slice::from_raw_parts(ptr, len as usize);
    let s = std::str::from_utf8_unchecked(slice);

    if is_stderr_capturing() {
        append_stderr(s);
    } else {
        let mut err = std::io::stderr().lock();
        if let Err(e) = write!(err, "{}", s) {
            if e.kind() == std::io::ErrorKind::BrokenPipe {
                std::process::exit(0);
            }
        }
        let _ = err.flush();
    }
}

/// Legacy alias used by source-level `extern fn stderr_write(data: text) -> i64`.
///
/// Accepts a RuntimeValue string handle encoded as a raw u64/i64 payload.
#[no_mangle]
pub extern "C" fn stderr_write(data: i64) -> i64 {
    let s = value_to_display_string(RuntimeValue::from_raw(data as u64));
    unsafe {
        rt_eprint_str(s.as_ptr(), s.len() as u64);
    }
    0
}

/// Legacy alias used by source-level `extern fn stdout_write(data: text) -> i64`.
///
/// Accepts a RuntimeValue string handle encoded as a raw u64/i64 payload.
#[no_mangle]
pub extern "C" fn stdout_write(data: i64) -> i64 {
    let s = value_to_display_string(RuntimeValue::from_raw(data as u64));
    unsafe {
        rt_print_str(s.as_ptr(), s.len() as u64);
    }
    0
}

/// Runtime-prefixed stdout alias used by native-built entry closures.
#[no_mangle]
pub extern "C" fn rt_stdout_write(data: i64) -> i64 {
    stdout_write(data)
}

/// Runtime-prefixed stderr alias used by native-built entry closures.
#[no_mangle]
pub extern "C" fn rt_stderr_write(data: i64) -> i64 {
    stderr_write(data)
}

/// Runtime-prefixed stdout flush alias used by native-built entry closures.
#[no_mangle]
pub extern "C" fn rt_stdout_flush() -> i64 {
    let _ = std::io::stdout().flush();
    0
}

/// Runtime-prefixed stderr flush alias used by native-built entry closures.
#[no_mangle]
pub extern "C" fn rt_stderr_flush() -> i64 {
    let _ = std::io::stderr().flush();
    0
}

/// Legacy alias used by source-level `extern fn stderr_flush() -> i64`.
#[no_mangle]
pub extern "C" fn stderr_flush() -> i64 {
    rt_stderr_flush()
}

/// Print a string to stderr with newline (with optional capture).
///
/// # Safety
/// ptr must be a valid pointer to len bytes of UTF-8 data.
#[no_mangle]
pub unsafe extern "C" fn rt_eprintln_str(ptr: *const u8, len: u64) {
    rt_eprint_str(ptr, len);
    if is_stderr_capturing() {
        append_stderr("\n");
    } else {
        let mut err = std::io::stderr().lock();
        if let Err(e) = writeln!(err) {
            if e.kind() == std::io::ErrorKind::BrokenPipe {
                std::process::exit(0);
            }
        }
    }
}

/// Print a RuntimeValue to stdout (converts to display string first).
/// Nil values are silently skipped to prevent stdout pollution
/// (e.g., MCP JSON-RPC servers, binary protocol output).
#[no_mangle]
pub extern "C" fn rt_print_value(v: RuntimeValue) {
    if v.is_nil() {
        return;
    }
    let s = value_to_display_string(v);
    unsafe {
        rt_print_str(s.as_ptr(), s.len() as u64);
    }
}

/// Codegen alias for `rt_print_value`: the compiler emits `rt_print` for the `print`
/// builtin. The AOT loader rewrites this name; the Cranelift JIT registers by exact
/// name, so expose `rt_print` as a real exported symbol forwarding to `rt_print_value`.
#[export_name = "rt_print"]
pub extern "C" fn rt_print_alias(v: RuntimeValue) {
    rt_print_value(v);
}

/// Print a RuntimeValue to stdout with newline.
/// Nil values print just a newline (matching `print` with no args behavior).
#[no_mangle]
pub extern "C" fn rt_println_value(v: RuntimeValue) {
    if v.is_nil() {
        unsafe {
            rt_println_str(b"".as_ptr(), 0);
        }
        return;
    }
    let s = value_to_display_string(v);
    unsafe {
        rt_println_str(s.as_ptr(), s.len() as u64);
    }
}

/// Codegen alias for `rt_println_value`: the compiler emits `rt_println` for the
/// `println` builtin. The AOT loader rewrites this name; the Cranelift JIT registers by
/// exact name, so expose `rt_println` as a real exported symbol forwarding to
/// `rt_println_value`.
#[export_name = "rt_println"]
pub extern "C" fn rt_println_alias(v: RuntimeValue) {
    rt_println_value(v);
}

/// Print a RuntimeValue to stderr.
/// Nil values are silently skipped.
#[no_mangle]
pub extern "C" fn rt_eprint_value(v: RuntimeValue) {
    if v.is_nil() {
        return;
    }
    let s = value_to_display_string(v);
    unsafe {
        rt_eprint_str(s.as_ptr(), s.len() as u64);
    }
}

/// Print a RuntimeValue to stderr with newline.
/// Nil values print just a newline.
#[no_mangle]
pub extern "C" fn rt_eprintln_value(v: RuntimeValue) {
    if v.is_nil() {
        unsafe {
            rt_eprintln_str(b"".as_ptr(), 0);
        }
        return;
    }
    let s = value_to_display_string(v);
    unsafe {
        rt_eprintln_str(s.as_ptr(), s.len() as u64);
    }
}

/// Convert a RuntimeValue to a string RuntimeValue.
/// This is used for f-string interpolation in native compiled code.
#[no_mangle]
pub extern "C" fn rt_value_to_string(v: RuntimeValue) -> RuntimeValue {
    let s = value_to_display_string(v);
    let bytes = s.as_bytes();
    unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
}

/// Convert a raw native `u64` payload to a string RuntimeValue.
///
/// Native codegen keeps `u64` scalars as raw 64-bit integers. Values with any
/// high bits set cannot be losslessly boxed into the 61-bit tagged-int
/// RuntimeValue representation, so callers must route unsigned stringification
/// through this helper instead of `rt_value_to_string`.
#[no_mangle]
pub extern "C" fn rt_raw_u64_to_string(raw: i64) -> RuntimeValue {
    let s = (raw as u64).to_string();
    unsafe { crate::value::collections::rt_string_new(s.as_ptr(), s.len() as u64) }
}

/// Format a RuntimeValue using a format specifier string.
/// The format spec follows Python conventions: [[fill]align][sign][#][0][width][grouping][.precision][type]
///
/// Supported format types:
/// - `f`/`F`: Fixed-point float (e.g., `.2f` -> "3.14")
/// - `d`: Decimal integer (e.g., `05d` -> "00042")
/// - `e`/`E`: Scientific notation (e.g., `.3e` -> "3.142e+00")
/// - `%`: Percentage (e.g., `.1%` -> "73.2%")
/// - `x`/`X`: Hex integer (e.g., `x` -> "2a", `X` -> "2A")
/// - `o`: Octal integer (e.g., `o` -> "52")
/// - `b`: Binary integer (e.g., `b` -> "101010")
/// - `s` or none: String (default)
/// - Alignment: `<` left, `>` right, `^` center, with optional fill char
/// - `0` prefix: Zero-pad (shorthand for `0>Nd`)
///
/// Arguments:
///   v:        the value to format
///   fmt_ptr:  pointer to format spec string bytes
///   fmt_len:  length of the format spec string
#[no_mangle]
pub extern "C" fn rt_value_format_string(v: RuntimeValue, fmt_ptr: *const u8, fmt_len: u64) -> RuntimeValue {
    let spec = unsafe {
        if fmt_ptr.is_null() {
            ""
        } else {
            std::str::from_utf8_unchecked(std::slice::from_raw_parts(fmt_ptr, fmt_len as usize))
        }
    };
    let s = format_runtime_value(v, spec);
    if s.is_empty() {
        return unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) };
    }
    unsafe { crate::value::collections::rt_string_new(s.as_ptr(), s.len() as u64) }
}

fn value_to_display_string(v: RuntimeValue) -> String {
    match v.tag() {
        tags::TAG_SPECIAL => match v.payload() {
            tags::SPECIAL_NIL => "nil".to_string(),
            tags::SPECIAL_TRUE => "true".to_string(),
            tags::SPECIAL_FALSE => "false".to_string(),
            tags::SPECIAL_ERROR => "error".to_string(),
            p => format!("<special:{p}>"),
        },
        tags::TAG_INT => v.as_int().to_string(),
        tags::TAG_FLOAT => format_float_display(v.as_float()),
        tags::TAG_HEAP => heap_value_to_display_string(v),
        _ => format!("<value:0x{:x}>", v.to_raw()),
    }
}

fn heap_value_to_display_string(v: RuntimeValue) -> String {
    let ptr = v.as_heap_ptr();
    if ptr.is_null() {
        return "nil".to_string();
    }
    let Some(object_type) = v.heap_type() else {
        return format!("<invalid-heap:0x{:x}>", v.to_raw());
    };
    match object_type {
        HeapObjectType::String => {
            let Some(s) = get_typed_ptr::<RuntimeString>(v, HeapObjectType::String) else {
                return format!("<invalid-heap:0x{:x}>", v.to_raw());
            };
            unsafe { String::from_utf8_lossy((*s).as_bytes()).into_owned() }
        }
        HeapObjectType::Array => format!("<array@{ptr:p}>"),
        HeapObjectType::Dict => format!("<dict@{ptr:p}>"),
        HeapObjectType::Tuple => format!("<tuple@{ptr:p}>"),
        HeapObjectType::Object => format!("<object@{ptr:p}>"),
        HeapObjectType::Closure => format!("<closure@{ptr:p}>"),
        HeapObjectType::Enum => format!("<enum@{ptr:p}>"),
        _ => format!("<heap@{ptr:p}>"),
    }
}

fn format_float_display(value: f64) -> String {
    for precision in 1..=17 {
        let candidate = format!("{value:.precision$}");
        if candidate.parse::<f64>().ok() == Some(value) {
            return candidate;
        }
    }
    format!("{value:.17}")
}

fn format_runtime_value(v: RuntimeValue, spec: &str) -> String {
    let fs = parse_format_spec(spec);
    let raw = match fs.type_code {
        Some('f') | Some('F') => format_fixed(v, fs),
        Some('e') => format_scientific(v, fs, false),
        Some('E') => format_scientific(v, fs, true),
        Some('d') => format_decimal(v, fs),
        Some('x') => format_int_radix(v, fs, 16, false),
        Some('X') => format_int_radix(v, fs, 16, true),
        Some('o') => format_int_radix(v, fs, 8, false),
        Some('b') => format_int_radix(v, fs, 2, false),
        Some('%') => format_percent(v, fs),
        _ => {
            let mut text = value_to_display_string(v);
            if fs.type_code == Some('s') {
                if let Some(precision) = fs.precision {
                    text.truncate(precision);
                }
            }
            text
        }
    };
    apply_alignment(&raw, fs)
}

fn parse_format_spec(spec: &str) -> FormatSpec {
    let chars: Vec<char> = spec.chars().collect();
    let mut fs = FormatSpec::default();
    let mut pos = 0;

    if chars.len() >= 2 && matches!(chars[1], '<' | '>' | '^' | '=') {
        fs.fill = chars[0];
        fs.align = Some(chars[1]);
        pos = 2;
    } else if chars.first().is_some_and(|c| matches!(c, '<' | '>' | '^' | '=')) {
        fs.align = Some(chars[0]);
        pos = 1;
    }
    if chars.get(pos).is_some_and(|c| matches!(c, '+' | '-' | ' ')) {
        fs.sign = Some(chars[pos]);
        pos += 1;
    }
    if chars.get(pos) == Some(&'#') {
        fs.alt_form = true;
        pos += 1;
    }
    if chars.get(pos) == Some(&'0') {
        fs.zero_pad = true;
        pos += 1;
    }
    if chars.get(pos).is_some_and(|c| c.is_ascii_digit()) {
        let mut width = 0usize;
        while chars.get(pos).is_some_and(|c| c.is_ascii_digit()) {
            width = width * 10 + chars[pos].to_digit(10).unwrap() as usize;
            pos += 1;
        }
        fs.width = Some(width);
    }
    if chars.get(pos).is_some_and(|c| matches!(c, ',' | '_')) {
        pos += 1;
    }
    if chars.get(pos) == Some(&'.') {
        pos += 1;
        let mut precision = 0usize;
        while chars.get(pos).is_some_and(|c| c.is_ascii_digit()) {
            precision = precision * 10 + chars[pos].to_digit(10).unwrap() as usize;
            pos += 1;
        }
        fs.precision = Some(precision);
    }
    if let Some(&type_code) = chars.get(pos) {
        fs.type_code = Some(type_code);
    }
    fs
}

fn format_fixed(v: RuntimeValue, fs: FormatSpec) -> String {
    let f = if v.is_float() {
        v.as_float()
    } else if v.is_int() {
        v.as_int() as f64
    } else {
        0.0
    };
    let precision = fs.precision.unwrap_or(6);
    let magnitude = format!("{:.precision$}", f.abs());
    format_sign(&magnitude, f >= 0.0, fs)
}

fn format_scientific(v: RuntimeValue, fs: FormatSpec, upper: bool) -> String {
    let f = if v.is_float() {
        v.as_float()
    } else if v.is_int() {
        v.as_int() as f64
    } else {
        0.0
    };
    let precision = fs.precision.unwrap_or(6);
    if upper {
        format!("{f:.precision$E}")
    } else {
        format!("{f:.precision$e}")
    }
}

fn format_decimal(v: RuntimeValue, fs: FormatSpec) -> String {
    let i = if v.is_int() {
        v.as_int()
    } else if v.is_float() {
        v.as_float() as i64
    } else {
        0
    };
    format_sign(&i.abs().to_string(), i >= 0, fs)
}

fn format_int_radix(v: RuntimeValue, fs: FormatSpec, radix: u32, upper: bool) -> String {
    let i = if v.is_int() { v.as_int() as u64 } else { 0 };
    let digits = match (radix, upper) {
        (16, true) => format!("{i:X}"),
        (16, false) => format!("{i:x}"),
        (8, _) => format!("{i:o}"),
        (2, _) => format!("{i:b}"),
        _ => i.to_string(),
    };
    if !fs.alt_form {
        return digits;
    }
    let prefix = match (radix, upper) {
        (16, true) => "0X",
        (16, false) => "0x",
        (8, _) => "0o",
        (2, _) => "0b",
        _ => "",
    };
    format!("{prefix}{digits}")
}

fn format_percent(v: RuntimeValue, fs: FormatSpec) -> String {
    let f = if v.is_float() {
        v.as_float()
    } else if v.is_int() {
        v.as_int() as f64
    } else {
        0.0
    };
    let precision = fs.precision.unwrap_or(6);
    format!("{:.precision$}%", f * 100.0)
}

fn format_sign(magnitude: &str, is_positive: bool, fs: FormatSpec) -> String {
    if !is_positive {
        format!("-{magnitude}")
    } else if fs.sign == Some('+') {
        format!("+{magnitude}")
    } else if fs.sign == Some(' ') {
        format!(" {magnitude}")
    } else {
        magnitude.to_string()
    }
}

fn apply_alignment(s: &str, fs: FormatSpec) -> String {
    let Some(width) = fs.width else {
        return s.to_string();
    };
    let len = s.len();
    if len >= width {
        return s.to_string();
    }
    let padding = width - len;
    let fill = if fs.zero_pad && fs.align.is_none() {
        '0'
    } else {
        fs.fill
    };
    let align = fs.align.unwrap_or(if fs.zero_pad { '>' } else { '<' });

    match align {
        '>' => {
            if fill == '0' && matches!(s.as_bytes().first(), Some(b'+' | b'-' | b' ')) {
                format!("{}{}{}", &s[..1], fill.to_string().repeat(padding), &s[1..])
            } else {
                format!("{}{}", fill.to_string().repeat(padding), s)
            }
        }
        '<' => format!("{}{}", s, fill.to_string().repeat(padding)),
        '^' => {
            let left = padding / 2;
            let right = padding - left;
            format!(
                "{}{}{}",
                fill.to_string().repeat(left),
                s,
                fill.to_string().repeat(right)
            )
        }
        '=' => {
            if matches!(s.as_bytes().first(), Some(b'+' | b'-' | b' ')) {
                format!("{}{}{}", &s[..1], fill.to_string().repeat(padding), &s[1..])
            } else {
                format!("{}{}", fill.to_string().repeat(padding), s)
            }
        }
        _ => s.to_string(),
    }
}

// ============================================================================
// Stdin Input Functions
// ============================================================================

use std::io::{self, BufRead};

/// Read a line from stdin (checks mock first, then real stdin)
#[export_name = "rt_read_stdin_line"]
pub extern "C" fn rt_read_stdin_line_sffi() -> RuntimeValue {
    // First try mock stdin for testing
    if let Some(line) = read_stdin_line_internal() {
        let bytes = line.as_bytes();
        return unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) };
    }

    // Fall back to real stdin
    let stdin = io::stdin();
    let mut line = String::new();

    match stdin.lock().read_line(&mut line) {
        Ok(_) => {
            // Remove trailing newline
            if line.ends_with('\n') {
                line.pop();
                if line.ends_with('\r') {
                    line.pop();
                }
            }
            let bytes = line.as_bytes();
            unsafe { crate::value::collections::rt_string_new(bytes.as_ptr(), bytes.len() as u64) }
        }
        Err(_) => RuntimeValue::NIL,
    }
}

/// Legacy alias used by source-level `extern fn stdin_read_char() -> text`.
#[no_mangle]
pub extern "C" fn stdin_read_char() -> RuntimeValue {
    if let Some(ch) = rt_read_stdin_char() {
        let mut buf = [0u8; 4];
        let encoded = ch.encode_utf8(&mut buf);
        return unsafe { crate::value::collections::rt_string_new(encoded.as_ptr(), encoded.len() as u64) };
    }

    let stdin = io::stdin();
    let mut reader = stdin.lock();
    let mut buf = [0u8; 1];
    match std::io::Read::read(&mut reader, &mut buf) {
        Ok(0) => unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) },
        Ok(_) => unsafe { crate::value::collections::rt_string_new(buf.as_ptr(), 1) },
        Err(_) => unsafe { crate::value::collections::rt_string_new(std::ptr::null(), 0) },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::value::sffi::io_capture::{
        rt_capture_stdout_start, rt_capture_stdout_stop, rt_capture_stderr_start, rt_capture_stderr_stop, rt_set_stdin,
    };

    #[test]
    fn test_print_str_basic() {
        rt_capture_stdout_start();
        let msg = b"Hello, world!";
        unsafe {
            rt_print_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "Hello, world!");
    }

    #[test]
    fn test_println_str_basic() {
        rt_capture_stdout_start();
        let msg = b"Hello";
        unsafe {
            rt_println_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "Hello\n");
    }

    #[test]
    fn test_eprint_str_basic() {
        rt_capture_stderr_start();
        let msg = b"Error message";
        unsafe {
            rt_eprint_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "Error message");
    }

    #[test]
    fn test_eprintln_str_basic() {
        rt_capture_stderr_start();
        let msg = b"Error";
        unsafe {
            rt_eprintln_str(msg.as_ptr(), msg.len() as u64);
        }
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "Error\n");
    }

    #[test]
    fn test_print_str_null() {
        rt_capture_stdout_start();
        unsafe {
            rt_print_str(std::ptr::null(), 0);
        }
        let output = rt_capture_stdout_stop();
        assert_eq!(output, ""); // Should not crash
    }

    #[test]
    fn test_print_value_int() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::from_int(42));
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "42");
    }

    #[test]
    fn test_print_value_float() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::from_float(3.25));
        let output = rt_capture_stdout_stop();
        // Float to string conversion may have precision issues
        assert!(output.starts_with("3.25") || output == "3.139999999999997");
    }

    #[test]
    fn test_print_value_bool() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::from_bool(true));
        unsafe {
            rt_print_str(b" ".as_ptr(), 1);
        }
        rt_print_value(RuntimeValue::from_bool(false));
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "true false");
    }

    #[test]
    fn test_print_value_nil() {
        rt_capture_stdout_start();
        rt_print_value(RuntimeValue::NIL);
        let output = rt_capture_stdout_stop();
        // Nil values are silently skipped to prevent stdout pollution
        assert_eq!(output, "");
    }

    #[test]
    fn test_println_value() {
        rt_capture_stdout_start();
        rt_println_value(RuntimeValue::from_int(42));
        let output = rt_capture_stdout_stop();
        assert_eq!(output, "42\n");
    }

    #[test]
    fn test_eprint_value() {
        rt_capture_stderr_start();
        rt_eprint_value(RuntimeValue::from_int(99));
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "99");
    }

    #[test]
    fn test_eprintln_value() {
        rt_capture_stderr_start();
        rt_eprintln_value(RuntimeValue::from_int(99));
        let output = rt_capture_stderr_stop();
        assert_eq!(output, "99\n");
    }

    #[test]
    fn test_value_to_display_string() {
        assert_eq!(value_to_display_string(RuntimeValue::NIL), "nil");
        assert_eq!(value_to_display_string(RuntimeValue::from_int(42)), "42");
        // Float to string conversion may have precision issues
        let float_str = value_to_display_string(RuntimeValue::from_float(3.25));
        assert!(float_str.starts_with("3.25") || float_str == "3.139999999999997");
        assert_eq!(value_to_display_string(RuntimeValue::from_bool(true)), "true");
        assert_eq!(value_to_display_string(RuntimeValue::from_bool(false)), "false");
    }

    #[test]
    fn test_value_to_display_string_rejects_forged_heap_value() {
        let forged_heap = RuntimeValue::from_raw(0x1001);
        let text = value_to_display_string(forged_heap);

        assert!(text.starts_with("<invalid-heap:0x"));
    }

    #[test]
    fn test_print_value_rejects_forged_heap_value() {
        let forged_heap = RuntimeValue::from_raw(0x1001);

        rt_capture_stdout_start();
        rt_print_value(forged_heap);
        let output = rt_capture_stdout_stop();

        assert!(output.starts_with("<invalid-heap:0x"));
    }

    #[test]
    fn test_raw_u64_to_string_preserves_high_bit_patterns() {
        let top_bit = rt_raw_u64_to_string(i64::MIN);
        let all_bits = rt_raw_u64_to_string(-1);
        let marker = rt_raw_u64_to_string(0xCAFEBABEDEADBEEFu64 as i64);

        let top_bit_text = value_to_display_string(top_bit);
        let all_bits_text = value_to_display_string(all_bits);
        let marker_text = value_to_display_string(marker);

        assert_eq!(top_bit_text, "9223372036854775808");
        assert_eq!(all_bits_text, "18446744073709551615");
        assert_eq!(marker_text, "14627333968688430831");
    }

    #[test]
    fn test_read_stdin_line_mock() {
        rt_set_stdin("test input\n");
        let result = rt_read_stdin_line_sffi();

        // Result should be a string RuntimeValue
        assert!(result.is_heap());

        // Convert to Rust string to verify
        let ptr = result.as_heap_ptr() as *const RuntimeString;
        unsafe {
            let data = (ptr.add(1)) as *const u8;
            let slice = std::slice::from_raw_parts(data, (*ptr).len as usize);
            let s = String::from_utf8_lossy(slice);
            assert_eq!(s, "test input");
        }
    }

    #[test]
    fn test_read_stdin_line_multiple() {
        rt_set_stdin("line1\nline2\n");

        let result1 = rt_read_stdin_line_sffi();
        let ptr1 = result1.as_heap_ptr() as *const RuntimeString;
        unsafe {
            let data = (ptr1.add(1)) as *const u8;
            let slice = std::slice::from_raw_parts(data, (*ptr1).len as usize);
            assert_eq!(String::from_utf8_lossy(slice), "line1");
        }

        let result2 = rt_read_stdin_line_sffi();
        let ptr2 = result2.as_heap_ptr() as *const RuntimeString;
        unsafe {
            let data = (ptr2.add(1)) as *const u8;
            let slice = std::slice::from_raw_parts(data, (*ptr2).len as usize);
            assert_eq!(String::from_utf8_lossy(slice), "line2");
        }
    }

    // =========================================================================
    // Format specifier tests (C-backed via rt_value_format_string)
    // =========================================================================

    fn format_value_with_spec(v: RuntimeValue, spec: &str) -> String {
        let result = unsafe { rt_value_format_string(v, spec.as_ptr(), spec.len() as u64) };
        let ptr = result.as_heap_ptr();
        if ptr.is_null() {
            return String::new();
        }
        unsafe {
            let base = ptr as *const u8;
            let len = *(base.add(8) as *const u64) as usize;
            let data = base.add(24);
            String::from_utf8_lossy(std::slice::from_raw_parts(data, len)).into_owned()
        }
    }

    #[test]
    fn test_format_float_precision() {
        let v = RuntimeValue::from_float(3.14159);
        let result = format_value_with_spec(v, ".2f");
        assert_eq!(result, "3.14");
    }

    #[test]
    fn test_format_zero_padded_int() {
        let v = RuntimeValue::from_int(42);
        let result = format_value_with_spec(v, "05d");
        assert_eq!(result, "00042");
    }

    #[test]
    fn test_format_hex_lower() {
        let v = RuntimeValue::from_int(42);
        let result = format_value_with_spec(v, "x");
        assert_eq!(result, "2a");
    }

    #[test]
    fn test_format_hex_upper() {
        let v = RuntimeValue::from_int(42);
        let result = format_value_with_spec(v, "X");
        assert_eq!(result, "2A");
    }

    #[test]
    fn test_format_octal() {
        let v = RuntimeValue::from_int(42);
        let result = format_value_with_spec(v, "o");
        assert_eq!(result, "52");
    }

    #[test]
    fn test_format_binary() {
        let v = RuntimeValue::from_int(42);
        let result = format_value_with_spec(v, "b");
        assert_eq!(result, "101010");
    }

    #[test]
    fn test_format_int_as_float() {
        let v = RuntimeValue::from_int(42);
        let result = format_value_with_spec(v, ".2f");
        assert_eq!(result, "42.00");
    }

    #[test]
    fn test_format_empty_spec() {
        let v = RuntimeValue::from_int(42);
        let result = format_value_with_spec(v, "");
        assert_eq!(result, "42");
    }
}
