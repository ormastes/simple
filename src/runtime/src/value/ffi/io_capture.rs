//! I/O capture system for testing and embedding.
//!
//! Provides thread-local capture of stdout/stderr and mock stdin for testing.
//! When capture mode is enabled, print operations buffer output instead of writing
//! to the actual stdout/stderr streams.
//!
//! ## Features
//!
//! - **Stdout Capture**: Buffer print() output for inspection
//! - **Stderr Capture**: Buffer eprint() output for inspection
//! - **Mock Stdin**: Provide input() data from a string buffer
//! - **Thread-Local**: Each thread has independent capture state
//!
//! ## Usage Pattern
//!
//! ```ignore
//! // Enable capture
//! rt_capture_stdout_start();
//!
//! // Run code that prints
//! // ... code calls rt_print_str() ...
//!
//! // Get captured output
//! let output = rt_capture_stdout_stop();
//! assert_eq!(output, "expected output");
//! ```
//!
//! ## Mock Stdin Usage
//!
//! ```ignore
//! // Set mock stdin
//! rt_set_stdin("line1\nline2\n");
//!
//! // Read from stdin (gets from buffer)
//! let line1 = read_stdin_line_internal(); // Some("line1")
//! let line2 = read_stdin_line_internal(); // Some("line2")
//! let line3 = read_stdin_line_internal(); // None
//! ```

use std::cell::RefCell;

thread_local! {
    /// Captured stdout buffer (when capture mode is enabled)
    static STDOUT_CAPTURE: RefCell<Option<String>> = const { RefCell::new(None) };
    /// Captured stderr buffer (when capture mode is enabled)
    static STDERR_CAPTURE: RefCell<Option<String>> = const { RefCell::new(None) };
    /// Mock stdin buffer (for testing - reads from this instead of real stdin)
    static STDIN_BUFFER: RefCell<Option<String>> = const { RefCell::new(None) };
}

// ============================================================================
// Stdout/Stderr Capture
// ============================================================================

/// Enable stdout capture mode. All print output will be buffered instead of printed.
#[no_mangle]
pub extern "C" fn rt_capture_stdout_start() {
    STDOUT_CAPTURE.with(|buf| {
        *buf.borrow_mut() = Some(String::new());
    });
}

/// Enable stderr capture mode.
#[no_mangle]
pub extern "C" fn rt_capture_stderr_start() {
    STDERR_CAPTURE.with(|buf| {
        *buf.borrow_mut() = Some(String::new());
    });
}

/// Stop stdout capture and return captured content.
/// Returns empty string if capture was not enabled.
pub fn rt_capture_stdout_stop() -> String {
    STDOUT_CAPTURE.with(|buf| buf.borrow_mut().take().unwrap_or_default())
}

/// Stop stderr capture and return captured content.
pub fn rt_capture_stderr_stop() -> String {
    STDERR_CAPTURE.with(|buf| buf.borrow_mut().take().unwrap_or_default())
}

/// Get current captured stdout without stopping capture.
pub fn rt_get_captured_stdout() -> String {
    STDOUT_CAPTURE.with(|buf| buf.borrow().clone().unwrap_or_default())
}

/// Get current captured stderr without stopping capture.
pub fn rt_get_captured_stderr() -> String {
    STDERR_CAPTURE.with(|buf| buf.borrow().clone().unwrap_or_default())
}

/// Clear captured stdout buffer (keep capture mode enabled).
pub fn rt_clear_captured_stdout() {
    STDOUT_CAPTURE.with(|buf| {
        if let Some(ref mut s) = *buf.borrow_mut() {
            s.clear();
        }
    });
}

/// Clear captured stderr buffer (keep capture mode enabled).
pub fn rt_clear_captured_stderr() {
    STDERR_CAPTURE.with(|buf| {
        if let Some(ref mut s) = *buf.borrow_mut() {
            s.clear();
        }
    });
}

/// Check if stdout capture is currently enabled.
pub fn rt_is_stdout_capturing() -> bool {
    STDOUT_CAPTURE.with(|buf| buf.borrow().is_some())
}

/// Check if stderr capture is currently enabled.
pub fn rt_is_stderr_capturing() -> bool {
    STDERR_CAPTURE.with(|buf| buf.borrow().is_some())
}

/// Append to stdout capture buffer if enabled.
/// Used by print functions.
pub(crate) fn append_stdout(s: &str) {
    STDOUT_CAPTURE.with(|buf| {
        if let Some(ref mut capture) = *buf.borrow_mut() {
            capture.push_str(s);
        }
    });
}

/// Append to stderr capture buffer if enabled.
/// Used by eprint functions.
pub(crate) fn append_stderr(s: &str) {
    STDERR_CAPTURE.with(|buf| {
        if let Some(ref mut capture) = *buf.borrow_mut() {
            capture.push_str(s);
        }
    });
}

/// Check if stdout capture is enabled (for print functions to check).
pub(crate) fn is_stdout_capturing() -> bool {
    rt_is_stdout_capturing()
}

/// Check if stderr capture is enabled (for eprint functions to check).
pub(crate) fn is_stderr_capturing() -> bool {
    rt_is_stderr_capturing()
}

// ============================================================================
// Stdin Mock Functions (for testing)
// ============================================================================

/// Set mock stdin content. When set, input() reads from this instead of real stdin.
/// Pass empty string to clear the buffer and revert to real stdin.
pub fn rt_set_stdin(content: &str) {
    STDIN_BUFFER.with(|buf| {
        if content.is_empty() {
            *buf.borrow_mut() = None;
        } else {
            *buf.borrow_mut() = Some(content.to_string());
        }
    });
}

/// Read a line from mock stdin buffer, or None if buffer is empty/not set.
/// Removes the line from the buffer (including the newline).
/// This is a public wrapper for use by other modules.
pub fn rt_read_stdin_line() -> Option<String> {
    read_stdin_line_internal()
}

/// Read a line from mock stdin buffer, or None if buffer is empty/not set.
/// Removes the line from the buffer (including the newline).
pub(crate) fn read_stdin_line_internal() -> Option<String> {
    STDIN_BUFFER.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut content) = *guard {
            if content.is_empty() {
                return None;
            }
            // Find the first newline
            if let Some(pos) = content.find('\n') {
                let line = content[..pos].to_string();
                *content = content[pos + 1..].to_string();
                return Some(line);
            } else {
                // No newline, return entire content and clear
                let line = content.clone();
                content.clear();
                return Some(line);
            }
        }
        None
    })
}

/// Check if mock stdin is currently active.
pub fn rt_has_mock_stdin() -> bool {
    STDIN_BUFFER.with(|buf| buf.borrow().is_some())
}

/// Clear mock stdin buffer.
pub fn rt_clear_stdin() {
    STDIN_BUFFER.with(|buf| {
        *buf.borrow_mut() = None;
    });
}

/// Read a single character from mock stdin buffer, or None if buffer is empty/not set.
pub fn rt_read_stdin_char() -> Option<char> {
    STDIN_BUFFER.with(|buf| {
        let mut guard = buf.borrow_mut();
        if let Some(ref mut content) = *guard {
            if content.is_empty() {
                return None;
            }
            let ch = content.chars().next();
            if ch.is_some() {
                *content = content[ch.unwrap().len_utf8()..].to_string();
            }
            ch
        } else {
            None
        }
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_stdout_capture_basic() {
        rt_capture_stdout_start();
        assert!(rt_is_stdout_capturing());

        append_stdout("hello");
        assert_eq!(rt_get_captured_stdout(), "hello");

        append_stdout(" world");
        assert_eq!(rt_get_captured_stdout(), "hello world");

        let output = rt_capture_stdout_stop();
        assert_eq!(output, "hello world");
        assert!(!rt_is_stdout_capturing());
    }

    #[test]
    fn test_stderr_capture_basic() {
        rt_capture_stderr_start();
        assert!(rt_is_stderr_capturing());

        append_stderr("error");
        assert_eq!(rt_get_captured_stderr(), "error");

        let output = rt_capture_stderr_stop();
        assert_eq!(output, "error");
        assert!(!rt_is_stderr_capturing());
    }

    #[test]
    fn test_stdout_clear() {
        rt_capture_stdout_start();
        append_stdout("test");
        rt_clear_captured_stdout();
        assert_eq!(rt_get_captured_stdout(), "");
        assert!(rt_is_stdout_capturing()); // Still capturing
        rt_capture_stdout_stop();
    }

    #[test]
    fn test_stderr_clear() {
        rt_capture_stderr_start();
        append_stderr("test");
        rt_clear_captured_stderr();
        assert_eq!(rt_get_captured_stderr(), "");
        assert!(rt_is_stderr_capturing()); // Still capturing
        rt_capture_stderr_stop();
    }

    #[test]
    fn test_capture_not_enabled() {
        // When not capturing, should return empty string
        assert_eq!(rt_get_captured_stdout(), "");
        assert_eq!(rt_get_captured_stderr(), "");
        assert!(!rt_is_stdout_capturing());
        assert!(!rt_is_stderr_capturing());
    }

    #[test]
    fn test_mock_stdin_basic() {
        rt_set_stdin("line1\nline2\nline3\n");
        assert!(rt_has_mock_stdin());

        assert_eq!(read_stdin_line_internal(), Some("line1".to_string()));
        assert_eq!(read_stdin_line_internal(), Some("line2".to_string()));
        assert_eq!(read_stdin_line_internal(), Some("line3".to_string()));
        assert_eq!(read_stdin_line_internal(), None);
    }

    #[test]
    fn test_mock_stdin_no_trailing_newline() {
        rt_set_stdin("single line");
        assert_eq!(read_stdin_line_internal(), Some("single line".to_string()));
        assert_eq!(read_stdin_line_internal(), None);
        rt_clear_stdin();
    }

    #[test]
    fn test_mock_stdin_empty() {
        rt_set_stdin("");
        assert!(!rt_has_mock_stdin());
        assert_eq!(read_stdin_line_internal(), None);
    }

    #[test]
    fn test_mock_stdin_clear() {
        rt_set_stdin("test");
        assert!(rt_has_mock_stdin());
        rt_clear_stdin();
        assert!(!rt_has_mock_stdin());
        assert_eq!(read_stdin_line_internal(), None);
    }

    #[test]
    fn test_read_stdin_char() {
        rt_set_stdin("abc");
        assert_eq!(rt_read_stdin_char(), Some('a'));
        assert_eq!(rt_read_stdin_char(), Some('b'));
        assert_eq!(rt_read_stdin_char(), Some('c'));
        assert_eq!(rt_read_stdin_char(), None);
        rt_clear_stdin();
    }

    #[test]
    fn test_read_stdin_char_unicode() {
        rt_set_stdin("日本語");
        assert_eq!(rt_read_stdin_char(), Some('日'));
        assert_eq!(rt_read_stdin_char(), Some('本'));
        assert_eq!(rt_read_stdin_char(), Some('語'));
        assert_eq!(rt_read_stdin_char(), None);
        rt_clear_stdin();
    }

    #[test]
    fn test_multiple_captures_independent() {
        // Test that stopping one capture doesn't affect the other
        rt_capture_stdout_start();
        rt_capture_stderr_start();

        append_stdout("out");
        append_stderr("err");

        let stdout_output = rt_capture_stdout_stop();
        assert_eq!(stdout_output, "out");
        assert!(!rt_is_stdout_capturing());
        assert!(rt_is_stderr_capturing()); // stderr still capturing

        let stderr_output = rt_capture_stderr_stop();
        assert_eq!(stderr_output, "err");
        assert!(!rt_is_stderr_capturing());
    }
}
