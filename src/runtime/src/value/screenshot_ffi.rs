//! FFI functions for screenshot capture in GUI tests.
//!
//! Supports capturing:
//! - Terminal/PTY buffer to ANSI-rendered images
//! - TUI widget state
//! - Vulkan framebuffer (when available)

use std::ffi::{CStr, CString};
use std::os::raw::c_char;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

use parking_lot::RwLock;

// ============================================================================
// Screenshot State
// ============================================================================

/// Whether screenshot capture is enabled
static SCREENSHOT_ENABLED: AtomicBool = AtomicBool::new(false);

/// Whether to force refresh (recapture existing)
static FORCE_REFRESH: AtomicBool = AtomicBool::new(false);

/// Output directory for screenshots
static OUTPUT_DIR: OnceLock<RwLock<String>> = OnceLock::new();

fn get_output_dir() -> &'static RwLock<String> {
    OUTPUT_DIR.get_or_init(|| RwLock::new("doc/spec/image".to_string()))
}

/// Current test context
static CURRENT_TEST: OnceLock<RwLock<TestContext>> = OnceLock::new();

fn get_test_context() -> &'static RwLock<TestContext> {
    CURRENT_TEST.get_or_init(|| RwLock::new(TestContext::default()))
}

#[derive(Default, Clone)]
struct TestContext {
    test_file: String,
    test_name: String,
}

/// Screenshot metadata
#[derive(Debug, Clone)]
pub struct ScreenshotMetadata {
    pub test_file: String,
    pub test_name: String,
    pub capture_type: CaptureType,
    pub timestamp: u64,
    pub width: u32,
    pub height: u32,
    pub format: ImageFormat,
}

/// Capture type
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub enum CaptureType {
    Before = 0,
    After = 1,
    OnChange = 2,
}

/// Image format
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(C)]
pub enum ImageFormat {
    Png = 0,
    Jpeg = 1,
    Svg = 2,
}

/// Captured screenshots for current test
static CAPTURES: OnceLock<RwLock<Vec<CapturedScreenshot>>> = OnceLock::new();

fn get_captures() -> &'static RwLock<Vec<CapturedScreenshot>> {
    CAPTURES.get_or_init(|| RwLock::new(Vec::new()))
}

#[derive(Debug, Clone)]
pub struct CapturedScreenshot {
    pub path: String,
    pub capture_type: CaptureType,
    pub metadata: ScreenshotMetadata,
}

// ============================================================================
// FFI Functions - Control
// ============================================================================

/// Enable screenshot capture
#[no_mangle]
pub extern "C" fn rt_screenshot_enable() {
    SCREENSHOT_ENABLED.store(true, Ordering::SeqCst);
}

/// Disable screenshot capture
#[no_mangle]
pub extern "C" fn rt_screenshot_disable() {
    SCREENSHOT_ENABLED.store(false, Ordering::SeqCst);
}

/// Check if screenshot capture is enabled
#[no_mangle]
pub extern "C" fn rt_screenshot_is_enabled() -> bool {
    SCREENSHOT_ENABLED.load(Ordering::SeqCst)
}

/// Set force refresh mode
#[no_mangle]
pub extern "C" fn rt_screenshot_set_refresh(refresh: bool) {
    FORCE_REFRESH.store(refresh, Ordering::SeqCst);
}

/// Check if force refresh is enabled
#[no_mangle]
pub extern "C" fn rt_screenshot_is_refresh() -> bool {
    FORCE_REFRESH.load(Ordering::SeqCst)
}

/// Set output directory
///
/// # Safety
/// `dir` must be a valid C string
#[no_mangle]
pub unsafe extern "C" fn rt_screenshot_set_output_dir(dir: *const c_char) {
    if dir.is_null() {
        return;
    }
    if let Ok(s) = CStr::from_ptr(dir).to_str() {
        *get_output_dir().write() = s.to_string();
    }
}

/// Get output directory (returns allocated string)
///
/// # Safety
/// Returned string must be freed with rt_screenshot_free_string
#[no_mangle]
pub extern "C" fn rt_screenshot_get_output_dir() -> *mut c_char {
    let dir = get_output_dir().read().clone();
    match CString::new(dir) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Set test context
///
/// # Safety
/// `test_file` and `test_name` must be valid C strings
#[no_mangle]
pub unsafe extern "C" fn rt_screenshot_set_context(
    test_file: *const c_char,
    test_name: *const c_char,
) {
    let mut ctx = get_test_context().write();

    if !test_file.is_null() {
        if let Ok(s) = CStr::from_ptr(test_file).to_str() {
            ctx.test_file = s.to_string();
        }
    }
    if !test_name.is_null() {
        if let Ok(s) = CStr::from_ptr(test_name).to_str() {
            ctx.test_name = s.to_string();
        }
    }
}

/// Clear test context
#[no_mangle]
pub extern "C" fn rt_screenshot_clear_context() {
    let mut ctx = get_test_context().write();
    ctx.test_file.clear();
    ctx.test_name.clear();
}

/// Clear all captured screenshots
#[no_mangle]
pub extern "C" fn rt_screenshot_clear_captures() {
    get_captures().write().clear();
}

// ============================================================================
// FFI Functions - Capture
// ============================================================================

/// Capture a "before" screenshot from terminal buffer
///
/// # Safety
/// `buffer` must be a valid C string containing ANSI escape sequences
#[no_mangle]
pub unsafe extern "C" fn rt_screenshot_capture_before_terminal(buffer: *const c_char) -> bool {
    capture_terminal_internal(buffer, CaptureType::Before)
}

/// Capture an "after" screenshot from terminal buffer
///
/// # Safety
/// `buffer` must be a valid C string containing ANSI escape sequences
#[no_mangle]
pub unsafe extern "C" fn rt_screenshot_capture_after_terminal(buffer: *const c_char) -> bool {
    capture_terminal_internal(buffer, CaptureType::After)
}

/// Internal terminal capture
unsafe fn capture_terminal_internal(buffer: *const c_char, capture_type: CaptureType) -> bool {
    if !SCREENSHOT_ENABLED.load(Ordering::SeqCst) || buffer.is_null() {
        return false;
    }

    let buffer_str = match CStr::from_ptr(buffer).to_str() {
        Ok(s) => s,
        Err(_) => return false,
    };

    let ctx = get_test_context().read().clone();
    let output_dir = get_output_dir().read().clone();

    // Generate path
    let path = generate_screenshot_path(&ctx.test_file, &ctx.test_name, capture_type, &output_dir);

    // Check if exists and not refreshing
    if !FORCE_REFRESH.load(Ordering::SeqCst) && std::path::Path::new(&path).exists() {
        return true; // Already exists
    }

    // Create directory if needed
    if let Some(parent) = std::path::Path::new(&path).parent() {
        let _ = std::fs::create_dir_all(parent);
    }

    // Render ANSI to image (simplified - just save as text for now)
    // In a full implementation, this would use a library like `ansi-to-image`
    let text_path = path.replace(".png", ".txt");
    if std::fs::write(&text_path, buffer_str).is_err() {
        return false;
    }

    // Record capture
    let metadata = ScreenshotMetadata {
        test_file: ctx.test_file.clone(),
        test_name: ctx.test_name.clone(),
        capture_type,
        timestamp: now_millis(),
        width: 80,  // Default terminal width
        height: 24, // Default terminal height
        format: ImageFormat::Png,
    };

    get_captures().write().push(CapturedScreenshot {
        path: text_path,
        capture_type,
        metadata,
    });

    true
}

/// Check if screenshot exists for current test
#[no_mangle]
pub extern "C" fn rt_screenshot_exists(capture_type: CaptureType) -> bool {
    let ctx = get_test_context().read().clone();
    let output_dir = get_output_dir().read().clone();

    let path = generate_screenshot_path(&ctx.test_file, &ctx.test_name, capture_type, &output_dir);
    std::path::Path::new(&path).exists()
}

/// Get screenshot path for current test
///
/// # Safety
/// Returned string must be freed with rt_screenshot_free_string
#[no_mangle]
pub extern "C" fn rt_screenshot_get_path(capture_type: CaptureType) -> *mut c_char {
    let ctx = get_test_context().read().clone();
    let output_dir = get_output_dir().read().clone();

    let path = generate_screenshot_path(&ctx.test_file, &ctx.test_name, capture_type, &output_dir);

    match CString::new(path) {
        Ok(s) => s.into_raw(),
        Err(_) => std::ptr::null_mut(),
    }
}

/// Get count of captured screenshots
#[no_mangle]
pub extern "C" fn rt_screenshot_capture_count() -> usize {
    get_captures().read().len()
}

/// Free a string allocated by screenshot functions
///
/// # Safety
/// `s` must be a pointer returned by rt_screenshot_* or null
#[no_mangle]
pub unsafe extern "C" fn rt_screenshot_free_string(s: *mut c_char) {
    if !s.is_null() {
        drop(CString::from_raw(s));
    }
}

// ============================================================================
// Helper Functions
// ============================================================================

fn now_millis() -> u64 {
    use std::time::{SystemTime, UNIX_EPOCH};
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_millis() as u64)
        .unwrap_or(0)
}

fn generate_screenshot_path(
    test_file: &str,
    test_name: &str,
    capture_type: CaptureType,
    output_dir: &str,
) -> String {
    // Clean up test file path
    let relative = test_file
        .replace("simple/std_lib/test/", "")
        .replace("test/", "")
        .replace("_spec.spl", "")
        .replace("_test.spl", "")
        .replace(".spl", "");

    // Clean up test name
    let safe_name = test_name
        .replace(' ', "_")
        .replace('/', "_")
        .to_lowercase();

    let suffix = match capture_type {
        CaptureType::Before => "before",
        CaptureType::After => "after",
        CaptureType::OnChange => "change",
    };

    format!("{}/{}/{}_{}.png", output_dir, relative, safe_name, suffix)
}

// ============================================================================
// Public Rust API
// ============================================================================

/// Enable screenshots (Rust API)
pub fn enable_screenshots() {
    SCREENSHOT_ENABLED.store(true, Ordering::SeqCst);
}

/// Disable screenshots (Rust API)
pub fn disable_screenshots() {
    SCREENSHOT_ENABLED.store(false, Ordering::SeqCst);
}

/// Check if screenshots enabled (Rust API)
pub fn is_screenshot_enabled() -> bool {
    SCREENSHOT_ENABLED.load(Ordering::SeqCst)
}

/// Get captured screenshots (Rust API)
pub fn get_captured_screenshots() -> Vec<CapturedScreenshot> {
    get_captures().read().clone()
}

/// Set output directory (Rust API)
pub fn set_screenshot_output_dir(dir: &str) {
    *get_output_dir().write() = dir.to_string();
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_screenshot_enable_disable() {
        rt_screenshot_disable();
        assert!(!rt_screenshot_is_enabled());

        rt_screenshot_enable();
        assert!(rt_screenshot_is_enabled());

        rt_screenshot_disable();
        assert!(!rt_screenshot_is_enabled());
    }

    #[test]
    fn test_path_generation() {
        let path = generate_screenshot_path(
            "simple/std_lib/test/unit/ui/widgets_spec.spl",
            "renders button",
            CaptureType::Before,
            "doc/spec/image",
        );
        assert!(path.contains("unit/ui/widgets"));
        assert!(path.contains("renders_button"));
        assert!(path.contains("before.png"));
    }
}
