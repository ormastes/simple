//! Early startup argument parsing
//!
//! This module provides minimal argument parsing that happens before any
//! runtime initialization. It extracts essential information like app type
//! and input files so prefetching can begin immediately.
//!
//! # Design Goals
//! - Zero allocation where possible (stack-only for critical path)
//! - No dependencies on Simple runtime
//! - Fast parsing (single pass)
//! - Cross-platform (Linux + Windows)

use std::ffi::{OsStr, OsString};
use std::path::PathBuf;

/// Application type detected from arguments or binary metadata
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AppType {
    /// Command-line tool (minimal resources)
    Cli,
    /// Terminal UI application (terminal mode, buffers)
    Tui,
    /// Graphical application (window, GPU context)
    Gui,
    /// Background service/daemon (IPC, signal handlers)
    Service,
    /// Interactive REPL (history, line editor)
    Repl,
}

impl Default for AppType {
    fn default() -> Self {
        AppType::Cli
    }
}

impl AppType {
    /// Parse app type from string argument
    pub fn from_str(s: &str) -> Option<Self> {
        match s {
            "cli" => Some(AppType::Cli),
            "tui" => Some(AppType::Tui),
            "gui" => Some(AppType::Gui),
            "service" => Some(AppType::Service),
            "repl" => Some(AppType::Repl),
            _ => None,
        }
    }

    /// Get app type as string
    pub fn as_str(&self) -> &'static str {
        match self {
            AppType::Cli => "cli",
            AppType::Tui => "tui",
            AppType::Gui => "gui",
            AppType::Service => "service",
            AppType::Repl => "repl",
        }
    }
}

/// Window hints for GUI applications
#[derive(Debug, Clone)]
pub struct WindowHints {
    pub width: u32,
    pub height: u32,
    pub title: String,
}

impl Default for WindowHints {
    fn default() -> Self {
        WindowHints {
            width: 1280,
            height: 720,
            title: "Simple Application".to_string(),
        }
    }
}

/// Early startup configuration extracted from arguments
#[derive(Debug, Clone)]
pub struct EarlyConfig {
    /// Application type
    pub app_type: AppType,
    /// Input files to prefetch
    pub input_files: Vec<PathBuf>,
    /// Window hints for GUI apps
    pub window_hints: WindowHints,
    /// Enable prefetching (default: true)
    pub enable_prefetch: bool,
    /// Remaining arguments to pass to main Simple runtime
    pub remaining_args: Vec<OsString>,
}

impl Default for EarlyConfig {
    fn default() -> Self {
        EarlyConfig {
            app_type: AppType::Cli,
            input_files: Vec::new(),
            window_hints: WindowHints::default(),
            enable_prefetch: true,
            remaining_args: Vec::new(),
        }
    }
}

/// Parse arguments for early startup
///
/// This is called before any runtime initialization. It extracts:
/// - App type from --app-type argument
/// - Input files from positional arguments
/// - Window hints from --window-* arguments
/// - Prefetch control from --no-prefetch
///
/// # Arguments
/// - `args`: Iterator over command-line arguments (excluding program name)
///
/// # Returns
/// Early configuration for startup optimization
pub fn parse_early_args<I, S>(args: I) -> EarlyConfig
where
    I: IntoIterator<Item = S>,
    S: AsRef<OsStr>,
{
    let mut config = EarlyConfig::default();
    let mut args_iter = args.into_iter().peekable();

    while let Some(arg) = args_iter.next() {
        let arg_str = arg.as_ref().to_string_lossy();

        if arg_str.starts_with("--") {
            // Parse long options
            match arg_str.as_ref() {
                "--app-type" => {
                    if let Some(type_arg) = args_iter.next() {
                        if let Some(app_type) = AppType::from_str(&type_arg.as_ref().to_string_lossy()) {
                            config.app_type = app_type;
                        }
                    }
                }
                "--no-prefetch" => {
                    config.enable_prefetch = false;
                }
                "--window-width" => {
                    if let Some(width_arg) = args_iter.next() {
                        if let Ok(width) = width_arg.as_ref().to_string_lossy().parse() {
                            config.window_hints.width = width;
                        }
                    }
                }
                "--window-height" => {
                    if let Some(height_arg) = args_iter.next() {
                        if let Ok(height) = height_arg.as_ref().to_string_lossy().parse() {
                            config.window_hints.height = height;
                        }
                    }
                }
                "--window-title" => {
                    if let Some(title_arg) = args_iter.next() {
                        config.window_hints.title = title_arg.as_ref().to_string_lossy().to_string();
                    }
                }
                _ => {
                    // Unknown option - save for later
                    config.remaining_args.push(arg.as_ref().to_os_string());
                }
            }
        } else {
            // Positional argument - check if it's a file
            let arg_path = PathBuf::from(arg.as_ref());

            // If it exists and is a file, add to prefetch list
            if arg_path.exists() && arg_path.is_file() {
                config.input_files.push(arg_path.clone());
            }

            // Always save for later processing
            config.remaining_args.push(arg.as_ref().to_os_string());
        }
    }

    config
}

/// Parse arguments from raw argc/argv (C-style)
///
/// # Safety
/// This function is unsafe because it dereferences raw pointers.
/// The caller must ensure that:
/// - `argc` is the correct count of arguments
/// - `argv` points to a valid array of `argc + 1` pointers
/// - Each pointer in `argv` points to a valid null-terminated C string
/// - `argv[argc]` is null
#[cfg(unix)]
pub unsafe fn parse_early_args_raw(argc: i32, argv: *const *const u8) -> EarlyConfig {
    use std::ffi::CStr;

    let mut args = Vec::new();

    // Skip argv[0] (program name)
    for i in 1..argc {
        let arg_ptr = *argv.offset(i as isize);
        if arg_ptr.is_null() {
            break;
        }

        let c_str = CStr::from_ptr(arg_ptr as *const i8);
        if let Ok(arg_str) = c_str.to_str() {
            args.push(OsString::from(arg_str));
        }
    }

    parse_early_args(args)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_app_type_parsing() {
        assert_eq!(AppType::from_str("cli"), Some(AppType::Cli));
        assert_eq!(AppType::from_str("tui"), Some(AppType::Tui));
        assert_eq!(AppType::from_str("gui"), Some(AppType::Gui));
        assert_eq!(AppType::from_str("service"), Some(AppType::Service));
        assert_eq!(AppType::from_str("repl"), Some(AppType::Repl));
        assert_eq!(AppType::from_str("invalid"), None);
    }

    #[test]
    fn test_parse_early_args_app_type() {
        let args = vec!["--app-type", "gui"];
        let config = parse_early_args(args);
        assert_eq!(config.app_type, AppType::Gui);
    }

    #[test]
    fn test_parse_early_args_window_hints() {
        let args = vec![
            "--app-type",
            "gui",
            "--window-width",
            "1920",
            "--window-height",
            "1080",
            "--window-title",
            "Test App",
        ];
        let config = parse_early_args(args);
        assert_eq!(config.app_type, AppType::Gui);
        assert_eq!(config.window_hints.width, 1920);
        assert_eq!(config.window_hints.height, 1080);
        assert_eq!(config.window_hints.title, "Test App");
    }

    #[test]
    fn test_parse_early_args_no_prefetch() {
        let args = vec!["--no-prefetch"];
        let config = parse_early_args(args);
        assert!(!config.enable_prefetch);
    }

    #[test]
    fn test_parse_early_args_default_prefetch() {
        let args: Vec<&str> = vec![];
        let config = parse_early_args(args);
        assert!(config.enable_prefetch);
    }

    #[test]
    fn test_parse_early_args_remaining() {
        let args = vec!["--app-type", "cli", "--unknown", "value", "positional"];
        let config = parse_early_args(args);
        assert_eq!(config.app_type, AppType::Cli);
        assert_eq!(config.remaining_args.len(), 3);
    }
}
