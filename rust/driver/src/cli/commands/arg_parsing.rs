//! Command-line argument parsing and filtering utilities

use std::env;

/// Fix mode flags for auto-fix behavior
#[derive(Debug, Clone, Default)]
pub struct FixFlags {
    /// Apply all safe-confidence fixes automatically
    pub fix: bool,
    /// Apply all fixes regardless of confidence
    pub fix_all: bool,
    /// Apply fixes for warnings only
    pub fix_warnings: bool,
    /// Apply fixes for errors only
    pub fix_errors: bool,
    /// Apply fixes for info/notes only
    pub fix_info: bool,
    /// Apply fix with specific ID prefix
    pub fix_id: Option<String>,
    /// Apply fixes for specific error code
    pub fix_code: Option<String>,
    /// Apply only the Nth fix (1-based)
    pub fix_nth: Option<usize>,
    /// Prompt for each fix interactively
    pub fix_interactive: bool,
    /// Show what would be fixed without applying
    pub fix_dry_run: bool,
}

impl FixFlags {
    pub fn parse(args: &[String]) -> Self {
        let mut flags = Self::default();
        let mut iter = args.iter().peekable();

        while let Some(arg) = iter.next() {
            match arg.as_str() {
                "--fix" => flags.fix = true,
                "--fix-all" => flags.fix_all = true,
                "--fix-warnings" => flags.fix_warnings = true,
                "--fix-errors" => flags.fix_errors = true,
                "--fix-info" => flags.fix_info = true,
                "--fix-interactive" => flags.fix_interactive = true,
                "--fix-dry-run" => flags.fix_dry_run = true,
                _ => {
                    if let Some(id) = arg.strip_prefix("--fix-id=") {
                        flags.fix_id = Some(id.to_string());
                    } else if let Some(code) = arg.strip_prefix("--fix-code=") {
                        flags.fix_code = Some(code.to_string());
                    } else if let Some(n) = arg.strip_prefix("--fix-nth=") {
                        flags.fix_nth = n.parse().ok();
                    }
                }
            }
        }

        flags
    }

    /// Whether any fix mode is active
    pub fn any_fix_mode(&self) -> bool {
        self.fix
            || self.fix_all
            || self.fix_warnings
            || self.fix_errors
            || self.fix_info
            || self.fix_id.is_some()
            || self.fix_code.is_some()
            || self.fix_nth.is_some()
            || self.fix_interactive
    }
}

/// Parse global flags from command-line arguments
pub struct GlobalFlags {
    pub gc_log: bool,
    pub gc_off: bool,
    pub use_notui: bool,
    pub macro_trace: bool,
    pub debug_mode: bool,
    pub fix_flags: FixFlags,
}

impl GlobalFlags {
    pub fn parse(args: &[String]) -> Self {
        Self {
            gc_log: args.iter().any(|a| a == "--gc-log"),
            gc_off: args.iter().any(|a| a == "--gc=off" || a == "--gc=OFF"),
            use_notui: args.iter().any(|a| a == "--notui"),
            macro_trace: args.iter().any(|a| a == "--macro-trace"),
            debug_mode: args.iter().any(|a| a == "--debug"),
            fix_flags: FixFlags::parse(args),
        }
    }

    /// Apply global flags to the runtime environment
    pub fn apply(&self) {
        if self.macro_trace {
            simple_compiler::set_macro_trace(true);
        }
        if self.debug_mode {
            simple_compiler::set_debug_mode(true);
        }
    }
}

/// Parse and set language flag for i18n localization
pub fn parse_lang_flag(args: &[String]) {
    if let Some(lang_pos) = args.iter().position(|a| a == "--lang") {
        if let Some(lang) = args.get(lang_pos + 1) {
            env::set_var("SIMPLE_LANG", lang);
        }
    }
}

/// Filter out internal flags (GC, sandbox, etc.) from arguments
pub fn filter_internal_flags(args: &[String]) -> Vec<String> {
    let mut filtered_args = Vec::new();
    let mut skip_next = false;

    for arg in args.iter() {
        if skip_next {
            skip_next = false;
            continue;
        }

        // Single flags without values
        if arg.starts_with("--gc")
            || arg == "--notui"
            || arg == "--startup-metrics"
            || arg == "--macro-trace"
            || arg == "--debug"
            || arg == "--sandbox"
            || arg == "--no-network"
            || arg == "--fix"
            || arg == "--fix-all"
            || arg == "--fix-warnings"
            || arg == "--fix-errors"
            || arg == "--fix-info"
            || arg == "--fix-interactive"
            || arg == "--fix-dry-run"
            || arg.starts_with("--fix-id=")
            || arg.starts_with("--fix-code=")
            || arg.starts_with("--fix-nth=")
        {
            continue;
        }

        // Flags that take a value - skip the next argument too
        if arg == "--time-limit"
            || arg == "--memory-limit"
            || arg == "--fd-limit"
            || arg == "--thread-limit"
            || arg == "--network-allow"
            || arg == "--network-block"
            || arg == "--read-only"
            || arg == "--read-write"
            || arg == "--lang"
        {
            skip_next = true;
            continue;
        }

        filtered_args.push(arg.clone());
    }

    filtered_args
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_global_flags_parsing() {
        let args = vec!["simple".to_string(), "--gc-log".to_string(), "--debug".to_string()];
        let flags = GlobalFlags::parse(&args);
        assert!(flags.gc_log);
        assert!(flags.debug_mode);
        assert!(!flags.gc_off);
    }

    #[test]
    fn test_filter_internal_flags() {
        let args = vec![
            "test.spl".to_string(),
            "--gc-log".to_string(),
            "--time-limit".to_string(),
            "60".to_string(),
            "arg1".to_string(),
        ];
        let filtered = filter_internal_flags(&args);
        assert_eq!(filtered, vec!["test.spl", "arg1"]);
    }

    #[test]
    fn test_filter_lang_flag() {
        let args = vec![
            "test.spl".to_string(),
            "--lang".to_string(),
            "ko".to_string(),
            "arg1".to_string(),
        ];
        let filtered = filter_internal_flags(&args);
        assert_eq!(filtered, vec!["test.spl", "arg1"]);
    }
}
