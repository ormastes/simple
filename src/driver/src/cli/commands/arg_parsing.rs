//! Command-line argument parsing and filtering utilities

use std::env;

/// Parse global flags from command-line arguments
pub struct GlobalFlags {
    pub gc_log: bool,
    pub gc_off: bool,
    pub use_notui: bool,
    pub macro_trace: bool,
    pub debug_mode: bool,
}

impl GlobalFlags {
    pub fn parse(args: &[String]) -> Self {
        Self {
            gc_log: args.iter().any(|a| a == "--gc-log"),
            gc_off: args.iter().any(|a| a == "--gc=off" || a == "--gc=OFF"),
            use_notui: args.iter().any(|a| a == "--notui"),
            macro_trace: args.iter().any(|a| a == "--macro-trace"),
            debug_mode: args.iter().any(|a| a == "--debug"),
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
        let args = vec![
            "simple".to_string(),
            "--gc-log".to_string(),
            "--debug".to_string(),
        ];
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
