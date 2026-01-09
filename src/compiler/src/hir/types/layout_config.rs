//! Layout configuration for 4KB page locality optimization.
//!
//! This module provides types for loading and applying layout configuration
//! from SDN files. It enables:
//!
//! - Page budgets per phase (startup, first_frame, steady, cold)
//! - Function pattern matching for automatic phase assignment
//! - Profile-based layout hints from recorded execution data
//!
//! # SDN Schema
//!
//! ```sdn
//! # layout.sdn - Code locality configuration
//! layout:
//!     page_size: 4096
//!
//!     budgets:
//!         startup: 8       # Max 8 pages for startup code
//!         first_frame: 4   # Max 4 pages for first frame
//!         steady: 0        # Unlimited pages
//!         cold: 0          # Unlimited pages
//!
//!     patterns:
//!         startup = [parse_*, init_*, setup_*]
//!         first_frame = [render_first_*, ui_init_*]
//!         cold = [help_*, error_*, debug_*]
//!
//!     anchors:
//!         event_loop = [main_loop, event_loop, run_loop]
//!
//!     # Recorded function timings from profiling
//!     recorded |function, phase, size, call_count|
//!         main, startup, 256, 1
//!         parse_args, startup, 512, 1
//!         event_loop, steady, 128, 10000
//!         help_message, cold, 1024, 0
//! ```

use super::code_layout::{LayoutAnchor, LayoutPhase, PageBudget};
use indexmap::IndexMap;
use std::collections::HashMap;
use std::fmt;
use std::path::Path;

/// Complete layout configuration loaded from SDN.
#[derive(Debug, Clone, Default)]
pub struct LayoutConfig {
    /// Page size in bytes (typically 4096).
    pub page_size: u32,

    /// Page budgets per phase.
    pub budgets: PhaseBudgets,

    /// Pattern matching rules for automatic phase assignment.
    pub patterns: PhasePatterns,

    /// Anchor pattern matching rules.
    pub anchor_patterns: AnchorPatterns,

    /// Recorded function data from profiling.
    pub recorded: Vec<RecordedFunction>,

    /// Per-function overrides for phase assignment.
    pub overrides: HashMap<String, LayoutPhase>,

    /// Source file path (if loaded from file).
    pub source_path: Option<String>,
}

/// Page budgets for each layout phase.
#[derive(Debug, Clone)]
pub struct PhaseBudgets {
    /// Startup phase budget (pages).
    pub startup: u32,
    /// First frame phase budget (pages).
    pub first_frame: u32,
    /// Steady state phase budget (0 = unlimited).
    pub steady: u32,
    /// Cold code phase budget (0 = unlimited).
    pub cold: u32,
}

impl Default for PhaseBudgets {
    fn default() -> Self {
        Self {
            startup: 8,     // 32KB default for startup
            first_frame: 4, // 16KB default for first frame
            steady: 0,      // Unlimited
            cold: 0,        // Unlimited
        }
    }
}

impl PhaseBudgets {
    /// Get the budget for a specific phase.
    pub fn get(&self, phase: LayoutPhase) -> u32 {
        match phase {
            LayoutPhase::Startup => self.startup,
            LayoutPhase::FirstFrame => self.first_frame,
            LayoutPhase::Steady => self.steady,
            LayoutPhase::Cold => self.cold,
        }
    }

    /// Set the budget for a specific phase.
    pub fn set(&mut self, phase: LayoutPhase, pages: u32) {
        match phase {
            LayoutPhase::Startup => self.startup = pages,
            LayoutPhase::FirstFrame => self.first_frame = pages,
            LayoutPhase::Steady => self.steady = pages,
            LayoutPhase::Cold => self.cold = pages,
        }
    }

    /// Convert to PageBudget structs.
    pub fn to_page_budgets(&self, page_size: u32) -> Vec<PageBudget> {
        vec![
            PageBudget {
                phase: LayoutPhase::Startup,
                page_size,
                max_pages: self.startup,
                align_pages: true,
            },
            PageBudget {
                phase: LayoutPhase::FirstFrame,
                page_size,
                max_pages: self.first_frame,
                align_pages: true,
            },
            PageBudget {
                phase: LayoutPhase::Steady,
                page_size,
                max_pages: self.steady,
                align_pages: false,
            },
            PageBudget {
                phase: LayoutPhase::Cold,
                page_size,
                max_pages: self.cold,
                align_pages: false,
            },
        ]
    }
}

/// Pattern matching rules for automatic phase assignment.
#[derive(Debug, Clone, Default)]
pub struct PhasePatterns {
    /// Patterns for startup phase (glob-style: "parse_*", "init_*").
    pub startup: Vec<String>,
    /// Patterns for first_frame phase.
    pub first_frame: Vec<String>,
    /// Patterns for steady phase.
    pub steady: Vec<String>,
    /// Patterns for cold phase.
    pub cold: Vec<String>,
}

impl PhasePatterns {
    /// Get patterns for a specific phase.
    pub fn get(&self, phase: LayoutPhase) -> &[String] {
        match phase {
            LayoutPhase::Startup => &self.startup,
            LayoutPhase::FirstFrame => &self.first_frame,
            LayoutPhase::Steady => &self.steady,
            LayoutPhase::Cold => &self.cold,
        }
    }

    /// Check if a function name matches any pattern for a phase.
    pub fn matches(&self, phase: LayoutPhase, function_name: &str) -> bool {
        for pattern in self.get(phase) {
            if pattern_matches(pattern, function_name) {
                return true;
            }
        }
        false
    }

    /// Find the phase for a function name based on patterns.
    /// Returns None if no pattern matches.
    pub fn find_phase(&self, function_name: &str) -> Option<LayoutPhase> {
        // Check in priority order
        for phase in [
            LayoutPhase::Startup,
            LayoutPhase::FirstFrame,
            LayoutPhase::Cold,
            LayoutPhase::Steady,
        ] {
            if self.matches(phase, function_name) {
                return Some(phase);
            }
        }
        None
    }
}

/// Anchor pattern matching rules.
#[derive(Debug, Clone, Default)]
pub struct AnchorPatterns {
    /// Patterns for event loop anchors.
    pub event_loop: Vec<String>,
    /// Custom anchors with their patterns.
    pub custom: IndexMap<String, Vec<String>>,
}

impl AnchorPatterns {
    /// Check if a function is an event loop anchor.
    pub fn is_event_loop(&self, function_name: &str) -> bool {
        self.event_loop
            .iter()
            .any(|p| pattern_matches(p, function_name))
    }

    /// Find the anchor type for a function.
    pub fn find_anchor(&self, function_name: &str) -> Option<LayoutAnchor> {
        if self.is_event_loop(function_name) {
            return Some(LayoutAnchor::EventLoop);
        }

        for (name, patterns) in &self.custom {
            if patterns.iter().any(|p| pattern_matches(p, function_name)) {
                return Some(LayoutAnchor::Custom(name.clone()));
            }
        }

        None
    }
}

/// Recorded function data from profiling.
#[derive(Debug, Clone)]
pub struct RecordedFunction {
    /// Function name (fully qualified or simple).
    pub name: String,
    /// Assigned phase.
    pub phase: LayoutPhase,
    /// Function size in bytes.
    pub size: u64,
    /// Call count during profiling.
    pub call_count: u64,
    /// Optional module path.
    pub module: Option<String>,
}

impl RecordedFunction {
    /// Create a new recorded function entry.
    pub fn new(name: &str, phase: LayoutPhase, size: u64, call_count: u64) -> Self {
        Self {
            name: name.to_string(),
            phase,
            size,
            call_count,
            module: None,
        }
    }

    /// Set the module path.
    pub fn with_module(mut self, module: &str) -> Self {
        self.module = Some(module.to_string());
        self
    }
}

/// Simple glob-style pattern matching.
/// Supports:
/// - `*` at start or end for prefix/suffix matching
/// - `*` in middle for contains matching
/// - Exact match otherwise
fn pattern_matches(pattern: &str, text: &str) -> bool {
    if pattern == "*" {
        return true;
    }

    if pattern.starts_with('*') && pattern.ends_with('*') {
        // Contains match: *foo*
        let inner = &pattern[1..pattern.len() - 1];
        return text.contains(inner);
    }

    if pattern.starts_with('*') {
        // Suffix match: *_handler
        let suffix = &pattern[1..];
        return text.ends_with(suffix);
    }

    if pattern.ends_with('*') {
        // Prefix match: parse_*
        let prefix = &pattern[..pattern.len() - 1];
        return text.starts_with(prefix);
    }

    // Exact match
    pattern == text
}

/// Error type for layout configuration loading.
#[derive(Debug)]
pub enum LayoutConfigError {
    /// File not found.
    NotFound(String),
    /// Parse error in SDN file.
    ParseError(String),
    /// Invalid value in configuration.
    InvalidValue(String),
    /// IO error.
    IoError(std::io::Error),
}

impl fmt::Display for LayoutConfigError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            LayoutConfigError::NotFound(path) => write!(f, "Layout config not found: {}", path),
            LayoutConfigError::ParseError(msg) => write!(f, "Parse error: {}", msg),
            LayoutConfigError::InvalidValue(msg) => write!(f, "Invalid value: {}", msg),
            LayoutConfigError::IoError(e) => write!(f, "IO error: {}", e),
        }
    }
}

impl std::error::Error for LayoutConfigError {}

impl From<std::io::Error> for LayoutConfigError {
    fn from(e: std::io::Error) -> Self {
        LayoutConfigError::IoError(e)
    }
}

impl LayoutConfig {
    /// Create a new empty layout configuration.
    pub fn new() -> Self {
        Self {
            page_size: 4096,
            ..Default::default()
        }
    }

    /// Load layout configuration from an SDN file.
    pub fn from_file(path: &Path) -> Result<Self, LayoutConfigError> {
        use simple_sdn::{parse_file, SdnValue};

        if !path.exists() {
            return Err(LayoutConfigError::NotFound(path.display().to_string()));
        }

        let root = parse_file(path).map_err(|e| LayoutConfigError::ParseError(format!("{}", e)))?;

        Self::from_sdn_value(&root, Some(path.display().to_string()))
    }

    /// Load layout configuration from SDN string.
    pub fn from_str(s: &str) -> Result<Self, LayoutConfigError> {
        use simple_sdn::{parse, SdnValue};

        let root = parse(s).map_err(|e| LayoutConfigError::ParseError(format!("{}", e)))?;

        Self::from_sdn_value(&root, None)
    }

    /// Parse layout config from SDN value.
    fn from_sdn_value(
        root: &simple_sdn::SdnValue,
        source_path: Option<String>,
    ) -> Result<Self, LayoutConfigError> {
        use simple_sdn::SdnValue;

        let mut config = LayoutConfig {
            source_path,
            ..Default::default()
        };

        // Get the layout section
        let layout = match root {
            SdnValue::Dict(dict) => dict.get("layout").unwrap_or(root),
            _ => root,
        };

        if let SdnValue::Dict(dict) = layout {
            // Parse page_size
            if let Some(SdnValue::Int(size)) = dict.get("page_size") {
                config.page_size = *size as u32;
            }

            // Parse budgets
            if let Some(SdnValue::Dict(budgets)) = dict.get("budgets") {
                if let Some(SdnValue::Int(v)) = budgets.get("startup") {
                    config.budgets.startup = *v as u32;
                }
                if let Some(SdnValue::Int(v)) = budgets.get("first_frame") {
                    config.budgets.first_frame = *v as u32;
                }
                if let Some(SdnValue::Int(v)) = budgets.get("steady") {
                    config.budgets.steady = *v as u32;
                }
                if let Some(SdnValue::Int(v)) = budgets.get("cold") {
                    config.budgets.cold = *v as u32;
                }
            }

            // Parse patterns
            if let Some(SdnValue::Dict(patterns)) = dict.get("patterns") {
                config.patterns.startup = parse_string_array(patterns.get("startup"));
                config.patterns.first_frame = parse_string_array(patterns.get("first_frame"));
                config.patterns.steady = parse_string_array(patterns.get("steady"));
                config.patterns.cold = parse_string_array(patterns.get("cold"));
            }

            // Parse anchors
            if let Some(SdnValue::Dict(anchors)) = dict.get("anchors") {
                config.anchor_patterns.event_loop = parse_string_array(anchors.get("event_loop"));

                for (key, value) in anchors.iter() {
                    if key != "event_loop" {
                        config
                            .anchor_patterns
                            .custom
                            .insert(key.clone(), parse_string_array(Some(value)));
                    }
                }
            }

            // Parse recorded table
            if let Some(SdnValue::Table { fields, rows, .. }) = dict.get("recorded") {
                for row in rows {
                    if row.len() >= 4 {
                        let name = match &row[0] {
                            SdnValue::String(s) => s.clone(),
                            _ => continue,
                        };
                        let phase = match &row[1] {
                            SdnValue::String(s) => {
                                LayoutPhase::from_str(s).unwrap_or(LayoutPhase::Steady)
                            }
                            _ => continue,
                        };
                        let size = match &row[2] {
                            SdnValue::Int(i) => *i as u64,
                            _ => 0,
                        };
                        let call_count = match &row[3] {
                            SdnValue::Int(i) => *i as u64,
                            _ => 0,
                        };

                        config
                            .recorded
                            .push(RecordedFunction::new(&name, phase, size, call_count));
                    }
                }
            }

            // Parse overrides
            if let Some(SdnValue::Dict(overrides)) = dict.get("overrides") {
                for (func_name, phase_value) in overrides.iter() {
                    if let SdnValue::String(phase_str) = phase_value {
                        if let Some(phase) = LayoutPhase::from_str(phase_str) {
                            config.overrides.insert(func_name.clone(), phase);
                        }
                    }
                }
            }
        }

        Ok(config)
    }

    /// Get the layout phase for a function.
    /// Checks in order: overrides, recorded data, patterns, default.
    pub fn get_phase(&self, function_name: &str) -> LayoutPhase {
        // Check explicit overrides first
        if let Some(phase) = self.overrides.get(function_name) {
            return *phase;
        }

        // Check recorded data
        for recorded in &self.recorded {
            if recorded.name == function_name {
                return recorded.phase;
            }
        }

        // Check pattern matching
        if let Some(phase) = self.patterns.find_phase(function_name) {
            return phase;
        }

        // Default to steady
        LayoutPhase::Steady
    }

    /// Check if a function is an anchor point.
    pub fn is_anchor(&self, function_name: &str) -> Option<LayoutAnchor> {
        self.anchor_patterns.find_anchor(function_name)
    }

    /// Get page budgets as PageBudget structs.
    pub fn page_budgets(&self) -> Vec<PageBudget> {
        self.budgets.to_page_budgets(self.page_size)
    }

    /// Merge another configuration into this one.
    /// The other configuration's values take precedence.
    pub fn merge(&mut self, other: &LayoutConfig) {
        // Merge budgets (prefer non-default values from other)
        if other.budgets.startup != 8 {
            self.budgets.startup = other.budgets.startup;
        }
        if other.budgets.first_frame != 4 {
            self.budgets.first_frame = other.budgets.first_frame;
        }
        if other.budgets.steady != 0 {
            self.budgets.steady = other.budgets.steady;
        }
        if other.budgets.cold != 0 {
            self.budgets.cold = other.budgets.cold;
        }

        // Merge patterns (append)
        self.patterns
            .startup
            .extend(other.patterns.startup.iter().cloned());
        self.patterns
            .first_frame
            .extend(other.patterns.first_frame.iter().cloned());
        self.patterns
            .steady
            .extend(other.patterns.steady.iter().cloned());
        self.patterns
            .cold
            .extend(other.patterns.cold.iter().cloned());

        // Merge anchor patterns
        self.anchor_patterns
            .event_loop
            .extend(other.anchor_patterns.event_loop.iter().cloned());
        for (name, patterns) in &other.anchor_patterns.custom {
            self.anchor_patterns
                .custom
                .entry(name.clone())
                .or_insert_with(Vec::new)
                .extend(patterns.iter().cloned());
        }

        // Merge recorded (append)
        self.recorded.extend(other.recorded.iter().cloned());

        // Merge overrides (other takes precedence)
        for (name, phase) in &other.overrides {
            self.overrides.insert(name.clone(), *phase);
        }
    }

    /// Serialize to SDN string.
    pub fn to_sdn(&self) -> String {
        let mut output = String::new();

        output.push_str("# Layout configuration for 4KB page locality optimization\n\n");
        output.push_str("layout:\n");
        output.push_str(&format!("    page_size: {}\n\n", self.page_size));

        // Budgets
        output.push_str("    budgets:\n");
        output.push_str(&format!("        startup: {}\n", self.budgets.startup));
        output.push_str(&format!(
            "        first_frame: {}\n",
            self.budgets.first_frame
        ));
        output.push_str(&format!("        steady: {}\n", self.budgets.steady));
        output.push_str(&format!("        cold: {}\n\n", self.budgets.cold));

        // Patterns
        if !self.patterns.startup.is_empty()
            || !self.patterns.first_frame.is_empty()
            || !self.patterns.cold.is_empty()
        {
            output.push_str("    patterns:\n");
            if !self.patterns.startup.is_empty() {
                output.push_str(&format!(
                    "        startup = [{}]\n",
                    self.patterns.startup.join(", ")
                ));
            }
            if !self.patterns.first_frame.is_empty() {
                output.push_str(&format!(
                    "        first_frame = [{}]\n",
                    self.patterns.first_frame.join(", ")
                ));
            }
            if !self.patterns.cold.is_empty() {
                output.push_str(&format!(
                    "        cold = [{}]\n",
                    self.patterns.cold.join(", ")
                ));
            }
            output.push('\n');
        }

        // Anchors
        if !self.anchor_patterns.event_loop.is_empty() || !self.anchor_patterns.custom.is_empty() {
            output.push_str("    anchors:\n");
            if !self.anchor_patterns.event_loop.is_empty() {
                output.push_str(&format!(
                    "        event_loop = [{}]\n",
                    self.anchor_patterns.event_loop.join(", ")
                ));
            }
            for (name, patterns) in &self.anchor_patterns.custom {
                output.push_str(&format!("        {} = [{}]\n", name, patterns.join(", ")));
            }
            output.push('\n');
        }

        // Recorded functions
        if !self.recorded.is_empty() {
            output.push_str("    recorded |function, phase, size, call_count|\n");
            for func in &self.recorded {
                output.push_str(&format!(
                    "        {}, {}, {}, {}\n",
                    func.name, func.phase, func.size, func.call_count
                ));
            }
        }

        output
    }
}

/// Helper to parse an SDN array of strings.
fn parse_string_array(value: Option<&simple_sdn::SdnValue>) -> Vec<String> {
    use simple_sdn::SdnValue;

    match value {
        Some(SdnValue::Array(arr)) => arr
            .iter()
            .filter_map(|v| match v {
                SdnValue::String(s) => Some(s.clone()),
                _ => None,
            })
            .collect(),
        Some(SdnValue::String(s)) => vec![s.clone()],
        _ => Vec::new(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_pattern_matches() {
        // Prefix match
        assert!(pattern_matches("parse_*", "parse_args"));
        assert!(pattern_matches("parse_*", "parse_config"));
        assert!(!pattern_matches("parse_*", "do_parse"));

        // Suffix match
        assert!(pattern_matches("*_handler", "click_handler"));
        assert!(pattern_matches("*_handler", "event_handler"));
        assert!(!pattern_matches("*_handler", "handler_main"));

        // Contains match
        assert!(pattern_matches("*loop*", "main_loop_impl"));
        assert!(pattern_matches("*loop*", "loopback"));
        assert!(!pattern_matches("*loop*", "look"));

        // Exact match
        assert!(pattern_matches("main", "main"));
        assert!(!pattern_matches("main", "main_loop"));

        // Wildcard
        assert!(pattern_matches("*", "anything"));
    }

    #[test]
    fn test_phase_patterns() {
        let mut patterns = PhasePatterns::default();
        patterns.startup = vec!["init_*".to_string(), "parse_*".to_string()];
        patterns.cold = vec!["help_*".to_string(), "debug_*".to_string()];

        assert_eq!(patterns.find_phase("init_app"), Some(LayoutPhase::Startup));
        assert_eq!(
            patterns.find_phase("parse_args"),
            Some(LayoutPhase::Startup)
        );
        assert_eq!(patterns.find_phase("help_message"), Some(LayoutPhase::Cold));
        assert_eq!(patterns.find_phase("run_loop"), None);
    }

    #[test]
    fn test_anchor_patterns() {
        let mut anchors = AnchorPatterns::default();
        anchors.event_loop = vec!["main_loop".to_string(), "*_loop".to_string()];

        assert!(anchors.is_event_loop("main_loop"));
        assert!(anchors.is_event_loop("event_loop"));
        assert!(!anchors.is_event_loop("loopback"));
    }

    #[test]
    fn test_phase_budgets() {
        let budgets = PhaseBudgets::default();
        assert_eq!(budgets.get(LayoutPhase::Startup), 8);
        assert_eq!(budgets.get(LayoutPhase::FirstFrame), 4);
        assert_eq!(budgets.get(LayoutPhase::Steady), 0);
        assert_eq!(budgets.get(LayoutPhase::Cold), 0);

        let page_budgets = budgets.to_page_budgets(4096);
        assert_eq!(page_budgets.len(), 4);
        assert_eq!(page_budgets[0].max_pages, 8);
        assert!(page_budgets[0].align_pages);
    }

    #[test]
    fn test_layout_config_get_phase() {
        let mut config = LayoutConfig::new();
        config.patterns.startup = vec!["init_*".to_string()];
        config.patterns.cold = vec!["help_*".to_string()];
        config
            .overrides
            .insert("special_func".to_string(), LayoutPhase::FirstFrame);
        config.recorded.push(RecordedFunction::new(
            "recorded_func",
            LayoutPhase::Startup,
            100,
            5,
        ));

        // Override takes precedence
        assert_eq!(config.get_phase("special_func"), LayoutPhase::FirstFrame);

        // Recorded takes precedence over patterns
        assert_eq!(config.get_phase("recorded_func"), LayoutPhase::Startup);

        // Pattern matching
        assert_eq!(config.get_phase("init_app"), LayoutPhase::Startup);
        assert_eq!(config.get_phase("help_text"), LayoutPhase::Cold);

        // Default to steady
        assert_eq!(config.get_phase("unknown_func"), LayoutPhase::Steady);
    }

    #[test]
    fn test_layout_config_to_sdn() {
        let mut config = LayoutConfig::new();
        config.budgets.startup = 10;
        config.patterns.startup = vec!["init_*".to_string()];
        config.anchor_patterns.event_loop = vec!["main_loop".to_string()];
        config
            .recorded
            .push(RecordedFunction::new("main", LayoutPhase::Startup, 256, 1));

        let sdn = config.to_sdn();
        assert!(sdn.contains("page_size: 4096"));
        assert!(sdn.contains("startup: 10"));
        assert!(sdn.contains("startup = [init_*]"));
        assert!(sdn.contains("event_loop = [main_loop]"));
        assert!(sdn.contains("main, startup, 256, 1"));
    }
}
