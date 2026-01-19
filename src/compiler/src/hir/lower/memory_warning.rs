//! Memory safety warning detection (Phase 1 of migration plan)
//!
//! This module implements warning codes W1001-W1006 for detecting memory safety
//! violations without breaking existing code. In strict mode, these become errors.
//!
//! See: doc/plan/manual_memory_safety_plan.md

use simple_parser::Span;

/// Memory warning codes for the phased migration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum MemoryWarningCode {
    /// W1001: Shared pointer mutation
    /// Trigger: Mutating through a `*T` shared pointer
    /// Fix: Use COW pattern (into_unique or with_* methods)
    W1001,

    /// W1002: Unique pointer copied implicitly
    /// Trigger: Copying a `&T` unique pointer without explicit move/clone
    /// Fix: Use `move` keyword or `.clone()` method
    W1002,

    /// W1003: Mutable binding with shared type
    /// Trigger: `var x: *T = ...` (mutable binding of shared pointer)
    /// Fix: Use `val` instead of `var`, or use unique pointer
    W1003,

    /// W1004: Borrow escapes scope
    /// Trigger: Returning a borrow/reference that outlives its owner
    /// Fix: Return owned value or transfer ownership
    W1004,

    /// W1005: Potential reference cycle in RC graph
    /// Trigger: Cyclic reference through `*T` shared pointers
    /// Fix: Use weak pointer (`-T`) to break cycle
    W1005,

    /// W1006: Missing mut capability for mutation
    /// Trigger: Mutating a value without `mut` capability
    /// Fix: Add `mut` to parameter or variable type
    W1006,
}

impl MemoryWarningCode {
    /// Get the numeric code (for display)
    pub fn code(&self) -> u32 {
        match self {
            MemoryWarningCode::W1001 => 1001,
            MemoryWarningCode::W1002 => 1002,
            MemoryWarningCode::W1003 => 1003,
            MemoryWarningCode::W1004 => 1004,
            MemoryWarningCode::W1005 => 1005,
            MemoryWarningCode::W1006 => 1006,
        }
    }

    /// Get a short description of the warning
    pub fn description(&self) -> &'static str {
        match self {
            MemoryWarningCode::W1001 => "shared pointer mutation",
            MemoryWarningCode::W1002 => "implicit copy of unique pointer",
            MemoryWarningCode::W1003 => "mutable binding with shared type",
            MemoryWarningCode::W1004 => "borrow escapes scope",
            MemoryWarningCode::W1005 => "potential reference cycle",
            MemoryWarningCode::W1006 => "mutation without mut capability",
        }
    }

    /// Get a suggested fix for the warning
    pub fn suggested_fix(&self) -> &'static str {
        match self {
            MemoryWarningCode::W1001 => "use COW pattern: `val updated = shared.with_field(value)`",
            MemoryWarningCode::W1002 => "use explicit `move x` or `x.clone()`",
            MemoryWarningCode::W1003 => "use `val` instead of `var`, or use unique pointer `&T`",
            MemoryWarningCode::W1004 => "return owned value or transfer ownership with `move`",
            MemoryWarningCode::W1005 => "use weak pointer `-T` to break cycle",
            MemoryWarningCode::W1006 => "add `mut` capability to parameter or binding",
        }
    }
}

impl std::fmt::Display for MemoryWarningCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "W{}", self.code())
    }
}

/// A memory safety warning with location and context
#[derive(Debug, Clone)]
pub struct MemoryWarning {
    /// The warning code
    pub code: MemoryWarningCode,

    /// Source location of the violation
    pub span: Span,

    /// Additional context message
    pub context: Option<String>,

    /// Type name involved (if applicable)
    pub type_name: Option<String>,

    /// Variable or field name involved (if applicable)
    pub name: Option<String>,
}

impl MemoryWarning {
    /// Create a new memory warning
    pub fn new(code: MemoryWarningCode, span: Span) -> Self {
        Self {
            code,
            span,
            context: None,
            type_name: None,
            name: None,
        }
    }

    /// Add context to the warning
    pub fn with_context(mut self, context: impl Into<String>) -> Self {
        self.context = Some(context.into());
        self
    }

    /// Add type name to the warning
    pub fn with_type(mut self, type_name: impl Into<String>) -> Self {
        self.type_name = Some(type_name.into());
        self
    }

    /// Add variable/field name to the warning
    pub fn with_name(mut self, name: impl Into<String>) -> Self {
        self.name = Some(name.into());
        self
    }

    /// Format the warning for display
    pub fn format(&self, source_file: &str) -> String {
        let mut msg = format!(
            "{}:{}:{}: warning[{}]: {}",
            source_file,
            self.span.line,
            self.span.column,
            self.code,
            self.code.description()
        );

        if let Some(ref name) = self.name {
            msg.push_str(&format!(" ({})", name));
        }

        if let Some(ref type_name) = self.type_name {
            msg.push_str(&format!(" [type: {}]", type_name));
        }

        msg.push_str(&format!("\n  help: {}", self.code.suggested_fix()));

        if let Some(ref context) = self.context {
            msg.push_str(&format!("\n  note: {}", context));
        }

        msg
    }
}

/// Collector for memory warnings during compilation
#[derive(Debug, Default)]
pub struct MemoryWarningCollector {
    warnings: Vec<MemoryWarning>,
    /// Whether to treat warnings as errors (strict mode)
    strict_mode: bool,
}

impl MemoryWarningCollector {
    /// Create a new warning collector
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a warning collector in strict mode
    pub fn strict() -> Self {
        Self {
            warnings: Vec::new(),
            strict_mode: true,
        }
    }

    /// Set strict mode
    pub fn set_strict(&mut self, strict: bool) {
        self.strict_mode = strict;
    }

    /// Check if in strict mode
    pub fn is_strict(&self) -> bool {
        self.strict_mode
    }

    /// Add a warning
    pub fn warn(&mut self, warning: MemoryWarning) {
        self.warnings.push(warning);
    }

    /// Convenience: warn about shared pointer mutation (W1001)
    pub fn warn_shared_mutation(&mut self, span: Span, type_name: &str, field_name: &str) {
        self.warn(
            MemoryWarning::new(MemoryWarningCode::W1001, span)
                .with_type(type_name)
                .with_name(field_name)
                .with_context("shared pointers (*T) are read-only in strict mode"),
        );
    }

    /// Convenience: warn about unique pointer copy (W1002)
    pub fn warn_unique_copied(&mut self, span: Span, var_name: &str) {
        self.warn(
            MemoryWarning::new(MemoryWarningCode::W1002, span)
                .with_name(var_name)
                .with_context("unique pointers (&T) are move-only"),
        );
    }

    /// Convenience: warn about var with shared type (W1003)
    pub fn warn_mutable_shared(&mut self, span: Span, var_name: &str, type_name: &str) {
        self.warn(
            MemoryWarning::new(MemoryWarningCode::W1003, span)
                .with_name(var_name)
                .with_type(type_name)
                .with_context("shared pointers cannot be reassigned"),
        );
    }

    /// Convenience: warn about escaping borrow (W1004)
    pub fn warn_escaping_borrow(&mut self, span: Span, owner_scope: &str) {
        self.warn(
            MemoryWarning::new(MemoryWarningCode::W1004, span)
                .with_context(format!("borrow outlives owner in {}", owner_scope)),
        );
    }

    /// Convenience: warn about potential cycle (W1005)
    pub fn warn_potential_cycle(&mut self, span: Span, type_name: &str) {
        self.warn(
            MemoryWarning::new(MemoryWarningCode::W1005, span)
                .with_type(type_name)
                .with_context("reference cycles cause memory leaks with shared pointers"),
        );
    }

    /// Convenience: warn about missing mut (W1006)
    pub fn warn_missing_mut(&mut self, span: Span, name: &str) {
        self.warn(
            MemoryWarning::new(MemoryWarningCode::W1006, span)
                .with_name(name)
                .with_context("mutation requires exclusive (mut) access"),
        );
    }

    /// Get all collected warnings
    pub fn warnings(&self) -> &[MemoryWarning] {
        &self.warnings
    }

    /// Get the number of warnings
    pub fn count(&self) -> usize {
        self.warnings.len()
    }

    /// Check if there are any warnings
    pub fn has_warnings(&self) -> bool {
        !self.warnings.is_empty()
    }

    /// Clear all warnings
    pub fn clear(&mut self) {
        self.warnings.clear();
    }

    /// Format all warnings for display
    pub fn format_all(&self, source_file: &str) -> String {
        self.warnings
            .iter()
            .map(|w| w.format(source_file))
            .collect::<Vec<_>>()
            .join("\n\n")
    }

    /// Get warnings grouped by code
    pub fn by_code(&self) -> std::collections::HashMap<MemoryWarningCode, Vec<&MemoryWarning>> {
        let mut map = std::collections::HashMap::new();
        for warning in &self.warnings {
            map.entry(warning.code.clone())
                .or_insert_with(Vec::new)
                .push(warning);
        }
        map
    }

    /// Get summary statistics
    pub fn summary(&self) -> WarningSummary {
        let by_code = self.by_code();
        WarningSummary {
            total: self.warnings.len(),
            w1001: by_code.get(&MemoryWarningCode::W1001).map_or(0, |v| v.len()),
            w1002: by_code.get(&MemoryWarningCode::W1002).map_or(0, |v| v.len()),
            w1003: by_code.get(&MemoryWarningCode::W1003).map_or(0, |v| v.len()),
            w1004: by_code.get(&MemoryWarningCode::W1004).map_or(0, |v| v.len()),
            w1005: by_code.get(&MemoryWarningCode::W1005).map_or(0, |v| v.len()),
            w1006: by_code.get(&MemoryWarningCode::W1006).map_or(0, |v| v.len()),
        }
    }
}

/// Summary of warning counts by type
#[derive(Debug, Clone, Default)]
pub struct WarningSummary {
    pub total: usize,
    pub w1001: usize,
    pub w1002: usize,
    pub w1003: usize,
    pub w1004: usize,
    pub w1005: usize,
    pub w1006: usize,
}

impl std::fmt::Display for WarningSummary {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Memory Safety Warnings Summary")?;
        writeln!(f, "==============================")?;
        writeln!(f, "Total: {}", self.total)?;
        if self.w1001 > 0 {
            writeln!(f, "  W1001 (shared mutation):    {}", self.w1001)?;
        }
        if self.w1002 > 0 {
            writeln!(f, "  W1002 (unique copied):      {}", self.w1002)?;
        }
        if self.w1003 > 0 {
            writeln!(f, "  W1003 (var *T):             {}", self.w1003)?;
        }
        if self.w1004 > 0 {
            writeln!(f, "  W1004 (escaping borrow):    {}", self.w1004)?;
        }
        if self.w1005 > 0 {
            writeln!(f, "  W1005 (potential cycle):    {}", self.w1005)?;
        }
        if self.w1006 > 0 {
            writeln!(f, "  W1006 (missing mut):        {}", self.w1006)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn test_span() -> Span {
        Span::new(0, 10, 1, 1)
    }

    #[test]
    fn test_warning_codes() {
        assert_eq!(MemoryWarningCode::W1001.code(), 1001);
        assert_eq!(MemoryWarningCode::W1006.code(), 1006);
    }

    #[test]
    fn test_warning_format() {
        let warning = MemoryWarning::new(MemoryWarningCode::W1001, test_span())
            .with_type("*Data")
            .with_name("value");

        let formatted = warning.format("test.spl");
        assert!(formatted.contains("W1001"));
        assert!(formatted.contains("shared pointer mutation"));
        assert!(formatted.contains("COW pattern"));
    }

    #[test]
    fn test_collector_basic() {
        let mut collector = MemoryWarningCollector::new();

        collector.warn_shared_mutation(test_span(), "*Config", "setting");
        collector.warn_unique_copied(test_span(), "box");

        assert_eq!(collector.count(), 2);
        assert!(collector.has_warnings());
    }

    #[test]
    fn test_collector_summary() {
        let mut collector = MemoryWarningCollector::new();

        collector.warn_shared_mutation(test_span(), "*A", "x");
        collector.warn_shared_mutation(test_span(), "*B", "y");
        collector.warn_unique_copied(test_span(), "z");

        let summary = collector.summary();
        assert_eq!(summary.total, 3);
        assert_eq!(summary.w1001, 2);
        assert_eq!(summary.w1002, 1);
    }

    #[test]
    fn test_strict_mode() {
        let mut collector = MemoryWarningCollector::new();
        assert!(!collector.is_strict());

        collector.set_strict(true);
        assert!(collector.is_strict());

        let strict = MemoryWarningCollector::strict();
        assert!(strict.is_strict());
    }
}
