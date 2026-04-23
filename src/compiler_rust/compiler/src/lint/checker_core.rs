//! Lint checker implementation for AST traversal.
//!
//! #![skip_todo]

use super::super::config::LintConfig;
use super::super::diagnostics::LintDiagnostic;
use super::super::rules::{is_bare_bool, is_primitive_type, math_primitive_name};
use super::super::types::{LintLevel, LintName};
use simple_common::diagnostic::{EasyFix, FixConfidence, Replacement};
use simple_parser::ast::{
    Argument, Attribute, ClassDef, Decorator, EnumDef, Expr, FunctionDef, Node, StructDef, TraitDef, Type,
};
use simple_parser::token::Span;
use std::collections::HashMap;
use std::path::Path;

/// Parameter info for duplicate typed args checking
#[derive(Clone, Debug)]
pub(super) struct ParamInfo {
    pub(super) name: String,
    pub(super) ty: Option<Type>,
}

/// Function signature info for call-site checking
#[derive(Clone, Debug)]
pub(super) struct FunctionInfo {
    pub(super) params: Vec<ParamInfo>,
}

/// Format a type for user-friendly display
pub(super) fn format_type(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                let args_str: Vec<String> = args.iter().map(format_type).collect();
                format!("{}<{}>", name, args_str.join(", "))
            }
        }
        Type::Array { element, size } => {
            let elem_str = format_type(element);
            match size {
                Some(s) => format!("[{}; {:?}]", elem_str, s),
                None => format!("[{}]", elem_str),
            }
        }
        Type::Optional(inner) => format!("{}?", format_type(inner)),
        Type::Tuple(types) => {
            let types_str: Vec<String> = types.iter().map(format_type).collect();
            format!("({})", types_str.join(", "))
        }
        Type::LabeledTuple(fields) => {
            let fields_str: Vec<String> = fields
                .iter()
                .map(|field| format!("{}: {}", field.label, format_type(&field.ty)))
                .collect();
            format!("({})", fields_str.join(", "))
        }
        Type::Function { params, ret } => {
            let params_str: Vec<String> = params.iter().map(format_type).collect();
            let ret_str = ret.as_ref().map(|r| format_type(r)).unwrap_or_else(|| "()".to_string());
            format!("fn({}) -> {}", params_str.join(", "), ret_str)
        }
        _ => format!("{:?}", ty),
    }
}

/// Check if a function is a "pure math function" — all parameters and the return
/// type are the *same* bare numeric primitive (e.g. `fn abs(x: f64) -> f64`).
/// Such functions are exempt from the `primitive_api` lint.
pub(super) fn is_pure_math_function(func: &FunctionDef) -> bool {
    // Must have at least one parameter
    if func.params.is_empty() {
        return false;
    }

    // Return type must be a math primitive
    let ret_name = match func.return_type {
        Some(ref ret_ty) => match math_primitive_name(ret_ty) {
            Some(name) => name,
            None => return false,
        },
        None => return false,
    };

    // Every parameter type must be the same math primitive as the return type
    for param in &func.params {
        match param.ty {
            Some(ref ty) => match math_primitive_name(ty) {
                Some(name) if name == ret_name => {}
                _ => return false,
            },
            None => return false,
        }
    }

    true
}

/// Lint checker for a compilation unit
pub struct LintChecker {
    /// Current lint configuration
    pub(super) config: LintConfig,
    /// Collected diagnostics
    pub(super) diagnostics: Vec<LintDiagnostic>,
    /// Source file path (for file-based lints)
    pub(super) source_file: Option<std::path::PathBuf>,
    /// Function registry for call-site checks (populated during check_module)
    pub(super) functions: HashMap<String, FunctionInfo>,
}

impl LintChecker {
    pub fn new() -> Self {
        Self {
            config: LintConfig::new(),
            diagnostics: Vec::new(),
            source_file: None,
            functions: HashMap::new(),
        }
    }

    pub fn with_config(config: LintConfig) -> Self {
        Self {
            config,
            diagnostics: Vec::new(),
            source_file: None,
            functions: HashMap::new(),
        }
    }

    pub fn with_source_file(mut self, source_file: Option<std::path::PathBuf>) -> Self {
        self.source_file = source_file;
        self
    }

    /// Get collected diagnostics
    pub fn diagnostics(&self) -> &[LintDiagnostic] {
        &self.diagnostics
    }

    /// Take collected diagnostics
    pub fn take_diagnostics(&mut self) -> Vec<LintDiagnostic> {
        std::mem::take(&mut self.diagnostics)
    }

    /// Export diagnostics as JSON (#903)
    pub fn to_json(&self, file: Option<String>) -> Result<String, serde_json::Error> {
        use simple_common::diagnostic::Diagnostics;

        let mut diags = Diagnostics::new();
        for lint_diag in &self.diagnostics {
            diags.push(lint_diag.to_diagnostic(file.clone()));
        }
        diags.to_json()
    }

    /// Export diagnostics as compact JSON (#903)
    pub fn to_json_compact(&self, file: Option<String>) -> Result<String, serde_json::Error> {
        use simple_common::diagnostic::Diagnostics;

        let mut diags = Diagnostics::new();
        for lint_diag in &self.diagnostics {
            diags.push(lint_diag.to_diagnostic(file.clone()));
        }
        diags.to_json_compact()
    }

    /// Check if there are any errors
    pub fn has_errors(&self) -> bool {
        self.diagnostics.iter().any(|d| d.is_error())
    }

    /// Check if there are any warnings
    pub fn has_warnings(&self) -> bool {
        self.diagnostics.iter().any(|d| d.is_warning())
    }

    /// Emit a lint diagnostic if not allowed
    pub(super) fn emit(&mut self, lint: LintName, span: Span, message: String, suggestion: Option<String>) {
        self.emit_with_fix(lint, span, message, suggestion, None);
    }

    /// Emit a lint diagnostic with an optional machine-applicable fix
    pub(super) fn emit_with_fix(
        &mut self,
        lint: LintName,
        span: Span,
        message: String,
        suggestion: Option<String>,
        easy_fix: Option<simple_common::diagnostic::EasyFix>,
    ) {
        let level = self.config.get_level(lint);
        if level == LintLevel::Allow {
            return;
        }

        let mut diagnostic = LintDiagnostic::new(lint, level, span, message);
        if let Some(s) = suggestion {
            diagnostic = diagnostic.with_suggestion(s);
        }
        if let Some(fix) = easy_fix {
            diagnostic = diagnostic.with_easy_fix(fix);
        }
        self.diagnostics.push(diagnostic);
    }

    /// Apply file-level lint directives from source.
    ///
    /// Scans the source file for standalone `#[allow(...)]`, `#[deny(...)]`,
    /// `#[warn(...)]` lines that appear before the first definition.
    /// The parser currently drops these attributes, so we pre-scan the raw source.
    fn apply_file_level_lint_directives(&mut self) {
        let source_file = match &self.source_file {
            Some(f) => f.clone(),
            None => return,
        };
        let content = match std::fs::read_to_string(&source_file) {
            Ok(c) => c,
            Err(_) => return,
        };
        for line in content.lines() {
            let trimmed = line.trim();
            // Stop scanning at first definition-like line
            if trimmed.starts_with("fn ")
                || trimmed.starts_with("pub fn ")
                || trimmed.starts_with("pub ")
                    && (trimmed.contains("fn ")
                        || trimmed.contains("struct ")
                        || trimmed.contains("class ")
                        || trimmed.contains("enum "))
                || trimmed.starts_with("struct ")
                || trimmed.starts_with("class ")
                || trimmed.starts_with("enum ")
                || trimmed.starts_with("trait ")
                || trimmed.starts_with("impl ")
                || trimmed.starts_with("extern ")
            {
                break;
            }
            // Parse #[allow(...)], #![allow(...)], #[deny(...)], #[warn(...)]
            // Both #[allow(...)] and #![allow(...)] are supported; the latter is
            // preferred as it is valid Simple parser syntax (inner module attribute).
            let allow_rest = trimmed
                .strip_prefix("#![allow(")
                .or_else(|| trimmed.strip_prefix("#[allow("));
            let deny_rest = trimmed.strip_prefix("#[deny(");
            let warn_rest = trimmed.strip_prefix("#[warn(");
            if let Some(rest) = allow_rest {
                if let Some(args) = rest.strip_suffix(")]") {
                    for lint_name in args.split(',') {
                        let lint_name = lint_name.trim();
                        if let Some(lint) = LintName::from_str(lint_name) {
                            self.config.set_level(lint, LintLevel::Allow);
                        }
                    }
                }
            } else if let Some(rest) = deny_rest {
                if let Some(args) = rest.strip_suffix(")]") {
                    for lint_name in args.split(',') {
                        let lint_name = lint_name.trim();
                        if let Some(lint) = LintName::from_str(lint_name) {
                            self.config.set_level(lint, LintLevel::Deny);
                        }
                    }
                }
            } else if let Some(rest) = warn_rest {
                if let Some(args) = rest.strip_suffix(")]") {
                    for lint_name in args.split(',') {
                        let lint_name = lint_name.trim();
                        if let Some(lint) = LintName::from_str(lint_name) {
                            self.config.set_level(lint, LintLevel::Warn);
                        }
                    }
                }
            }
        }
    }

    /// Check a module for lint violations
    pub fn check_module(&mut self, items: &[Node]) {
        // Apply file-level lint directives (e.g., #[allow(primitive_api)])
        self.apply_file_level_lint_directives();

        // First pass: collect function definitions for call-site checks
        self.collect_functions(items);

        // Run file-based lints first
        if let Some(source_file) = self.source_file.clone() {
            // Check for print in test spec files
            if source_file.to_string_lossy().ends_with("_spec.spl") {
                self.check_print_in_test_spec(items);
                // SSpec-specific lints
                self.check_sspec_print_based_tests(items);
                self.check_sspec_minimal_docstrings(&source_file);
                self.check_sspec_manual_assertions(items);
            }

            self.check_source_backed_quality_patterns(&source_file);

            // Check TODO format
            self.check_todo_format(&source_file);

            // Check for exports outside __init__.spl
            self.check_export_outside_init(items, &source_file);

            // Check for imports bypassing __init__.spl boundaries
            self.check_init_boundary(items, &source_file);

            // Check for bypass directories with code files
            self.check_bypass_validity(items, &source_file);
        }

        // Check for unknown decorators/attributes
        self.check_unknown_annotations(items);

        // Run AST-based lints
        for item in items {
            self.check_node(item);
        }

        // Check for unnamed duplicate typed args at call sites
        self.check_unnamed_duplicate_typed_args(items);

        // Check for resource leaks
        self.check_resource_leaks(items);
    }

    /// Collect function definitions for call-site checking
    fn collect_functions(&mut self, items: &[Node]) {
        fn collect_from_node(functions: &mut HashMap<String, FunctionInfo>, node: &Node) {
            match node {
                Node::Function(func) => {
                    let info = FunctionInfo {
                        params: func
                            .params
                            .iter()
                            .map(|p| ParamInfo {
                                name: p.name.clone(),
                                ty: p.ty.clone(),
                            })
                            .collect(),
                    };
                    functions.insert(func.name.clone(), info);
                }
                Node::Class(c) => {
                    // Collect methods from class
                    for method in &c.methods {
                        let info = FunctionInfo {
                            params: method
                                .params
                                .iter()
                                .filter(|p| p.name != "self")
                                .map(|p| ParamInfo {
                                    name: p.name.clone(),
                                    ty: p.ty.clone(),
                                })
                                .collect(),
                        };
                        // Store as ClassName.method_name for method lookup
                        let key = format!("{}.{}", c.name, method.name);
                        functions.insert(key, info.clone());
                        // Also store just by method name for simple lookup
                        functions.insert(method.name.clone(), info);
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        let info = FunctionInfo {
                            params: method
                                .params
                                .iter()
                                .filter(|p| p.name != "self")
                                .map(|p| ParamInfo {
                                    name: p.name.clone(),
                                    ty: p.ty.clone(),
                                })
                                .collect(),
                        };
                        let key = format!("{}.{}", s.name, method.name);
                        functions.insert(key, info.clone());
                        functions.insert(method.name.clone(), info);
                    }
                }
                Node::Impl(impl_block) => {
                    for method in &impl_block.methods {
                        let info = FunctionInfo {
                            params: method
                                .params
                                .iter()
                                .filter(|p| p.name != "self")
                                .map(|p| ParamInfo {
                                    name: p.name.clone(),
                                    ty: p.ty.clone(),
                                })
                                .collect(),
                        };
                        // Format target_type for key
                        let type_name = format!("{:?}", impl_block.target_type);
                        let key = format!("{}.{}", type_name, method.name);
                        functions.insert(key, info.clone());
                        functions.insert(method.name.clone(), info);
                    }
                }
                _ => {}
            }
        }

        for item in items {
            collect_from_node(&mut self.functions, item);
        }
    }

    /// Check a single AST node
    /// Known decorator names (whitelist)
    pub(super) const KNOWN_DECORATORS: &'static [&'static str] = &[
        "async",
        "pure",
        "io",
        "net",
        "fs",
        "unsafe",
        "verify",
        "trusted",
        "ghost",
        "auto_lean",
        "bounds",
        "extern",
        "simd",
        "inline",
        "test",
        "property_test",
        "snapshot_test",
        "deprecated",
        "generated_by",
        "Lib",
        "inject",
        "sys_inject",
        // Baremetal / low-level decorators
        "naked",
        "noreturn",
        "interrupt",
        "entry",
        "align",
        // GPU decorators
        "gpu_intrinsic",
    ];

    /// Known attribute names (whitelist)
    pub(super) const KNOWN_ATTRIBUTES: &'static [&'static str] = &[
        "allow",
        "warn",
        "deny",
        "default",
        "concurrency_mode",
        "layout",
        "pure",
        "snapshot",
        "deprecated",
        "bypass",
        "skip_todo",
        "generated",
        "inline",
        "ignore",
    ];
}
