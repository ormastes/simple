//! Lint checks for public API type usage: bare primitives, bare bools,
//! export-outside-init, and per-node dispatch for function/struct/class/enum/trait.
//!
//! #![skip_todo]

use super::checker_core::{is_pure_math_function, LintChecker};
use super::rules::{is_bare_bool, is_primitive_type};
use super::types::LintName;
use simple_parser::ast::{ClassDef, EnumDef, FunctionDef, Node, StructDef, TraitDef, Type};
use simple_parser::token::Span;

impl LintChecker {
    pub(super) fn check_node(&mut self, node: &Node) {
        match node {
            Node::Function(func) => self.check_function(func),
            Node::Struct(s) => self.check_struct(s),
            Node::Class(c) => self.check_class(c),
            Node::Enum(e) => self.check_enum(e),
            Node::Trait(t) => self.check_trait(t),
            _ => {}
        }
    }

    /// Check for export statements outside of __init__.spl files
    pub(super) fn check_export_outside_init(&mut self, items: &[Node], source_file: &std::path::Path) {
        // Check if this is an __init__.spl file
        let filename = source_file.file_name().and_then(|f| f.to_str()).unwrap_or("");

        if filename == "__init__.spl" {
            return; // Exports are allowed in __init__.spl
        }

        // Exports are allowed in test/spec files (they re-export test utilities)
        if filename.ends_with("_spec.spl") || filename.ends_with("_test.spl") {
            return;
        }

        // Scan for ExportUseStmt nodes
        fn check_for_exports(checker: &mut LintChecker, items: &[Node], source_file: &std::path::Path) {
            for node in items {
                match node {
                    Node::ExportUseStmt(export_stmt) => {
                        let file_display = source_file.display().to_string();
                        let suggestion = if let Some(parent) = source_file.parent() {
                            let init_path = parent.join("__init__.spl");
                            format!("move this export to {} (the directory manifest)", init_path.display())
                        } else {
                            "move this export to the directory's __init__.spl file".to_string()
                        };

                        checker.emit(
                            LintName::ExportOutsideInit,
                            export_stmt.span,
                            format!(
                                "export statement not allowed in regular .spl files (found in {})",
                                file_display
                            ),
                            Some(suggestion),
                        );
                    }
                    // Recursively check inline modules
                    Node::ModDecl(mod_decl) => {
                        if let Some(ref body) = mod_decl.body {
                            check_for_exports(checker, body, source_file);
                        }
                    }
                    // Check impl blocks
                    Node::Impl(_impl_block) => {
                        // impl blocks don't contain top-level exports, but check for completeness
                    }
                    _ => {}
                }
            }
        }

        check_for_exports(self, items, source_file);
    }

    /// Check a function definition
    pub(super) fn check_function(&mut self, func: &FunctionDef) {
        // Only check public functions
        if !func.visibility.is_public() {
            return;
        }

        // Exempt pure math functions where all params + return are the same
        // bare numeric primitive (e.g., fn abs(x: f64) -> f64).
        if is_pure_math_function(func) {
            return;
        }

        // Create scoped config with function attributes
        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&func.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check parameters
        for param in &func.params {
            if let Some(ref ty) = param.ty {
                self.check_type_in_public_api(ty, param.span, &param.name, "parameter");
            }
        }

        // Check return type
        if let Some(ref ret_ty) = func.return_type {
            self.check_type_in_public_api(ret_ty, func.span, &func.name, "return type");
        }

        // Restore original config
        self.config = original_config;
    }

    /// Check a struct definition
    pub(super) fn check_struct(&mut self, s: &StructDef) {
        if !s.visibility.is_public() {
            return;
        }

        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&s.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check public fields
        for field in &s.fields {
            if field.visibility.is_public() {
                self.check_type_in_public_api(&field.ty, field.span, &field.name, "field");
            }
        }

        // Check public methods
        for method in &s.methods {
            if method.visibility.is_public() {
                self.check_function(method);
            }
        }

        self.config = original_config;
    }

    /// Check a class definition
    pub(super) fn check_class(&mut self, c: &ClassDef) {
        if !c.visibility.is_public() {
            return;
        }

        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&c.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check public fields
        for field in &c.fields {
            if field.visibility.is_public() {
                self.check_type_in_public_api(&field.ty, field.span, &field.name, "field");
            }
        }

        // Check public methods
        for method in &c.methods {
            if method.visibility.is_public() {
                self.check_function(method);
            }
        }

        self.config = original_config;
    }

    /// Check an enum definition
    pub(super) fn check_enum(&mut self, e: &EnumDef) {
        if !e.visibility.is_public() {
            return;
        }

        let mut scoped_config = self.config.child();
        scoped_config.apply_attributes(&e.attributes);
        let original_config = std::mem::replace(&mut self.config, scoped_config);

        // Check variant fields
        for variant in &e.variants {
            if let Some(ref fields) = variant.fields {
                for (i, field) in fields.iter().enumerate() {
                    let field_desc = match &field.name {
                        Some(name) => format!("{}::{}.{}", e.name, variant.name, name),
                        None => format!("{}::{}.{}", e.name, variant.name, i),
                    };
                    self.check_type_in_public_api(&field.ty, variant.span, &field_desc, "variant field");
                }
            }
        }

        self.config = original_config;
    }

    /// Check a trait definition
    pub(super) fn check_trait(&mut self, t: &TraitDef) {
        if !t.visibility.is_public() {
            return;
        }

        // TraitDef doesn't have attributes field, so use current config
        // Check method signatures
        for method in &t.methods {
            // Trait methods are implicitly public
            for param in &method.params {
                if let Some(ref ty) = param.ty {
                    self.check_type_in_public_api(ty, param.span, &param.name, "parameter");
                }
            }
            if let Some(ref ret_ty) = method.return_type {
                self.check_type_in_public_api(ret_ty, method.span, &method.name, "return type");
            }
        }
    }

    /// Check a type used in a public API
    pub(super) fn check_type_in_public_api(&mut self, ty: &Type, span: Span, name: &str, context: &str) {
        // Check for bare bool (more specific lint)
        if is_bare_bool(ty) {
            self.emit(
                LintName::BareBool,
                span,
                format!("bare `bool` in public API {} `{}`", context, name),
                Some("consider using an enum with descriptive variants instead".to_string()),
            );
        }

        // Check for any primitive type
        if is_primitive_type(ty) {
            let type_name = match ty {
                Type::Simple(n) => n.as_str(),
                _ => "primitive",
            };
            self.emit(
                LintName::PrimitiveApi,
                span,
                format!("bare primitive `{}` in public API {} `{}`", type_name, context, name),
                Some(format!(
                    "consider using a unit type or newtype wrapper instead of `{}`",
                    type_name
                )),
            );
        }

        // Recursively check nested types
        match ty {
            Type::Array { element, .. } => {
                self.check_type_in_public_api(element, span, name, context);
            }
            Type::Tuple(types) => {
                for t in types {
                    self.check_type_in_public_api(t, span, name, context);
                }
            }
            Type::Generic { args, .. } => {
                for arg in args {
                    self.check_type_in_public_api(arg, span, name, context);
                }
            }
            Type::Function { params, ret } => {
                for p in params {
                    self.check_type_in_public_api(p, span, name, context);
                }
                if let Some(r) = ret {
                    self.check_type_in_public_api(r, span, name, context);
                }
            }
            Type::Optional(inner) => {
                self.check_type_in_public_api(inner, span, name, context);
            }
            Type::Union(types) => {
                for t in types {
                    self.check_type_in_public_api(t, span, name, context);
                }
            }
            Type::Pointer { inner, .. } => {
                self.check_type_in_public_api(inner, span, name, context);
            }
            Type::Simd { element, .. } => {
                self.check_type_in_public_api(element, span, name, context);
            }
            _ => {}
        }
    }
}
