//! Lint checker: unknown annotation and attribute validation.

use super::super::diagnostics::LintDiagnostic;
use super::super::types::LintName;
use simple_parser::ast::{Attribute, ClassDef, Decorator, EnumDef, Expr, FunctionDef, Node, StructDef, TraitDef};

use super::LintChecker;

impl LintChecker {
    /// Check for unknown decorators and attributes across all items
    pub(super) fn check_unknown_annotations(&mut self, items: &[Node]) {
        for item in items {
            self.check_node_annotations(item);
        }
    }

    /// Check a single node's decorators and attributes
    pub(super) fn check_node_annotations(&mut self, node: &Node) {
        match node {
            Node::Function(f) => {
                let mut scoped_config = self.config.child();
                scoped_config.apply_attributes(&f.attributes);
                let original_config = std::mem::replace(&mut self.config, scoped_config);
                self.check_decorators(&f.decorators);
                self.check_attributes(&f.attributes);
                self.config = original_config;
            }
            Node::Class(c) => {
                let mut scoped_config = self.config.child();
                scoped_config.apply_attributes(&c.attributes);
                let original_config = std::mem::replace(&mut self.config, scoped_config);
                self.check_attributes(&c.attributes);
                // Check methods within the class
                for method in &c.methods {
                    let mut method_config = self.config.child();
                    method_config.apply_attributes(&method.attributes);
                    let method_original = std::mem::replace(&mut self.config, method_config);
                    self.check_decorators(&method.decorators);
                    self.check_attributes(&method.attributes);
                    self.config = method_original;
                }
                self.config = original_config;
            }
            Node::Struct(s) => {
                let mut scoped_config = self.config.child();
                scoped_config.apply_attributes(&s.attributes);
                let original_config = std::mem::replace(&mut self.config, scoped_config);
                self.check_attributes(&s.attributes);
                for method in &s.methods {
                    let mut method_config = self.config.child();
                    method_config.apply_attributes(&method.attributes);
                    let method_original = std::mem::replace(&mut self.config, method_config);
                    self.check_decorators(&method.decorators);
                    self.check_attributes(&method.attributes);
                    self.config = method_original;
                }
                self.config = original_config;
            }
            Node::Enum(e) => {
                self.check_attributes(&e.attributes);
            }
            Node::Trait(_t) => {
                // TraitDef doesn't have attributes field
            }
            Node::Impl(imp) => {
                self.check_attributes(&imp.attributes);
                for method in &imp.methods {
                    let mut method_config = self.config.child();
                    method_config.apply_attributes(&method.attributes);
                    let method_original = std::mem::replace(&mut self.config, method_config);
                    self.check_decorators(&method.decorators);
                    self.check_attributes(&method.attributes);
                    self.config = method_original;
                }
            }
            Node::ClassAlias(ca) => {
                self.check_decorators(&ca.decorators);
            }
            Node::FunctionAlias(fa) => {
                self.check_decorators(&fa.decorators);
            }
            _ => {}
        }
    }

    /// Check decorators against the known whitelist
    pub(super) fn check_decorators(&mut self, decorators: &[Decorator]) {
        for dec in decorators {
            if let Expr::Identifier(name) = &dec.name {
                if !Self::KNOWN_DECORATORS.contains(&name.as_str()) {
                    self.emit(
                        LintName::UnknownDecorator,
                        dec.span,
                        format!("unknown decorator '@{}'", name),
                        Some("Suppress with: #[allow(unknown_decorator)]".to_string()),
                    );
                }
            }
        }
    }

    /// Check attributes against the known whitelist
    pub(super) fn check_attributes(&mut self, attributes: &[Attribute]) {
        for attr in attributes {
            if !Self::KNOWN_ATTRIBUTES.contains(&attr.name.as_str()) {
                self.emit(
                    LintName::UnknownAttribute,
                    attr.span,
                    format!("unknown attribute '#[{}]'", attr.name),
                    Some("Suppress with: #[allow(unknown_attribute)]".to_string()),
                );
            }
        }
    }

}
