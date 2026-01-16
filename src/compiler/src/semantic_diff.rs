//! Semantic Diff Tool (#889)
//!
//! Compares AST/HIR instead of text to detect semantic changes.
//! Reports type changes, control flow modifications, and structural differences.

use serde::{Deserialize, Serialize};
use simple_parser::ast::{FunctionDef, Module as AstModule, Node, Type, Visibility};
use std::collections::{HashMap, HashSet};

/// Result of semantic diff comparison
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticDiff {
    /// Path to the compared module
    pub module_path: String,
    /// Changes detected
    pub changes: Vec<SemanticChange>,
    /// Summary statistics
    pub summary: DiffSummary,
}

/// Summary of diff statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DiffSummary {
    /// Total number of changes
    pub total_changes: usize,
    /// Functions added
    pub functions_added: usize,
    /// Functions removed
    pub functions_removed: usize,
    /// Functions modified
    pub functions_modified: usize,
    /// Classes added
    pub classes_added: usize,
    /// Classes removed
    pub classes_removed: usize,
    /// Classes modified
    pub classes_modified: usize,
    /// Type changes
    pub type_changes: usize,
    /// Control flow changes
    pub control_flow_changes: usize,
}

impl Default for DiffSummary {
    fn default() -> Self {
        Self {
            total_changes: 0,
            functions_added: 0,
            functions_removed: 0,
            functions_modified: 0,
            classes_added: 0,
            classes_removed: 0,
            classes_modified: 0,
            type_changes: 0,
            control_flow_changes: 0,
        }
    }
}

/// A semantic change detected between two versions
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SemanticChange {
    /// Type of change
    pub kind: ChangeKind,
    /// Symbol affected
    pub symbol: String,
    /// Description of the change
    pub description: String,
    /// Old value (if applicable)
    pub old_value: Option<String>,
    /// New value (if applicable)
    pub new_value: Option<String>,
    /// Impact level
    pub impact: ImpactLevel,
}

/// Kind of semantic change
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChangeKind {
    /// Function added
    FunctionAdded,
    /// Function removed
    FunctionRemoved,
    /// Function signature changed
    SignatureChanged,
    /// Function visibility changed
    VisibilityChanged,
    /// Return type changed
    ReturnTypeChanged,
    /// Parameter added
    ParameterAdded,
    /// Parameter removed
    ParameterRemoved,
    /// Parameter type changed
    ParameterTypeChanged,
    /// Class added
    ClassAdded,
    /// Class removed
    ClassRemoved,
    /// Field added
    FieldAdded,
    /// Field removed
    FieldRemoved,
    /// Field type changed
    FieldTypeChanged,
    /// Method added
    MethodAdded,
    /// Method removed
    MethodRemoved,
    /// Trait added
    TraitAdded,
    /// Trait removed
    TraitRemoved,
    /// Control flow changed
    ControlFlowChanged,
    /// Effect annotation changed
    EffectChanged,
}

/// Impact level of a change
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum ImpactLevel {
    /// Breaking change (affects API)
    Breaking,
    /// Major change (significant behavior change)
    Major,
    /// Minor change (implementation detail)
    Minor,
    /// Informational (no functional impact)
    Info,
}

/// Semantic differ for AST modules
pub struct SemanticDiffer {
    /// Path to the module being compared
    module_path: String,
}

impl SemanticDiffer {
    /// Create a new semantic differ
    pub fn new(module_path: impl Into<String>) -> Self {
        Self {
            module_path: module_path.into(),
        }
    }

    /// Compare two AST modules and detect semantic differences
    pub fn diff_modules(&self, old: &AstModule, new: &AstModule) -> SemanticDiff {
        let mut changes = Vec::new();
        let mut summary = DiffSummary::default();

        // Build symbol tables for quick lookup
        let old_symbols = self.build_symbol_table(old);
        let new_symbols = self.build_symbol_table(new);

        // Detect additions
        for (name, node) in &new_symbols {
            if !old_symbols.contains_key(name) {
                if let Some(change) = self.detect_addition(name, node) {
                    self.update_summary(&mut summary, &change);
                    changes.push(change);
                }
            }
        }

        // Detect removals
        for (name, node) in &old_symbols {
            if !new_symbols.contains_key(name) {
                if let Some(change) = self.detect_removal(name, node) {
                    self.update_summary(&mut summary, &change);
                    changes.push(change);
                }
            }
        }

        // Detect modifications
        for (name, old_node) in &old_symbols {
            if let Some(new_node) = new_symbols.get(name) {
                let node_changes = self.diff_nodes(name, old_node, new_node);
                for change in node_changes {
                    self.update_summary(&mut summary, &change);
                    changes.push(change);
                }
            }
        }

        summary.total_changes = changes.len();

        SemanticDiff {
            module_path: self.module_path.clone(),
            changes,
            summary,
        }
    }

    fn build_symbol_table(&self, module: &AstModule) -> HashMap<String, Node> {
        let mut symbols = HashMap::new();
        for node in &module.items {
            if let Some(name) = self.get_node_name(node) {
                symbols.insert(name, node.clone());
            }
        }
        symbols
    }

    fn get_node_name(&self, node: &Node) -> Option<String> {
        match node {
            Node::Function(f) => Some(f.name.clone()),
            Node::Class(c) => Some(c.name.clone()),
            Node::Struct(s) => Some(s.name.clone()),
            Node::Trait(t) => Some(t.name.clone()),
            Node::Enum(e) => Some(e.name.clone()),
            _ => None,
        }
    }

    fn detect_addition(&self, name: &str, node: &Node) -> Option<SemanticChange> {
        match node {
            Node::Function(f) => Some(SemanticChange {
                kind: ChangeKind::FunctionAdded,
                symbol: name.to_string(),
                description: format!("Function '{}' added", name),
                old_value: None,
                new_value: Some(self.format_function_signature(f)),
                impact: if f.visibility.is_public() {
                    ImpactLevel::Breaking
                } else {
                    ImpactLevel::Minor
                },
            }),
            Node::Class(c) => Some(SemanticChange {
                kind: ChangeKind::ClassAdded,
                symbol: name.to_string(),
                description: format!("Class '{}' added", name),
                old_value: None,
                new_value: Some(format!("class {}", name)),
                impact: if c.visibility.is_public() {
                    ImpactLevel::Breaking
                } else {
                    ImpactLevel::Minor
                },
            }),
            Node::Trait(t) => Some(SemanticChange {
                kind: ChangeKind::TraitAdded,
                symbol: name.to_string(),
                description: format!("Trait '{}' added", name),
                old_value: None,
                new_value: Some(format!("trait {}", name)),
                impact: ImpactLevel::Breaking,
            }),
            _ => None,
        }
    }

    fn detect_removal(&self, name: &str, node: &Node) -> Option<SemanticChange> {
        match node {
            Node::Function(f) => Some(SemanticChange {
                kind: ChangeKind::FunctionRemoved,
                symbol: name.to_string(),
                description: format!("Function '{}' removed", name),
                old_value: Some(self.format_function_signature(f)),
                new_value: None,
                impact: if f.visibility.is_public() {
                    ImpactLevel::Breaking
                } else {
                    ImpactLevel::Minor
                },
            }),
            Node::Class(c) => Some(SemanticChange {
                kind: ChangeKind::ClassRemoved,
                symbol: name.to_string(),
                description: format!("Class '{}' removed", name),
                old_value: Some(format!("class {}", name)),
                new_value: None,
                impact: if c.visibility.is_public() {
                    ImpactLevel::Breaking
                } else {
                    ImpactLevel::Minor
                },
            }),
            Node::Trait(_) => Some(SemanticChange {
                kind: ChangeKind::TraitRemoved,
                symbol: name.to_string(),
                description: format!("Trait '{}' removed", name),
                old_value: Some(format!("trait {}", name)),
                new_value: None,
                impact: ImpactLevel::Breaking,
            }),
            _ => None,
        }
    }

    fn diff_nodes(&self, name: &str, old: &Node, new: &Node) -> Vec<SemanticChange> {
        match (old, new) {
            (Node::Function(old_f), Node::Function(new_f)) => self.diff_functions(name, old_f, new_f),
            (Node::Class(old_c), Node::Class(new_c)) => self.diff_classes(name, old_c, new_c),
            _ => vec![],
        }
    }

    fn diff_functions(&self, name: &str, old: &FunctionDef, new: &FunctionDef) -> Vec<SemanticChange> {
        let mut changes = Vec::new();

        // Check visibility change
        if old.visibility != new.visibility {
            changes.push(SemanticChange {
                kind: ChangeKind::VisibilityChanged,
                symbol: name.to_string(),
                description: format!("Function '{}' visibility changed", name),
                old_value: Some(format!("{:?}", old.visibility)),
                new_value: Some(format!("{:?}", new.visibility)),
                impact: ImpactLevel::Breaking,
            });
        }

        // Check return type change
        if !self.types_equal(&old.return_type, &new.return_type) {
            changes.push(SemanticChange {
                kind: ChangeKind::ReturnTypeChanged,
                symbol: name.to_string(),
                description: format!("Function '{}' return type changed", name),
                old_value: old.return_type.as_ref().map(|t| self.format_type(t)),
                new_value: new.return_type.as_ref().map(|t| self.format_type(t)),
                impact: if old.visibility.is_public() {
                    ImpactLevel::Breaking
                } else {
                    ImpactLevel::Major
                },
            });
        }

        // Check parameter changes
        if old.params.len() != new.params.len() {
            let diff = new.params.len() as i32 - old.params.len() as i32;
            if diff > 0 {
                changes.push(SemanticChange {
                    kind: ChangeKind::ParameterAdded,
                    symbol: name.to_string(),
                    description: format!("Function '{}' has {} new parameter(s)", name, diff),
                    old_value: Some(old.params.len().to_string()),
                    new_value: Some(new.params.len().to_string()),
                    impact: if old.visibility.is_public() {
                        ImpactLevel::Breaking
                    } else {
                        ImpactLevel::Major
                    },
                });
            } else {
                changes.push(SemanticChange {
                    kind: ChangeKind::ParameterRemoved,
                    symbol: name.to_string(),
                    description: format!("Function '{}' has {} fewer parameter(s)", name, -diff),
                    old_value: Some(old.params.len().to_string()),
                    new_value: Some(new.params.len().to_string()),
                    impact: if old.visibility.is_public() {
                        ImpactLevel::Breaking
                    } else {
                        ImpactLevel::Major
                    },
                });
            }
        } else {
            // Check parameter type changes
            for (i, (old_p, new_p)) in old.params.iter().zip(new.params.iter()).enumerate() {
                if !self.types_equal(&old_p.ty, &new_p.ty) {
                    changes.push(SemanticChange {
                        kind: ChangeKind::ParameterTypeChanged,
                        symbol: format!("{}[param:{}]", name, i),
                        description: format!("Function '{}' parameter '{}' type changed", name, old_p.name),
                        old_value: old_p.ty.as_ref().map(|t| self.format_type(t)),
                        new_value: new_p.ty.as_ref().map(|t| self.format_type(t)),
                        impact: if old.visibility.is_public() {
                            ImpactLevel::Breaking
                        } else {
                            ImpactLevel::Major
                        },
                    });
                }
            }
        }

        // Check effect changes
        if old.effects != new.effects {
            changes.push(SemanticChange {
                kind: ChangeKind::EffectChanged,
                symbol: name.to_string(),
                description: format!("Function '{}' effects changed", name),
                old_value: Some(format!("{:?}", old.effects)),
                new_value: Some(format!("{:?}", new.effects)),
                impact: ImpactLevel::Major,
            });
        }

        changes
    }

    fn diff_classes(
        &self,
        name: &str,
        old: &simple_parser::ast::ClassDef,
        new: &simple_parser::ast::ClassDef,
    ) -> Vec<SemanticChange> {
        let mut changes = Vec::new();

        // Check visibility change
        if old.visibility != new.visibility {
            changes.push(SemanticChange {
                kind: ChangeKind::VisibilityChanged,
                symbol: name.to_string(),
                description: format!("Class '{}' visibility changed", name),
                old_value: Some(format!("{:?}", old.visibility)),
                new_value: Some(format!("{:?}", new.visibility)),
                impact: ImpactLevel::Breaking,
            });
        }

        // Build field maps
        let old_fields: HashMap<_, _> = old.fields.iter().map(|f| (&f.name, f)).collect();
        let new_fields: HashMap<_, _> = new.fields.iter().map(|f| (&f.name, f)).collect();

        // Detect field additions
        for (field_name, _) in &new_fields {
            if !old_fields.contains_key(field_name) {
                changes.push(SemanticChange {
                    kind: ChangeKind::FieldAdded,
                    symbol: format!("{}.{}", name, field_name),
                    description: format!("Class '{}' field '{}' added", name, field_name),
                    old_value: None,
                    new_value: Some(field_name.to_string()),
                    impact: if old.visibility.is_public() {
                        ImpactLevel::Breaking
                    } else {
                        ImpactLevel::Minor
                    },
                });
            }
        }

        // Detect field removals and type changes
        for (field_name, old_field) in &old_fields {
            if let Some(new_field) = new_fields.get(field_name) {
                // Field exists in both, check type change
                if !self.types_equal_direct(&old_field.ty, &new_field.ty) {
                    changes.push(SemanticChange {
                        kind: ChangeKind::FieldTypeChanged,
                        symbol: format!("{}.{}", name, field_name),
                        description: format!("Class '{}' field '{}' type changed", name, field_name),
                        old_value: Some(self.format_type(&old_field.ty)),
                        new_value: Some(self.format_type(&new_field.ty)),
                        impact: if old.visibility.is_public() {
                            ImpactLevel::Breaking
                        } else {
                            ImpactLevel::Major
                        },
                    });
                }
            } else {
                // Field removed
                changes.push(SemanticChange {
                    kind: ChangeKind::FieldRemoved,
                    symbol: format!("{}.{}", name, field_name),
                    description: format!("Class '{}' field '{}' removed", name, field_name),
                    old_value: Some(field_name.to_string()),
                    new_value: None,
                    impact: if old.visibility.is_public() {
                        ImpactLevel::Breaking
                    } else {
                        ImpactLevel::Minor
                    },
                });
            }
        }

        // Build method maps
        let old_methods: HashMap<_, _> = old.methods.iter().map(|m| (&m.name, m)).collect();
        let new_methods: HashMap<_, _> = new.methods.iter().map(|m| (&m.name, m)).collect();

        // Detect method additions
        for (method_name, _) in &new_methods {
            if !old_methods.contains_key(method_name) {
                changes.push(SemanticChange {
                    kind: ChangeKind::MethodAdded,
                    symbol: format!("{}.{}", name, method_name),
                    description: format!("Class '{}' method '{}' added", name, method_name),
                    old_value: None,
                    new_value: Some(method_name.to_string()),
                    impact: if old.visibility.is_public() {
                        ImpactLevel::Breaking
                    } else {
                        ImpactLevel::Minor
                    },
                });
            }
        }

        // Detect method removals
        for (method_name, _) in &old_methods {
            if !new_methods.contains_key(method_name) {
                changes.push(SemanticChange {
                    kind: ChangeKind::MethodRemoved,
                    symbol: format!("{}.{}", name, method_name),
                    description: format!("Class '{}' method '{}' removed", name, method_name),
                    old_value: Some(method_name.to_string()),
                    new_value: None,
                    impact: if old.visibility.is_public() {
                        ImpactLevel::Breaking
                    } else {
                        ImpactLevel::Minor
                    },
                });
            }
        }

        changes
    }

    fn types_equal(&self, old: &Option<Type>, new: &Option<Type>) -> bool {
        match (old, new) {
            (None, None) => true,
            (Some(old_t), Some(new_t)) => self.types_equal_direct(old_t, new_t),
            _ => false,
        }
    }

    fn types_equal_direct(&self, old: &Type, new: &Type) -> bool {
        // Simplified type comparison - could be more sophisticated
        self.format_type(old) == self.format_type(new)
    }

    fn format_type(&self, ty: &Type) -> String {
        match ty {
            Type::Simple(name) => name.clone(),
            Type::Generic { name, args } => {
                format!(
                    "{}<{}>",
                    name,
                    args.iter().map(|t| self.format_type(t)).collect::<Vec<_>>().join(", ")
                )
            }
            Type::Array { element, .. } => format!("[{}]", self.format_type(element)),
            Type::Optional(inner) => format!("{}?", self.format_type(inner)),
            Type::Tuple(types) => format!(
                "({})",
                types.iter().map(|t| self.format_type(t)).collect::<Vec<_>>().join(", ")
            ),
            _ => format!("{:?}", ty),
        }
    }

    fn format_function_signature(&self, func: &FunctionDef) -> String {
        let params = func
            .params
            .iter()
            .map(|p| {
                if let Some(ty) = &p.ty {
                    format!("{}: {}", p.name, self.format_type(ty))
                } else {
                    p.name.clone()
                }
            })
            .collect::<Vec<_>>()
            .join(", ");

        let ret = func
            .return_type
            .as_ref()
            .map(|t| format!(" -> {}", self.format_type(t)))
            .unwrap_or_default();

        format!("fn {}({}){}", func.name, params, ret)
    }

    fn update_summary(&self, summary: &mut DiffSummary, change: &SemanticChange) {
        match change.kind {
            ChangeKind::FunctionAdded => summary.functions_added += 1,
            ChangeKind::FunctionRemoved => summary.functions_removed += 1,
            ChangeKind::SignatureChanged
            | ChangeKind::ReturnTypeChanged
            | ChangeKind::ParameterAdded
            | ChangeKind::ParameterRemoved
            | ChangeKind::ParameterTypeChanged => summary.functions_modified += 1,
            ChangeKind::ClassAdded => summary.classes_added += 1,
            ChangeKind::ClassRemoved => summary.classes_removed += 1,
            ChangeKind::FieldAdded
            | ChangeKind::FieldRemoved
            | ChangeKind::FieldTypeChanged
            | ChangeKind::MethodAdded
            | ChangeKind::MethodRemoved => summary.classes_modified += 1,
            ChangeKind::ReturnTypeChanged | ChangeKind::ParameterTypeChanged | ChangeKind::FieldTypeChanged => {
                summary.type_changes += 1
            }
            ChangeKind::ControlFlowChanged => summary.control_flow_changes += 1,
            _ => {}
        }
    }

    /// Format diff output as human-readable text
    pub fn format_text(diff: &SemanticDiff) -> String {
        let mut output = String::new();

        output.push_str(&format!("Semantic Diff: {}\n", diff.module_path));
        output.push_str(&format!("Total changes: {}\n\n", diff.summary.total_changes));

        if diff.changes.is_empty() {
            output.push_str("No semantic changes detected.\n");
            return output;
        }

        // Group changes by kind
        for change in &diff.changes {
            let impact_marker = match change.impact {
                ImpactLevel::Breaking => "⚠️ BREAKING",
                ImpactLevel::Major => "⚡ MAJOR",
                ImpactLevel::Minor => "ℹ️  MINOR",
                ImpactLevel::Info => "ℹ️  INFO",
            };

            output.push_str(&format!("{} {}\n", impact_marker, change.description));

            if let Some(old) = &change.old_value {
                output.push_str(&format!("  - {}\n", old));
            }
            if let Some(new) = &change.new_value {
                output.push_str(&format!("  + {}\n", new));
            }
            output.push('\n');
        }

        // Summary
        output.push_str("Summary:\n");
        if diff.summary.functions_added > 0 {
            output.push_str(&format!("  Functions added: {}\n", diff.summary.functions_added));
        }
        if diff.summary.functions_removed > 0 {
            output.push_str(&format!("  Functions removed: {}\n", diff.summary.functions_removed));
        }
        if diff.summary.functions_modified > 0 {
            output.push_str(&format!("  Functions modified: {}\n", diff.summary.functions_modified));
        }
        if diff.summary.classes_added > 0 {
            output.push_str(&format!("  Classes added: {}\n", diff.summary.classes_added));
        }
        if diff.summary.classes_removed > 0 {
            output.push_str(&format!("  Classes removed: {}\n", diff.summary.classes_removed));
        }
        if diff.summary.classes_modified > 0 {
            output.push_str(&format!("  Classes modified: {}\n", diff.summary.classes_modified));
        }

        output
    }

    /// Format diff output as JSON
    pub fn format_json(diff: &SemanticDiff) -> Result<String, serde_json::Error> {
        serde_json::to_string_pretty(diff)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::*;
    use simple_parser::token::Span;

    fn make_module(items: Vec<Node>) -> AstModule {
        AstModule { name: None, items }
    }

    fn make_function(name: &str, params: usize, ret_type: Option<Type>) -> Node {
        Node::Function(FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: name.to_string(),
            visibility: Visibility::Public,
            params: (0..params)
                .map(|i| Parameter {
                    span: Span::new(0, 0, 0, 0),
                    name: format!("arg{}", i),
                    ty: Some(Type::Simple("i64".to_string())),
                    default: None,
                    mutability: Mutability::Immutable,
                    inject: false,
                    variadic: false,
                })
                .collect(),
            return_type: ret_type,
            where_clause: vec![],
            body: Block::default(),
            decorators: vec![],
            generic_params: vec![],
            effects: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            bounds_block: None,
        })
    }

    #[test]
    fn test_function_added() {
        let old = make_module(vec![]);
        let new = make_module(vec![make_function("foo", 0, None)]);

        let differ = SemanticDiffer::new("test.spl");
        let diff = differ.diff_modules(&old, &new);

        assert_eq!(diff.changes.len(), 1);
        assert_eq!(diff.changes[0].kind, ChangeKind::FunctionAdded);
        assert_eq!(diff.summary.functions_added, 1);
    }

    #[test]
    fn test_function_removed() {
        let old = make_module(vec![make_function("foo", 0, None)]);
        let new = make_module(vec![]);

        let differ = SemanticDiffer::new("test.spl");
        let diff = differ.diff_modules(&old, &new);

        assert_eq!(diff.changes.len(), 1);
        assert_eq!(diff.changes[0].kind, ChangeKind::FunctionRemoved);
        assert_eq!(diff.summary.functions_removed, 1);
    }

    #[test]
    fn test_return_type_changed() {
        let old = make_module(vec![make_function("foo", 0, None)]);
        let new = make_module(vec![make_function("foo", 0, Some(Type::Simple("bool".to_string())))]);

        let differ = SemanticDiffer::new("test.spl");
        let diff = differ.diff_modules(&old, &new);

        assert_eq!(diff.changes.len(), 1);
        assert_eq!(diff.changes[0].kind, ChangeKind::ReturnTypeChanged);
        assert_eq!(diff.changes[0].impact, ImpactLevel::Breaking);
    }

    #[test]
    fn test_parameter_added() {
        let old = make_module(vec![make_function("foo", 1, None)]);
        let new = make_module(vec![make_function("foo", 2, None)]);

        let differ = SemanticDiffer::new("test.spl");
        let diff = differ.diff_modules(&old, &new);

        assert_eq!(diff.changes.len(), 1);
        assert_eq!(diff.changes[0].kind, ChangeKind::ParameterAdded);
        assert_eq!(diff.changes[0].impact, ImpactLevel::Breaking);
    }

    #[test]
    fn test_no_changes() {
        let module = make_module(vec![make_function("foo", 1, None)]);

        let differ = SemanticDiffer::new("test.spl");
        let diff = differ.diff_modules(&module, &module);

        assert_eq!(diff.changes.len(), 0);
        assert_eq!(diff.summary.total_changes, 0);
    }
}
