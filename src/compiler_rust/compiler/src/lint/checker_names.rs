//! Lint checker: accessor forwarding and inherited near-miss names.

use std::collections::{HashMap, HashSet};

use simple_parser::ast::{AssignOp, Attribute, Block, ClassDef, Decorator, Expr, FunctionDef, Node};

use super::super::types::LintName;
use super::LintChecker;

#[derive(Debug, Clone, PartialEq, Eq)]
enum AccessorKind {
    Get,
    Set,
    Is,
}

#[derive(Debug, Clone)]
struct AccessorInfo<'a> {
    method: &'a FunctionDef,
    kind: AccessorKind,
    suffix: String,
    dummy: bool,
    overrides_parent: bool,
}

impl LintChecker {
    pub(super) fn check_accessor_and_parent_names(&mut self, items: &[Node]) {
        let classes: HashMap<&str, &ClassDef> = items
            .iter()
            .filter_map(|item| match item {
                Node::Class(class_def) => Some((class_def.name.as_str(), class_def)),
                _ => None,
            })
            .collect();

        for class_def in classes.values() {
            self.check_dummy_accessors(class_def, &classes);
            self.check_similar_parent_method_names(class_def, &classes);
        }
    }

    fn check_dummy_accessors<'a>(&mut self, class_def: &'a ClassDef, classes: &HashMap<&str, &'a ClassDef>) {
        let inherited = inherited_method_names(class_def, classes);
        let mut by_suffix: HashMap<String, Vec<AccessorInfo<'a>>> = HashMap::new();

        for method in &class_def.methods {
            let Some((kind, suffix)) = accessor_kind_and_suffix(&method.name) else {
                continue;
            };
            let overrides_parent = inherited.contains(method.name.as_str());
            let dummy = is_dummy_accessor(method, &kind, &suffix);
            by_suffix.entry(suffix.clone()).or_default().push(AccessorInfo {
                method,
                kind,
                suffix,
                dummy,
                overrides_parent,
            });
        }

        for group in by_suffix.values() {
            if group.iter().any(|info| !info.dummy) {
                continue;
            }
            for info in group {
                if info.overrides_parent {
                    continue;
                }
                self.emit(
                    LintName::DummyAccessor,
                    info.method.span,
                    format!(
                        "accessor '{}' only forwards backing field '{}' without behavior",
                        info.method.name, info.suffix
                    ),
                    Some(
                        "remove the wrapper and use field forwarding directly, or add the missing behavior"
                            .to_string(),
                    ),
                );
            }
        }
    }

    fn check_similar_parent_method_names<'a>(&mut self, class_def: &'a ClassDef, classes: &HashMap<&str, &'a ClassDef>) {
        let inherited = inherited_method_names(class_def, classes);
        if inherited.is_empty() {
            return;
        }

        for method in &class_def.methods {
            if inherited.contains(method.name.as_str()) || has_name_checked(method) {
                continue;
            }
            for parent_name in &inherited {
                if accessor_prefix_collision_is_expected(&method.name, parent_name) {
                    continue;
                }
                if is_likely_misspelling(&method.name, parent_name) {
                    self.emit(
                        LintName::SimilarParentMethodName,
                        method.span,
                        format!(
                            "method '{}' is similar to inherited method '{}' and may be a misspelled override",
                            method.name, parent_name
                        ),
                        Some("rename to the inherited method name or add @name_checked if this is intentional".to_string()),
                    );
                    break;
                }
            }
        }
    }
}

fn inherited_method_names<'a>(class_def: &'a ClassDef, classes: &HashMap<&str, &'a ClassDef>) -> HashSet<String> {
    let mut names = HashSet::new();
    let mut seen = HashSet::new();
    let mut current = class_def.parent.as_deref();

    while let Some(parent_name) = current {
        if !seen.insert(parent_name.to_string()) {
            break;
        }
        let Some(parent_class) = classes.get(parent_name).copied() else {
            break;
        };
        for method in &parent_class.methods {
            names.insert(method.name.clone());
        }
        current = parent_class.parent.as_deref();
    }

    names
}

fn accessor_kind_and_suffix(name: &str) -> Option<(AccessorKind, String)> {
    for (prefix, kind) in [
        ("get_", AccessorKind::Get),
        ("set_", AccessorKind::Set),
        ("is_", AccessorKind::Is),
    ] {
        if let Some(suffix) = name.strip_prefix(prefix) {
            if !suffix.is_empty() {
                return Some((kind, suffix.to_string()));
            }
        }
    }
    None
}

fn is_dummy_accessor(method: &FunctionDef, kind: &AccessorKind, suffix: &str) -> bool {
    match kind {
        AccessorKind::Get | AccessorKind::Is => block_is_self_field(&method.body, suffix),
        AccessorKind::Set => block_is_self_field_assignment(&method.body, suffix, method),
    }
}

fn block_is_self_field(block: &Block, field: &str) -> bool {
    match block.statements.as_slice() {
        [Node::Expression(expr)] => expr_is_self_field(expr, field),
        [Node::Return(ret)] => ret.value.as_ref().is_some_and(|expr| expr_is_self_field(expr, field)),
        _ => false,
    }
}

fn block_is_self_field_assignment(block: &Block, field: &str, method: &FunctionDef) -> bool {
    let value_param = method.params.iter().find(|param| param.name != "self").map(|param| param.name.as_str());
    let Some(value_param) = value_param else {
        return false;
    };

    match block.statements.as_slice() {
        [Node::Assignment(assign)] if assign.op == AssignOp::Assign => {
            expr_is_self_field(&assign.target, field)
                && matches!(&assign.value, Expr::Identifier(name) if name == value_param)
        }
        _ => false,
    }
}

fn expr_is_self_field(expr: &Expr, field: &str) -> bool {
    matches!(
        expr,
        Expr::FieldAccess { receiver, field: actual }
            if actual == field && matches!(receiver.as_ref(), Expr::Identifier(name) if name == "self")
    )
}

fn has_name_checked(method: &FunctionDef) -> bool {
    method.attributes.iter().any(attribute_is_name_checked) || method.decorators.iter().any(decorator_is_name_checked)
}

fn attribute_is_name_checked(attr: &Attribute) -> bool {
    attr.name == "name_checked"
}

fn decorator_is_name_checked(decorator: &Decorator) -> bool {
    matches!(&decorator.name, Expr::Identifier(name) if name == "name_checked")
}

fn accessor_prefix_collision_is_expected(a: &str, b: &str) -> bool {
    let Some((a_kind, a_suffix)) = accessor_kind_and_suffix(a) else {
        return false;
    };
    let Some((b_kind, b_suffix)) = accessor_kind_and_suffix(b) else {
        return false;
    };
    a_suffix == b_suffix && a_kind != b_kind
}

fn is_likely_misspelling(candidate: &str, inherited: &str) -> bool {
    if candidate == inherited {
        return false;
    }
    let max_len = candidate.chars().count().max(inherited.chars().count());
    if max_len < 4 {
        return false;
    }
    let threshold = if max_len >= 9 { 2 } else { 1 };
    bounded_damerau_levenshtein(candidate, inherited, threshold) <= threshold
}

fn bounded_damerau_levenshtein(a: &str, b: &str, limit: usize) -> usize {
    let a_chars: Vec<char> = a.chars().collect();
    let b_chars: Vec<char> = b.chars().collect();
    let a_len = a_chars.len();
    let b_len = b_chars.len();

    if a_len.abs_diff(b_len) > limit {
        return limit + 1;
    }

    let mut prev_prev = vec![usize::MAX / 4; b_len + 1];
    let mut prev: Vec<usize> = (0..=b_len).collect();
    let mut curr = vec![0; b_len + 1];

    for i in 1..=a_len {
        curr[0] = i;
        let mut row_min = curr[0];
        for j in 1..=b_len {
            let cost = usize::from(a_chars[i - 1] != b_chars[j - 1]);
            let mut best = (prev[j] + 1).min(curr[j - 1] + 1).min(prev[j - 1] + cost);
            if i > 1
                && j > 1
                && a_chars[i - 1] == b_chars[j - 2]
                && a_chars[i - 2] == b_chars[j - 1]
            {
                best = best.min(prev_prev[j - 2] + 1);
            }
            curr[j] = best;
            row_min = row_min.min(best);
        }
        if row_min > limit {
            return limit + 1;
        }
        std::mem::swap(&mut prev_prev, &mut prev);
        std::mem::swap(&mut prev, &mut curr);
    }

    prev[b_len]
}
