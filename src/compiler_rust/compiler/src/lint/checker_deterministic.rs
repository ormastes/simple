//! Lint checker: @deterministic function body walker (GAME-DET-LINT-001).
//!
//! Flags direct calls to non-deterministic APIs inside functions (or methods)
//! annotated with @deterministic.  Only direct-call detection is implemented
//! here; transitive call-graph analysis is deferred (see bug doc).
//!
//! Note: Expr::Call carries no span of its own in this AST; diagnostics are
//! reported at the containing function's declaration span so the user can
//! find the function quickly.
//!
//! #![skip_todo]

use super::super::types::LintName;
use simple_parser::ast::{Block, Decorator, Expr, FunctionDef, Node};
use simple_parser::token::Span;

use super::LintChecker;

/// Non-deterministic function names that are blocked outright.
const NON_DET_FN_NAMES: &[&str] = &[
    "now",
    "rand",
    "random_u64",
    "random_f64",
    "rt_time_now_seconds",
    "print",
    "println",
];

/// Prefixes whose functions are considered non-deterministic (I/O, net, fs).
const NON_DET_PREFIXES: &[&str] = &["rt_fs_", "rt_net_", "rt_http_"];

impl LintChecker {
    /// Entry point: walk all top-level items and check @deterministic functions.
    pub(super) fn check_deterministic_calls(&mut self, items: &[Node]) {
        for item in items {
            self.check_node_for_det(item);
        }
    }

    fn check_node_for_det(&mut self, node: &Node) {
        match node {
            Node::Function(f) => {
                if is_deterministic_fn(f) {
                    self.check_block_for_non_det(&f.body, &f.name, f.span);
                }
            }
            Node::Class(c) => {
                for method in &c.methods {
                    if is_deterministic_fn(method) {
                        let scoped_name = format!("{}.{}", c.name, method.name);
                        self.check_block_for_non_det(&method.body, &scoped_name, method.span);
                    }
                }
            }
            Node::Struct(s) => {
                for method in &s.methods {
                    if is_deterministic_fn(method) {
                        let scoped_name = format!("{}.{}", s.name, method.name);
                        self.check_block_for_non_det(&method.body, &scoped_name, method.span);
                    }
                }
            }
            Node::Impl(imp) => {
                for method in &imp.methods {
                    if is_deterministic_fn(method) {
                        let type_name = format!("{:?}", imp.target_type);
                        let scoped_name = format!("{}.{}", type_name, method.name);
                        self.check_block_for_non_det(&method.body, &scoped_name, method.span);
                    }
                }
            }
            Node::ModDecl(md) => {
                if let Some(body) = &md.body {
                    for item in body {
                        self.check_node_for_det(item);
                    }
                }
            }
            _ => {}
        }
    }

    fn check_block_for_non_det(&mut self, block: &Block, fn_name: &str, fn_span: Span) {
        for node in &block.statements {
            self.check_stmt_for_non_det(node, fn_name, fn_span);
        }
    }

    fn check_stmt_for_non_det(&mut self, node: &Node, fn_name: &str, fn_span: Span) {
        match node {
            Node::Expression(expr) => {
                self.check_expr_for_non_det(expr, fn_name, fn_span);
            }
            Node::Let(s) => {
                if let Some(val) = &s.value {
                    self.check_expr_for_non_det(val, fn_name, fn_span);
                }
            }
            Node::Assignment(s) => {
                self.check_expr_for_non_det(&s.value, fn_name, fn_span);
            }
            Node::Return(s) => {
                if let Some(val) = &s.value {
                    self.check_expr_for_non_det(val, fn_name, fn_span);
                }
            }
            Node::If(s) => {
                self.check_expr_for_non_det(&s.condition, fn_name, fn_span);
                self.check_block_for_non_det(&s.then_block, fn_name, fn_span);
                for (_, _, elif_block) in &s.elif_branches {
                    self.check_block_for_non_det(elif_block, fn_name, fn_span);
                }
                if let Some(else_block) = &s.else_block {
                    self.check_block_for_non_det(else_block, fn_name, fn_span);
                }
            }
            Node::While(s) => {
                self.check_expr_for_non_det(&s.condition, fn_name, fn_span);
                self.check_block_for_non_det(&s.body, fn_name, fn_span);
            }
            Node::For(s) => {
                self.check_expr_for_non_det(&s.iterable, fn_name, fn_span);
                self.check_block_for_non_det(&s.body, fn_name, fn_span);
            }
            Node::Loop(s) => {
                self.check_block_for_non_det(&s.body, fn_name, fn_span);
            }
            _ => {}
        }
    }

    fn check_expr_for_non_det(&mut self, expr: &Expr, fn_name: &str, fn_span: Span) {
        match expr {
            Expr::Call { callee, args } => {
                if let Some(call_name) = extract_direct_call_name(callee) {
                    if is_non_det_name(&call_name) {
                        self.emit(
                            LintName::NonDetCallInDetFn,
                            fn_span,
                            format!(
                                "non-deterministic call '{}' inside @deterministic function '{}'",
                                call_name, fn_name
                            ),
                            Some(
                                "use the seeded det_guard equivalents from std.game2d.time, or move I/O outside the deterministic boundary"
                                    .to_string(),
                            ),
                        );
                    }
                }
                // Recurse into arguments and the callee itself (handles nested calls).
                for arg in args {
                    self.check_expr_for_non_det(&arg.value, fn_name, fn_span);
                }
                self.check_expr_for_non_det(callee, fn_name, fn_span);
            }
            Expr::MethodCall { receiver, args, .. } => {
                self.check_expr_for_non_det(receiver, fn_name, fn_span);
                for arg in args {
                    self.check_expr_for_non_det(&arg.value, fn_name, fn_span);
                }
            }
            Expr::BinaryOp { left, right, .. } => {
                self.check_expr_for_non_det(left, fn_name, fn_span);
                self.check_expr_for_non_det(right, fn_name, fn_span);
            }
            Expr::UnaryOp { operand, .. } => {
                self.check_expr_for_non_det(operand, fn_name, fn_span);
            }
            Expr::FieldAccess { receiver, .. } => {
                self.check_expr_for_non_det(receiver, fn_name, fn_span);
            }
            _ => {}
        }
    }
}

/// Returns true if the function has the @deterministic decorator or #[deterministic] attribute.
fn is_deterministic_fn(f: &FunctionDef) -> bool {
    has_deterministic_decorator(&f.decorators) || has_deterministic_attribute(f)
}

fn has_deterministic_decorator(decorators: &[Decorator]) -> bool {
    decorators
        .iter()
        .any(|d| matches!(&d.name, Expr::Identifier(name) if name == "deterministic"))
}

fn has_deterministic_attribute(f: &FunctionDef) -> bool {
    f.attributes.iter().any(|a| a.name == "deterministic")
}

/// Extract the bare function name from a direct call callee.
/// Returns None for field-access chains or other complex callees.
fn extract_direct_call_name(callee: &Expr) -> Option<String> {
    match callee {
        Expr::Identifier(name) => Some(name.clone()),
        _ => None,
    }
}

/// Check whether a function name is non-deterministic.
fn is_non_det_name(name: &str) -> bool {
    if NON_DET_FN_NAMES.contains(&name) {
        return true;
    }
    NON_DET_PREFIXES.iter().any(|prefix| name.starts_with(prefix))
}
