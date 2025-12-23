//! BDD testing state (thread-local for test isolation)

use std::cell::RefCell;
use std::collections::HashMap;
use crate::value::{Value, Env};
use simple_parser::ast::{Expr, ClassDef, FunctionDef, EnumDef};
use crate::interpreter::{Enums, ImplMethods, evaluate_expr};

// BDD testing state (thread-local for test isolation)
// Made pub(super) so other interpreter modules can access for context statement handling
thread_local! {
    // Current indentation level for nested describe/context blocks
    pub(crate) static BDD_INDENT: RefCell<usize> = RefCell::new(0);
    // (passed, failed) counts for current describe block
    pub(crate) static BDD_COUNTS: RefCell<(usize, usize)> = RefCell::new((0, 0));
    // Whether current "it" block has a failed expectation
    pub(super) static BDD_EXPECT_FAILED: RefCell<bool> = RefCell::new(false);
    // Whether we're currently inside an "it" block (expect should be silent)
    pub(super) static BDD_INSIDE_IT: RefCell<bool> = RefCell::new(false);
    // Failure message from expect (for display in it block)
    pub(super) static BDD_FAILURE_MSG: RefCell<Option<String>> = RefCell::new(None);

    // TEST-010: Shared examples registry - maps name to block
    pub(crate) static BDD_SHARED_EXAMPLES: RefCell<HashMap<String, Value>> = RefCell::new(HashMap::new());

    // Context definitions registry - maps symbol name to (givens, block)
    pub(crate) static BDD_CONTEXT_DEFS: RefCell<HashMap<String, Vec<Value>>> = RefCell::new(HashMap::new());

    // before_each hooks for current context (stack of hook lists for nesting)
    pub(crate) static BDD_BEFORE_EACH: RefCell<Vec<Vec<Value>>> = RefCell::new(vec![vec![]]);

    // after_each hooks for current context (stack of hook lists for nesting)
    pub(crate) static BDD_AFTER_EACH: RefCell<Vec<Vec<Value>>> = RefCell::new(vec![vec![]]);

    // TEST-012: Memoized lazy values (name -> (block, Option<cached_value>))
    pub(crate) static BDD_LAZY_VALUES: RefCell<HashMap<String, (Value, Option<Value>)>> = RefCell::new(HashMap::new());
}

/// Build a helpful failure message for expect by inspecting the expression
pub(super) fn build_expect_failure_message(
    expr: &Expr,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> String {
    use simple_parser::ast::BinOp;

    match expr {
        Expr::Binary { left, op, right } => {
            // Evaluate left and right sides to show actual values
            let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)
                .map(|v| format_value_for_message(&v))
                .unwrap_or_else(|_| "?".to_string());
            let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)
                .map(|v| format_value_for_message(&v))
                .unwrap_or_else(|_| "?".to_string());

            match op {
                BinOp::Eq => format!("expected {} to equal {}", left_val, right_val),
                BinOp::NotEq => format!("expected {} to not equal {}", left_val, right_val),
                BinOp::Lt => format!("expected {} < {}", left_val, right_val),
                BinOp::LtEq => format!("expected {} <= {}", left_val, right_val),
                BinOp::Gt => format!("expected {} > {}", left_val, right_val),
                BinOp::GtEq => format!("expected {} >= {}", left_val, right_val),
                _ => "expected expression to be true, got false".to_string(),
            }
        }
        Expr::Unary { op: simple_parser::ast::UnaryOp::Not, operand } => {
            let val = evaluate_expr(operand, env, functions, classes, enums, impl_methods)
                .map(|v| format_value_for_message(&v))
                .unwrap_or_else(|_| "?".to_string());
            format!("expected {} to be falsy", val)
        }
        Expr::Identifier(name) => {
            let val = env.get(name)
                .map(|v| format_value_for_message(v))
                .unwrap_or_else(|| "undefined".to_string());
            format!("expected {} ({}) to be truthy", name, val)
        }
        _ => "expected true, got false".to_string(),
    }
}

/// Format a value for display in error messages
pub(super) fn format_value_for_message(val: &Value) -> String {
    match val {
        Value::Int(n) => n.to_string(),
        Value::Float(f) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => format!("\"{}\"", s),
        Value::Nil => "nil".to_string(),
        Value::Array(items) => {
            let items_str: Vec<String> = items.iter().map(|v| format_value_for_message(v)).collect();
            format!("[{}]", items_str.join(", "))
        }
        _ => format!("{:?}", val),
    }
}
