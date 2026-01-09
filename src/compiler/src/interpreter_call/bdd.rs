// BDD testing framework for interpreter
// describe, context, it, expect, shared_examples, hooks, etc.

use crate::error::CompileError;
use crate::interpreter::evaluate_expr;
use crate::value::*;
use simple_parser::ast::{Argument, BinOp, ClassDef, EnumDef, Expr, FunctionDef, UnaryOp};
use std::cell::RefCell;
use std::collections::HashMap;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// BDD testing state (thread-local for test isolation)
// Made pub(crate) so interpreter_control.rs can access for context statement handling
thread_local! {
    // Current indentation level for nested describe/context blocks
    pub(crate) static BDD_INDENT: RefCell<usize> = RefCell::new(0);
    // (passed, failed) counts for current describe block
    pub(crate) static BDD_COUNTS: RefCell<(usize, usize)> = RefCell::new((0, 0));
    // Whether current "it" block has a failed expectation
    static BDD_EXPECT_FAILED: RefCell<bool> = RefCell::new(false);
    // Whether we're currently inside an "it" block (expect should be silent)
    static BDD_INSIDE_IT: RefCell<bool> = RefCell::new(false);
    // Failure message from expect (for display in it block)
    static BDD_FAILURE_MSG: RefCell<Option<String>> = RefCell::new(None);

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
fn build_expect_failure_message(
    expr: &Expr,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> String {
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
        Expr::Unary {
            op: UnaryOp::Not,
            operand,
        } => {
            let val = evaluate_expr(operand, env, functions, classes, enums, impl_methods)
                .map(|v| format_value_for_message(&v))
                .unwrap_or_else(|_| "?".to_string());
            format!("expected {} to be falsy", val)
        }
        Expr::Identifier(name) => {
            let val = env
                .get(name)
                .map(|v| format_value_for_message(v))
                .unwrap_or_else(|| "undefined".to_string());
            format!("expected {} ({}) to be truthy", name, val)
        }
        _ => "expected true, got false".to_string(),
    }
}

/// Format a value for display in error messages
fn format_value_for_message(val: &Value) -> String {
    match val {
        Value::Int(n) => n.to_string(),
        Value::Float(f) => f.to_string(),
        Value::Bool(b) => b.to_string(),
        Value::Str(s) => format!("\"{}\"", s),
        Value::Nil => "nil".to_string(),
        Value::Array(items) => {
            let items_str: Vec<String> =
                items.iter().map(|v| format_value_for_message(v)).collect();
            format!("[{}]", items_str.join(", "))
        }
        _ => format!("{:?}", val),
    }
}

/// Execute a block value (lambda or block closure)
pub(crate) fn exec_block_value(
    block: Value,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::block_execution::exec_block_closure;
    use super::core::exec_lambda;

    match block {
        Value::Lambda {
            params,
            body,
            env: captured,
        } => exec_lambda(
            &params,
            &body,
            &[],
            env,
            &captured,
            functions,
            classes,
            enums,
            impl_methods,
        ),
        Value::BlockClosure {
            nodes,
            env: captured,
        } => exec_block_closure(&nodes, &captured, functions, classes, enums, impl_methods),
        _ => Ok(Value::Nil),
    }
}

fn eval_arg(
    args: &[Argument],
    index: usize,
    default: Value,
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Some(arg) = args.get(index) {
        evaluate_expr(&arg.value, env, functions, classes, enums, impl_methods)
    } else {
        Ok(default)
    }
}

pub(super) fn eval_bdd_builtin(
    name: &str,
    args: &[Argument],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Option<Value>, CompileError> {
    match name {
        "describe" | "context" => {
            let first_arg = eval_arg(
                args,
                0,
                Value::Str("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            let (name_str, ctx_def_blocks) = match &first_arg {
                Value::Symbol(ctx_name) => {
                    let blocks = BDD_CONTEXT_DEFS.with(|cell| cell.borrow().get(ctx_name).cloned());
                    (format!("with {}", ctx_name), blocks)
                }
                Value::Str(s) => (s.clone(), None),
                _ => ("unnamed".to_string(), None),
            };

            let block = eval_arg(
                args,
                1,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            let indent = BDD_INDENT.with(|cell| *cell.borrow());
            let indent_str = "  ".repeat(indent);

            println!("{}{}", indent_str, name_str);

            BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);

            if let Some(ctx_blocks) = ctx_def_blocks {
                for ctx_block in ctx_blocks {
                    exec_block_value(ctx_block, env, functions, classes, enums, impl_methods)?;
                }
            }

            let result = exec_block_value(block, env, functions, classes, enums, impl_methods);

            BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);

            if indent == 0 {
                BDD_LAZY_VALUES.with(|cell| cell.borrow_mut().clear());
                let (passed, failed) = BDD_COUNTS.with(|cell| {
                    let counts = cell.borrow();
                    (counts.0, counts.1)
                });
                let total = passed + failed;
                println!();
                if failed == 0 {
                    println!(
                        "\x1b[32m{} example{}, 0 failures\x1b[0m",
                        total,
                        if total == 1 { "" } else { "s" }
                    );
                } else {
                    println!(
                        "\x1b[31m{} example{}, {} failure{}\x1b[0m",
                        total,
                        if total == 1 { "" } else { "s" },
                        failed,
                        if failed == 1 { "" } else { "s" }
                    );
                }
                BDD_COUNTS.with(|cell| *cell.borrow_mut() = (0, 0));
            }

            Ok(Some(result?))
        }
        "it" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Str(s) => s.clone(),
                _ => "unnamed".to_string(),
            };
            let block = eval_arg(
                args,
                1,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = false);
            BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = None);
            BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = true);

            BDD_LAZY_VALUES.with(|cell| {
                for (_, (_, cached)) in cell.borrow_mut().iter_mut() {
                    *cached = None;
                }
            });

            let before_hooks: Vec<Value> = BDD_BEFORE_EACH.with(|cell| {
                cell.borrow()
                    .iter()
                    .flat_map(|level| level.clone())
                    .collect()
            });
            for hook in before_hooks {
                exec_block_value(hook, env, functions, classes, enums, impl_methods)?;
            }

            let result = exec_block_value(block, env, functions, classes, enums, impl_methods);

            let after_hooks: Vec<Value> = BDD_AFTER_EACH.with(|cell| {
                cell.borrow()
                    .iter()
                    .rev()
                    .flat_map(|level| level.clone())
                    .collect()
            });
            for hook in after_hooks {
                let _ = exec_block_value(hook, env, functions, classes, enums, impl_methods);
            }

            BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = false);

            let failed = BDD_EXPECT_FAILED.with(|cell| *cell.borrow());
            let failure_msg = BDD_FAILURE_MSG.with(|cell| cell.borrow().clone());
            let indent = BDD_INDENT.with(|cell| *cell.borrow());
            let indent_str = "  ".repeat(indent);

            if failed {
                println!("{}\x1b[31m✗ {}\x1b[0m", indent_str, name_str);
                if let Some(msg) = failure_msg {
                    println!("{}  \x1b[31m{}\x1b[0m", indent_str, msg);
                }
                BDD_COUNTS.with(|cell| cell.borrow_mut().1 += 1);
            } else {
                println!("{}\x1b[32m✓ {}\x1b[0m", indent_str, name_str);
                BDD_COUNTS.with(|cell| cell.borrow_mut().0 += 1);
            }

            Ok(Some(result?))
        }
        "skip" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Str(s) => s.clone(),
                _ => "unnamed".to_string(),
            };

            let indent = BDD_INDENT.with(|cell| *cell.borrow());
            let indent_str = "  ".repeat(indent);

            println!("{}\x1b[33m○ {} (skipped)\x1b[0m", indent_str, name_str);

            BDD_COUNTS.with(|cell| cell.borrow_mut().0 += 1);

            Ok(Some(Value::Nil))
        }
        "expect" => {
            let condition = eval_arg(
                args,
                0,
                Value::Bool(false),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let passed = condition.truthy();

            let inside_it = BDD_INSIDE_IT.with(|cell| *cell.borrow());

            if !passed {
                BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = true);

                let failure_msg = if !args.is_empty() {
                    build_expect_failure_message(
                        &args[0].value,
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )
                } else {
                    "expected true, got false".to_string()
                };

                if !inside_it {
                    let indent = BDD_INDENT.with(|cell| *cell.borrow());
                    if indent > 0 {
                        let indent_str = "  ".repeat(indent);
                        println!("{}\x1b[31m✗ expectation failed\x1b[0m", indent_str);
                        println!("{}  \x1b[31m{}\x1b[0m", indent_str, failure_msg);
                        BDD_COUNTS.with(|cell| cell.borrow_mut().1 += 1);
                    }
                } else {
                    BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = Some(failure_msg));
                }
            } else if !inside_it {
                let indent = BDD_INDENT.with(|cell| *cell.borrow());
                if indent > 0 {
                    let indent_str = "  ".repeat(indent);
                    println!("{}\x1b[32m✓ expectation passed\x1b[0m", indent_str);
                    BDD_COUNTS.with(|cell| cell.borrow_mut().0 += 1);
                }
            }

            Ok(Some(Value::Bool(passed)))
        }
        "shared_examples" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Str(s) => s.clone(),
                Value::Symbol(s) => s.clone(),
                _ => "unnamed".to_string(),
            };
            let block = eval_arg(
                args,
                1,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            BDD_SHARED_EXAMPLES.with(|cell| {
                cell.borrow_mut().insert(name_str.clone(), block);
            });

            Ok(Some(Value::Nil))
        }
        "it_behaves_like" | "include_examples" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Str(s) => s.clone(),
                Value::Symbol(s) => s.clone(),
                _ => "unnamed".to_string(),
            };

            let block = BDD_SHARED_EXAMPLES.with(|cell| cell.borrow().get(&name_str).cloned());

            match block {
                Some(block) => {
                    let indent = BDD_INDENT.with(|cell| *cell.borrow());
                    let indent_str = "  ".repeat(indent);
                    println!("{}behaves like {}", indent_str, name_str);

                    BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);
                    let result =
                        exec_block_value(block, env, functions, classes, enums, impl_methods);
                    BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);

                    Ok(Some(result?))
                }
                None => {
                    bail_semantic!("Shared example '{}' not found", name_str);
                }
            }
        }
        "before_each" => {
            let block = eval_arg(
                args,
                0,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            BDD_BEFORE_EACH.with(|cell| {
                let mut hooks = cell.borrow_mut();
                if let Some(current) = hooks.last_mut() {
                    current.push(block);
                }
            });

            Ok(Some(Value::Nil))
        }
        "after_each" => {
            let block = eval_arg(
                args,
                0,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            BDD_AFTER_EACH.with(|cell| {
                let mut hooks = cell.borrow_mut();
                if let Some(current) = hooks.last_mut() {
                    current.push(block);
                }
            });

            Ok(Some(Value::Nil))
        }
        "context_def" => {
            let name = eval_arg(
                args,
                0,
                Value::Symbol("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Symbol(s) => s.clone(),
                Value::Str(s) => s.clone(),
                _ => "unnamed".to_string(),
            };
            let block = eval_arg(
                args,
                1,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            BDD_CONTEXT_DEFS.with(|cell| {
                cell.borrow_mut().insert(name_str, vec![block]);
            });

            Ok(Some(Value::Nil))
        }
        "given_lazy" => {
            let name = eval_arg(
                args,
                0,
                Value::Symbol("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Symbol(s) => s.clone(),
                Value::Str(s) => s.clone(),
                _ => "unnamed".to_string(),
            };
            let block = eval_arg(
                args,
                1,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            BDD_LAZY_VALUES.with(|cell| {
                cell.borrow_mut().insert(name_str, (block, None));
            });

            Ok(Some(Value::Nil))
        }
        "given" => {
            let first_arg = eval_arg(
                args,
                0,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            match &first_arg {
                Value::Symbol(ctx_name) => {
                    let ctx_block =
                        BDD_CONTEXT_DEFS.with(|cell| cell.borrow().get(ctx_name).cloned());
                    if let Some(blocks) = ctx_block {
                        for block in blocks {
                            exec_block_value(block, env, functions, classes, enums, impl_methods)?;
                        }
                    }
                }
                _ => {
                    if args.len() >= 2 {
                        let block = eval_arg(
                            args,
                            1,
                            Value::Nil,
                            env,
                            functions,
                            classes,
                            enums,
                            impl_methods,
                        )?;
                        exec_block_value(block, env, functions, classes, enums, impl_methods)?;
                    } else {
                        exec_block_value(first_arg, env, functions, classes, enums, impl_methods)?;
                    }
                }
            }

            Ok(Some(Value::Nil))
        }
        "let_lazy" => {
            let name = eval_arg(
                args,
                0,
                Value::Symbol("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Symbol(s) => s.clone(),
                Value::Str(s) => s.clone(),
                _ => "unnamed".to_string(),
            };
            let block = eval_arg(
                args,
                1,
                Value::Nil,
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;

            BDD_LAZY_VALUES.with(|cell| {
                cell.borrow_mut().insert(name_str, (block, None));
            });

            Ok(Some(Value::Nil))
        }
        "get_let" => {
            let name = eval_arg(
                args,
                0,
                Value::Symbol("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Symbol(s) => s.clone(),
                Value::Str(s) => s.clone(),
                _ => "unnamed".to_string(),
            };

            let cached = BDD_LAZY_VALUES.with(|cell| cell.borrow().get(&name_str).cloned());

            match cached {
                Some((_block, Some(value))) => Ok(Some(value)),
                Some((block, None)) => {
                    let value = exec_block_value(
                        block.clone(),
                        env,
                        functions,
                        classes,
                        enums,
                        impl_methods,
                    )?;
                    BDD_LAZY_VALUES.with(|cell| {
                        if let Some(entry) = cell.borrow_mut().get_mut(&name_str) {
                            entry.1 = Some(value.clone());
                        }
                    });
                    Ok(Some(value))
                }
                None => {
                    bail_semantic!("No lazy value found for '{}'", name_str);
                }
            }
        }
        "has_let" => {
            let name = eval_arg(
                args,
                0,
                Value::Symbol("unnamed".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match &name {
                Value::Symbol(s) => s.clone(),
                Value::Str(s) => s.clone(),
                _ => "unnamed".to_string(),
            };

            let exists = BDD_LAZY_VALUES.with(|cell| cell.borrow().contains_key(&name_str));

            Ok(Some(Value::Bool(exists)))
        }
        _ => Ok(None),
    }
}
