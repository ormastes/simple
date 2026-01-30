// BDD testing framework for interpreter
// describe, context, it, expect, shared_examples, hooks, etc.

use crate::error::{codes, CompileError, ErrorContext};
use crate::interpreter::evaluate_expr;
use crate::interpreter::{BDD_REGISTRY_CONTEXTS, BDD_REGISTRY_GROUPS, BDD_REGISTRY_SHARED};
use crate::value::*;
use simple_parser::ast::{Argument, BinOp, ClassDef, EnumDef, Expr, FunctionDef, UnaryOp};
use std::cell::RefCell;
use std::collections::HashMap;
use std::sync::Arc;

type Enums = HashMap<String, EnumDef>;
type ImplMethods = HashMap<String, Vec<FunctionDef>>;

// Type aliases for BDD registry types
type BddGroupsCell = RefCell<Vec<Value>>;
type BddContextsCell = RefCell<HashMap<String, Value>>;
type BddSharedCell = RefCell<HashMap<String, Value>>;

// BDD testing state (thread-local for test isolation)
// Made pub(crate) so interpreter_control.rs can access for context statement handling
thread_local! {
    // Current indentation level for nested describe/context blocks
    pub(crate) static BDD_INDENT: RefCell<usize> = RefCell::new(0);
    // (passed, failed) counts for current describe block
    pub(crate) static BDD_COUNTS: RefCell<(usize, usize)> = RefCell::new((0, 0));
    // Whether current "it" block has a failed expectation
    pub(crate) static BDD_EXPECT_FAILED: RefCell<bool> = RefCell::new(false);
    // Whether we're currently inside an "it" block (expect should be silent)
    pub(crate) static BDD_INSIDE_IT: RefCell<bool> = RefCell::new(false);
    // Failure message from expect (for display in it block)
    pub(crate) static BDD_FAILURE_MSG: RefCell<Option<String>> = RefCell::new(None);

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

    // Resource fixtures: name -> (factory_block, Option<created_resource>)
    // Resources are lazily created and automatically cleaned up after each test
    pub(crate) static BDD_RESOURCE_VALUES: RefCell<HashMap<String, (Value, Option<Value>)>> = RefCell::new(HashMap::new());

    // Stack of current ExampleGroup objects for nested describe/context
    pub(crate) static BDD_GROUP_STACK: RefCell<Vec<Value>> = RefCell::new(Vec::new());

    // Hook caches: indexed by stack depth to avoid O(n²) recomputation
    // Maps stack_depth -> flattened hooks for that depth
    static BDD_BEFORE_EACH_CACHE: RefCell<HashMap<usize, Vec<Value>>> = RefCell::new(HashMap::new());
    static BDD_AFTER_EACH_CACHE: RefCell<HashMap<usize, Vec<Value>>> = RefCell::new(HashMap::new());
}

/// Create an ExampleGroup Value object
fn create_example_group(description: String, parent: Option<Value>) -> Value {
    let mut fields = HashMap::new();
    fields.insert("description".to_string(), Value::Str(description));
    fields.insert(
        "parent".to_string(),
        match parent {
            Some(p) => Value::Enum {
                enum_name: "Option".to_string(),
                variant: "Some".to_string(),
                payload: Some(Box::new(p)),
            },
            None => Value::Enum {
                enum_name: "Option".to_string(),
                variant: "None".to_string(),
                payload: None,
            },
        },
    );
    fields.insert("children".to_string(), Value::Array(Vec::new()));
    fields.insert("test_examples".to_string(), Value::Array(Vec::new()));
    fields.insert("hooks".to_string(), Value::Array(Vec::new()));

    Value::Object {
        class: "ExampleGroup".to_string(),
        fields: Arc::new(fields),
    }
}

/// Create an Example Value object
fn create_example(description: String, block: Value) -> Value {
    let mut fields = HashMap::new();
    fields.insert("description".to_string(), Value::Str(description));
    fields.insert("block".to_string(), block);
    fields.insert("is_skipped".to_string(), Value::Bool(false));
    fields.insert("tags".to_string(), Value::Array(Vec::new()));
    fields.insert(
        "timeout_seconds".to_string(),
        Value::Enum {
            enum_name: "Option".to_string(),
            variant: "None".to_string(),
            payload: None,
        },
    );
    fields.insert(
        "resource_limits".to_string(),
        Value::Enum {
            enum_name: "Option".to_string(),
            variant: "None".to_string(),
            payload: None,
        },
    );

    Value::Object {
        class: "Example".to_string(),
        fields: Arc::new(fields),
    }
}

/// Add an example to the current group
fn add_example_to_current_group(example: Value) {
    BDD_GROUP_STACK.with(|cell| {
        let mut stack = cell.borrow_mut();
        if let Some(group) = stack.last_mut() {
            if let Value::Object { fields, .. } = group {
                if let Some(Value::Array(examples)) = Arc::make_mut(fields).get_mut("test_examples") {
                    examples.push(example);
                }
            }
        }
    });
}

/// Add a child group to the current group
fn add_child_to_current_group(child: &Value) {
    BDD_GROUP_STACK.with(|cell| {
        let mut stack = cell.borrow_mut();
        if let Some(group) = stack.last_mut() {
            if let Value::Object { fields, .. } = group {
                if let Some(Value::Array(children)) = Arc::make_mut(fields).get_mut("children") {
                    children.push(child.clone());
                }
            }
        }
    });
}

/// Add a hook to the current group
fn add_hook_to_current_group(hook: Value) {
    BDD_GROUP_STACK.with(|cell| {
        let mut stack = cell.borrow_mut();
        if let Some(group) = stack.last_mut() {
            if let Value::Object { fields, .. } = group {
                if let Some(Value::Array(hooks)) = Arc::make_mut(fields).get_mut("hooks") {
                    hooks.push(hook);
                }
            }
        }
    });
}

/// Update the last child in the current group's children array with a fully-built version
fn update_last_child_in_current_group(updated_child: &Value) {
    BDD_GROUP_STACK.with(|cell| {
        let mut stack = cell.borrow_mut();
        if let Some(group) = stack.last_mut() {
            if let Value::Object { fields, .. } = group {
                if let Some(Value::Array(children)) = Arc::make_mut(fields).get_mut("children") {
                    if !children.is_empty() {
                        let last_idx = children.len() - 1;
                        children[last_idx] = updated_child.clone();
                    }
                }
            }
        }
    });
}

/// Invalidate hook caches (called when hooks are added or when entering/exiting contexts)
fn invalidate_hook_caches() {
    BDD_BEFORE_EACH_CACHE.with(|cell| cell.borrow_mut().clear());
    BDD_AFTER_EACH_CACHE.with(|cell| cell.borrow_mut().clear());
}

/// Get before_each hooks with caching (O(1) after first call per nesting level)
fn get_before_each_hooks_cached() -> Vec<Value> {
    BDD_BEFORE_EACH.with(|hooks_cell| {
        let hooks_stack = hooks_cell.borrow();
        let depth = hooks_stack.len();

        BDD_BEFORE_EACH_CACHE.with(|cache_cell| {
            let mut cache = cache_cell.borrow_mut();

            // Check cache first
            if let Some(cached) = cache.get(&depth) {
                return cached.clone();
            }

            // Not cached - compute and store
            let flattened: Vec<Value> = hooks_stack
                .iter()
                .flat_map(|level| level.clone())
                .collect();

            cache.insert(depth, flattened.clone());
            flattened
        })
    })
}

/// Get after_each hooks with caching (O(1) after first call per nesting level)
fn get_after_each_hooks_cached() -> Vec<Value> {
    BDD_AFTER_EACH.with(|hooks_cell| {
        let hooks_stack = hooks_cell.borrow();
        let depth = hooks_stack.len();

        BDD_AFTER_EACH_CACHE.with(|cache_cell| {
            let mut cache = cache_cell.borrow_mut();

            // Check cache first
            if let Some(cached) = cache.get(&depth) {
                return cached.clone();
            }

            // Not cached - compute and store (reverse for after hooks)
            let flattened: Vec<Value> = hooks_stack
                .iter()
                .rev()
                .flat_map(|level| level.clone())
                .collect();

            cache.insert(depth, flattened.clone());
            flattened
        })
    })
}

/// Build a helpful failure message for expect by inspecting the expression
fn build_expect_failure_message(
    expr: &Expr,
    env: &mut Env,
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
            let items_str: Vec<String> = items.iter().map(|v| format_value_for_message(v)).collect();
            format!("[{}]", items_str.join(", "))
        }
        _ => format!("{:?}", val),
    }
}

/// Execute a block value (lambda or block closure)
pub(crate) fn exec_block_value(
    block: Value,
    env: &mut Env,
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
        } => {
            let mut captured_clone = captured.clone();
            exec_lambda(
                &params,
                &body,
                &[],
                env,
                &mut captured_clone,
                functions,
                classes,
                enums,
                impl_methods,
            )
        }
        Value::BlockClosure { nodes, env: captured } => {
            let mut captured_clone = captured.clone();
            exec_block_closure(&nodes, &mut captured_clone, functions, classes, enums, impl_methods)
        }
        _ => Ok(Value::Nil),
    }
}

fn eval_arg(
    args: &[Argument],
    index: usize,
    default: Value,
    env: &mut Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    use super::super::handle_method_call_with_self_update;

    if let Some(arg) = args.get(index) {
        // Handle method calls with self-update (e.g., m.call("method", []))
        // This ensures mutations from 'me' methods are persisted back to the environment
        let (value, update) =
            handle_method_call_with_self_update(&arg.value, env, functions, classes, enums, impl_methods)?;
        if let Some((obj_name, new_self)) = update {
            env.insert(obj_name, new_self);
        }
        Ok(value)
    } else {
        Ok(default)
    }
}

pub(super) fn eval_bdd_builtin(
    name: &str,
    args: &[Argument],
    env: &mut Env,
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

            let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

            let indent = BDD_INDENT.with(|cell| *cell.borrow());
            let indent_str = "  ".repeat(indent);

            println!("{}{}", indent_str, name_str);

            // Create ExampleGroup object
            // - `describe` always creates a top-level group (no parent)
            // - `context` creates a child of the current group (if there is one)
            let is_describe = name == "describe";
            let parent = if is_describe {
                None // describe always creates top-level group
            } else {
                BDD_GROUP_STACK.with(|cell| cell.borrow().last().cloned())
            };
            let group = create_example_group(name_str.clone(), parent.clone());

            // If context with a parent, add this as a child
            if !is_describe && parent.is_some() {
                add_child_to_current_group(&group);
            }

            // Push group onto stack
            BDD_GROUP_STACK.with(|cell| cell.borrow_mut().push(group));

            BDD_INDENT.with(|cell| *cell.borrow_mut() += 1);
            BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().push(vec![]));
            BDD_AFTER_EACH.with(|cell| cell.borrow_mut().push(vec![]));
            // Invalidate hook cache when entering new context
            invalidate_hook_caches();

            if let Some(ctx_blocks) = ctx_def_blocks {
                for ctx_block in ctx_blocks {
                    exec_block_value(ctx_block, env, functions, classes, enums, impl_methods)?;
                }
            }

            let result = exec_block_value(block, env, functions, classes, enums, impl_methods);

            BDD_BEFORE_EACH.with(|cell| cell.borrow_mut().pop());
            BDD_AFTER_EACH.with(|cell| cell.borrow_mut().pop());
            // Invalidate hook cache when exiting context
            invalidate_hook_caches();
            BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);

            // Pop finished group from stack
            let finished_group = BDD_GROUP_STACK.with(|cell| cell.borrow_mut().pop());

            // If this was a context with a parent, update the parent's child reference
            // with the fully-built child (including its own children)
            if !is_describe && parent.is_some() {
                if let Some(child) = &finished_group {
                    update_last_child_in_current_group(child);
                }
            }

            // Register group to the registry if it's a describe block
            if is_describe {
                if let Some(group) = finished_group {
                    BDD_REGISTRY_GROUPS.with(|cell: &BddGroupsCell| {
                        cell.borrow_mut().push(group);
                    });
                }
            }

            if indent == 0 {
                BDD_LAZY_VALUES.with(|cell| cell.borrow_mut().clear());

                // Skip summary in list mode
                let test_mode = std::env::var("SIMPLE_TEST_MODE").unwrap_or_default();
                let list_mode = test_mode == "list";

                if !list_mode {
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
            let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

            // Create and register Example object with current group
            let example = create_example(name_str.clone(), block.clone());
            add_example_to_current_group(example);

            BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = false);
            BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = None);
            BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = true);

            BDD_LAZY_VALUES.with(|cell| {
                for (_, (_, cached)) in cell.borrow_mut().iter_mut() {
                    *cached = None;
                }
            });

            // Check for list mode - skip test execution if SIMPLE_TEST_MODE=list
            let test_mode = std::env::var("SIMPLE_TEST_MODE").unwrap_or_default();
            let list_mode = test_mode == "list";

            if list_mode {
                // List mode - just print test name and skip execution
                let indent = BDD_INDENT.with(|cell| *cell.borrow());
                let indent_str = "  ".repeat(indent);
                println!("{}{}", indent_str, name_str);
                BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = false);
                return Ok(Some(Value::Nil));
            }

            // Create a fresh environment for this test to prevent memory accumulation.
            // Each test gets its own copy of the environment that is discarded after the test.
            // This prevents values created during one test from persisting into subsequent tests.
            let mut test_env = env.clone();

            // Use cached hooks to avoid O(n²) performance with deeply nested contexts
            let before_hooks = get_before_each_hooks_cached();
            for hook in before_hooks {
                exec_block_value(hook, &mut test_env, functions, classes, enums, impl_methods)?;
            }

            let result = exec_block_value(block, &mut test_env, functions, classes, enums, impl_methods);

            // Use cached hooks to avoid O(n²) performance with deeply nested contexts
            let after_hooks = get_after_each_hooks_cached();
            for hook in after_hooks {
                let _ = exec_block_value(hook, &mut test_env, functions, classes, enums, impl_methods);
            }
            // test_env is dropped here, freeing memory used by this test

            BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = false);

            let indent = BDD_INDENT.with(|cell| *cell.borrow());
            let indent_str = "  ".repeat(indent);

            // Check if block execution had an error first
            match result {
                Err(ref e) => {
                    // Test failed due to execution error
                    println!("{}\x1b[31m✗ {}\x1b[0m", indent_str, name_str);
                    println!("{}  \x1b[31m{}\x1b[0m", indent_str, e);
                    BDD_COUNTS.with(|cell| cell.borrow_mut().1 += 1);
                    // Don't propagate the error - allow other tests to run
                    Ok(Some(Value::Nil))
                }
                Ok(_) => {
                    // Check if expect failed
                    let failed = BDD_EXPECT_FAILED.with(|cell| *cell.borrow());
                    let failure_msg = BDD_FAILURE_MSG.with(|cell| cell.borrow().clone());

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

                    // Clear lazy values after each test to reduce memory accumulation.
                    // This forces lazy values to be re-evaluated for each test, which is
                    // the expected behavior (fresh values per test).
                    BDD_LAZY_VALUES.with(|cell| cell.borrow_mut().clear());

                    Ok(Some(result?))
                }
            }
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
            // Return the value as-is so .to(matcher) can match against it
            // The .to() method in interpreter_method/mod.rs handles the assertion result
            let value = eval_arg(
                args,
                0,
                Value::Bool(false),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            // Return the value for .to(matcher) to match against
            Ok(Some(value))
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
            let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

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
                    let result = exec_block_value(block, env, functions, classes, enums, impl_methods);
                    BDD_INDENT.with(|cell| *cell.borrow_mut() -= 1);

                    Ok(Some(result?))
                }
                None => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("define the shared example with shared_examples() before using it_behaves_like()");
                    return Err(CompileError::semantic_with_context(
                        format!("shared example '{}' not found", name_str),
                        ctx,
                    ));
                }
            }
        }
        "before_each" => {
            let block = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;

            BDD_BEFORE_EACH.with(|cell| {
                let mut hooks = cell.borrow_mut();
                if let Some(current) = hooks.last_mut() {
                    current.push(block);
                }
            });
            // Invalidate hook cache when new hook is added
            invalidate_hook_caches();

            Ok(Some(Value::Nil))
        }
        "after_each" => {
            let block = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;

            BDD_AFTER_EACH.with(|cell| {
                let mut hooks = cell.borrow_mut();
                if let Some(current) = hooks.last_mut() {
                    current.push(block);
                }
            });
            // Invalidate hook cache when new hook is added
            invalidate_hook_caches();

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
            let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

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
            let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

            BDD_LAZY_VALUES.with(|cell| {
                cell.borrow_mut().insert(name_str, (block, None));
            });

            Ok(Some(Value::Nil))
        }
        "given" => {
            let first_arg = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;

            match &first_arg {
                Value::Symbol(ctx_name) => {
                    let ctx_block = BDD_CONTEXT_DEFS.with(|cell| cell.borrow().get(ctx_name).cloned());
                    if let Some(blocks) = ctx_block {
                        for block in blocks {
                            exec_block_value(block, env, functions, classes, enums, impl_methods)?;
                        }
                    }
                }
                _ => {
                    if args.len() >= 2 {
                        let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
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
            let block = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

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
                    let value = exec_block_value(block.clone(), env, functions, classes, enums, impl_methods)?;
                    BDD_LAZY_VALUES.with(|cell| {
                        if let Some(entry) = cell.borrow_mut().get_mut(&name_str) {
                            entry.1 = Some(value.clone());
                        }
                    });
                    Ok(Some(value))
                }
                None => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("define the lazy value with let_lazy() or given_lazy() before using get_let()");
                    return Err(CompileError::semantic_with_context(
                        format!("no lazy value found for '{}'", name_str),
                        ctx,
                    ));
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
        // Resource fixtures with automatic cleanup
        "resource" => {
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
            let factory = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;

            // Register the factory block (resource not created yet)
            BDD_RESOURCE_VALUES.with(|cell| {
                cell.borrow_mut().insert(name_str, (factory, None));
            });

            Ok(Some(Value::Nil))
        }
        "get_resource" => {
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

            let cached = BDD_RESOURCE_VALUES.with(|cell| cell.borrow().get(&name_str).cloned());

            match cached {
                Some((_factory, Some(value))) => Ok(Some(value)),
                Some((factory, None)) => {
                    // Create the resource by calling the factory
                    let value = exec_block_value(factory.clone(), env, functions, classes, enums, impl_methods)?;
                    BDD_RESOURCE_VALUES.with(|cell| {
                        if let Some(entry) = cell.borrow_mut().get_mut(&name_str) {
                            entry.1 = Some(value.clone());
                        }
                    });
                    Ok(Some(value))
                }
                None => {
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNDEFINED_VARIABLE)
                        .with_help("define the resource with resource() before using get_resource()");
                    return Err(CompileError::semantic_with_context(
                        format!("no resource found for '{}'", name_str),
                        ctx,
                    ));
                }
            }
        }
        "has_resource" => {
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

            let exists = BDD_RESOURCE_VALUES.with(|cell| {
                cell.borrow()
                    .get(&name_str)
                    .map(|(_, cached)| cached.is_some())
                    .unwrap_or(false)
            });

            Ok(Some(Value::Bool(exists)))
        }
        "cleanup_resource" => {
            // Cleanup a specific resource by name (calls close() if available)
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

            // Get and remove the resource
            let resource = BDD_RESOURCE_VALUES.with(|cell| {
                let mut resources = cell.borrow_mut();
                if let Some((factory, cached)) = resources.get_mut(&name_str) {
                    let value = cached.take();
                    value
                } else {
                    None
                }
            });

            // Try to call close() on the resource if it was created
            if let Some(resource_value) = resource {
                // Try to call close() method using the interpreter's method dispatch
                // This is a best-effort cleanup - if close() doesn't exist, we just drop the value
                if let Value::Object { class, fields } = &resource_value {
                    if let Some(class_def) = classes.get(class).cloned() {
                        if let Some(method) = class_def.methods.iter().find(|m| m.name == "close") {
                            // Call close() method
                            let mut local_env = env.clone();
                            local_env.insert("self".to_string(), resource_value.clone());
                            for (k, v) in fields.iter() {
                                local_env.insert(k.clone(), v.clone());
                            }
                            let _ = crate::interpreter::exec_block(
                                &method.body,
                                &mut local_env,
                                functions,
                                classes,
                                enums,
                                impl_methods,
                            );
                        }
                    }
                }
            }

            Ok(Some(Value::Nil))
        }
        "cleanup_all_resources" => {
            // Cleanup all resources (called at end of test)
            let resources: Vec<(String, Option<Value>)> = BDD_RESOURCE_VALUES
                .with(|cell| cell.borrow().iter().map(|(k, (_, v))| (k.clone(), v.clone())).collect());

            // Clean up in reverse order (LIFO)
            for (name, cached) in resources.into_iter().rev() {
                if let Some(resource_value) = cached {
                    if let Value::Object { class, fields } = &resource_value {
                        if let Some(class_def) = classes.get(class).cloned() {
                            if let Some(method) = class_def.methods.iter().find(|m| m.name == "close") {
                                let mut local_env = env.clone();
                                local_env.insert("self".to_string(), resource_value.clone());
                                for (k, v) in fields.iter() {
                                    local_env.insert(k.clone(), v.clone());
                                }
                                let _ = crate::interpreter::exec_block(
                                    &method.body,
                                    &mut local_env,
                                    functions,
                                    classes,
                                    enums,
                                    impl_methods,
                                );
                            }
                        }
                    }
                }
            }

            // Clear all resource entries
            BDD_RESOURCE_VALUES.with(|cell| cell.borrow_mut().clear());

            Ok(Some(Value::Nil))
        }
        // BDD Matchers
        "be_true" => Ok(Some(Value::Matcher(MatcherValue::BeTrue))),
        "be_false" => Ok(Some(Value::Matcher(MatcherValue::BeFalse))),
        "eq" => {
            let expected = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(MatcherValue::Exact(Box::new(expected)))))
        }
        "GreaterThan" => {
            let threshold = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
            let n = match threshold {
                Value::Int(i) => i,
                Value::Float(f) => f as i64,
                _ => 0,
            };
            Ok(Some(Value::Matcher(MatcherValue::GreaterThan(n))))
        }
        "LessThan" => {
            let threshold = eval_arg(args, 0, Value::Int(0), env, functions, classes, enums, impl_methods)?;
            let n = match threshold {
                Value::Int(i) => i,
                Value::Float(f) => f as i64,
                _ => 0,
            };
            Ok(Some(Value::Matcher(MatcherValue::LessThan(n))))
        }
        "to_equal" => {
            // Alias for eq
            let expected = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            Ok(Some(Value::Matcher(MatcherValue::Exact(Box::new(expected)))))
        }
        "be_close_to" => {
            let target = eval_arg(args, 0, Value::Float(0.0), env, functions, classes, enums, impl_methods)?;
            let epsilon = if args.len() > 1 {
                eval_arg(args, 1, Value::Float(0.001), env, functions, classes, enums, impl_methods)?
            } else {
                Value::Float(0.001)
            };
            let target_f = match target {
                Value::Float(f) => f,
                Value::Int(i) => i as f64,
                _ => 0.0,
            };
            let epsilon_f = match epsilon {
                Value::Float(f) => f,
                Value::Int(i) => i as f64,
                _ => 0.001,
            };
            Ok(Some(Value::Matcher(MatcherValue::BeCloseTo {
                target: target_f,
                epsilon: epsilon_f,
            })))
        }
        // BDD Registry FFI functions - shared across all modules
        "__bdd_register_group" => {
            let group = eval_arg(args, 0, Value::Nil, env, functions, classes, enums, impl_methods)?;
            BDD_REGISTRY_GROUPS.with(|cell: &BddGroupsCell| {
                cell.borrow_mut().push(group);
            });
            Ok(Some(Value::Nil))
        }
        "__bdd_get_all_groups" => {
            let groups = BDD_REGISTRY_GROUPS.with(|cell: &BddGroupsCell| cell.borrow().clone());
            Ok(Some(Value::Array(groups)))
        }
        "__bdd_clear_groups" => {
            BDD_REGISTRY_GROUPS.with(|cell: &BddGroupsCell| {
                cell.borrow_mut().clear();
            });
            Ok(Some(Value::Nil))
        }
        "__bdd_register_context" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match name {
                Value::Str(s) => s,
                Value::Symbol(s) => s,
                _ => "".to_string(),
            };
            let ctx_def = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            BDD_REGISTRY_CONTEXTS.with(|cell: &BddContextsCell| {
                cell.borrow_mut().insert(name_str, ctx_def);
            });
            Ok(Some(Value::Nil))
        }
        "__bdd_get_context" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match name {
                Value::Str(s) => s,
                Value::Symbol(s) => s,
                _ => "".to_string(),
            };
            let result = BDD_REGISTRY_CONTEXTS.with(|cell: &BddContextsCell| cell.borrow().get(&name_str).cloned());
            match result {
                Some(ctx) => Ok(Some(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Some(Box::new(ctx)),
                })),
                None => Ok(Some(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: None,
                })),
            }
        }
        "__bdd_clear_contexts" => {
            BDD_REGISTRY_CONTEXTS.with(|cell: &BddContextsCell| {
                cell.borrow_mut().clear();
            });
            Ok(Some(Value::Nil))
        }
        "__bdd_register_shared_examples" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match name {
                Value::Str(s) => s,
                Value::Symbol(s) => s,
                _ => "".to_string(),
            };
            let shared_def = eval_arg(args, 1, Value::Nil, env, functions, classes, enums, impl_methods)?;
            BDD_REGISTRY_SHARED.with(|cell: &BddSharedCell| {
                cell.borrow_mut().insert(name_str, shared_def);
            });
            Ok(Some(Value::Nil))
        }
        "__bdd_get_shared_examples" => {
            let name = eval_arg(
                args,
                0,
                Value::Str("".to_string()),
                env,
                functions,
                classes,
                enums,
                impl_methods,
            )?;
            let name_str = match name {
                Value::Str(s) => s,
                Value::Symbol(s) => s,
                _ => "".to_string(),
            };
            let result = BDD_REGISTRY_SHARED.with(|cell: &BddSharedCell| cell.borrow().get(&name_str).cloned());
            match result {
                Some(shared) => Ok(Some(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "Some".to_string(),
                    payload: Some(Box::new(shared)),
                })),
                None => Ok(Some(Value::Enum {
                    enum_name: "Option".to_string(),
                    variant: "None".to_string(),
                    payload: None,
                })),
            }
        }
        "__bdd_clear_shared_examples" => {
            BDD_REGISTRY_SHARED.with(|cell: &BddSharedCell| {
                cell.borrow_mut().clear();
            });
            Ok(Some(Value::Nil))
        }
        "__bdd_reset_registry" => {
            BDD_REGISTRY_GROUPS.with(|cell: &BddGroupsCell| {
                cell.borrow_mut().clear();
            });
            BDD_REGISTRY_CONTEXTS.with(|cell: &BddContextsCell| {
                cell.borrow_mut().clear();
            });
            BDD_REGISTRY_SHARED.with(|cell: &BddSharedCell| {
                cell.borrow_mut().clear();
            });
            Ok(Some(Value::Nil))
        }
        _ => Ok(None),
    }
}

/// Clear all BDD testing state.
///
/// This function clears all thread-local BDD state to prevent memory leaks
/// and state pollution between test files. It clears:
/// - Indentation level
/// - Pass/fail counts
/// - Expectation state
/// - Shared examples
/// - Context definitions
/// - Before/after hooks
/// - Lazy values
/// - Group stack
/// - Global registries
pub fn clear_bdd_state() {
    // Clear local BDD state
    BDD_INDENT.with(|cell| *cell.borrow_mut() = 0);
    BDD_COUNTS.with(|cell| *cell.borrow_mut() = (0, 0));
    BDD_EXPECT_FAILED.with(|cell| *cell.borrow_mut() = false);
    BDD_INSIDE_IT.with(|cell| *cell.borrow_mut() = false);
    BDD_FAILURE_MSG.with(|cell| *cell.borrow_mut() = None);
    BDD_SHARED_EXAMPLES.with(|cell| cell.borrow_mut().clear());
    BDD_CONTEXT_DEFS.with(|cell| cell.borrow_mut().clear());
    BDD_BEFORE_EACH.with(|cell| *cell.borrow_mut() = vec![vec![]]);
    BDD_AFTER_EACH.with(|cell| *cell.borrow_mut() = vec![vec![]]);
    // Clear hook caches when resetting BDD state
    invalidate_hook_caches();
    BDD_LAZY_VALUES.with(|cell| cell.borrow_mut().clear());
    BDD_RESOURCE_VALUES.with(|cell| cell.borrow_mut().clear());
    BDD_GROUP_STACK.with(|cell| cell.borrow_mut().clear());

    // Clear global registries
    BDD_REGISTRY_GROUPS.with(|cell: &BddGroupsCell| cell.borrow_mut().clear());
    BDD_REGISTRY_CONTEXTS.with(|cell: &BddContextsCell| cell.borrow_mut().clear());
    BDD_REGISTRY_SHARED.with(|cell: &BddSharedCell| cell.borrow_mut().clear());
}
