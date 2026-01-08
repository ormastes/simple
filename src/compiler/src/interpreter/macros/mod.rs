use super::*;

// Macro invocation and expansion (part of interpreter module)

use simple_parser::ast::MacroAnchor;
use crate::macro_contracts::{process_macro_contract, MacroContractResult};
use crate::macro_validation::validate_macro_defined_before_use;

#[path = "../../interpreter_macro/helpers.rs"]
mod helpers;
use helpers::{build_macro_const_bindings, const_value_to_string};

mod state;
pub(crate) use state::{
    enter_block_scope, exit_block_scope, queue_tail_injection, set_macro_trace,
    store_macro_introduced_symbols, take_macro_introduced_symbols,
};
use state::{is_macro_trace_enabled, macro_trace, pop_macro_depth, push_macro_depth};

/// Convert an expression to its source code string representation
fn expr_to_source_string(expr: &Expr) -> String {
    use simple_parser::ast::BinOp;

    match expr {
        Expr::Integer(i) => i.to_string(),
        Expr::Float(f) => f.to_string(),
        Expr::Bool(b) => b.to_string(),
        Expr::String(s) => format!("\"{}\"", s),
        Expr::Identifier(name) => name.clone(),
        Expr::Binary { op, left, right } => {
            let op_str = match op {
                BinOp::Add => "+",
                BinOp::Sub => "-",
                BinOp::Mul => "*",
                BinOp::Div => "/",
                BinOp::Mod => "%",
                BinOp::Eq => "==",
                BinOp::NotEq => "!=",
                BinOp::Lt => "<",
                BinOp::LtEq => "<=",
                BinOp::Gt => ">",
                BinOp::GtEq => ">=",
                BinOp::And => "and",
                BinOp::Or => "or",
                _ => "?",
            };
            format!("({} {} {})", expr_to_source_string(left), op_str, expr_to_source_string(right))
        }
        Expr::Unary { op, operand } => {
            let op_str = match op {
                simple_parser::ast::UnaryOp::Neg => "-",
                simple_parser::ast::UnaryOp::Not => "not ",
                _ => "?",
            };
            format!("{}{}", op_str, expr_to_source_string(operand))
        }
        Expr::Call { callee, args } => {
            let args_str: Vec<String> = args.iter().map(|a| expr_to_source_string(&a.value)).collect();
            format!("{}({})", expr_to_source_string(callee), args_str.join(", "))
        }
        Expr::MethodCall { receiver, method, args } => {
            let args_str: Vec<String> = args.iter().map(|a| expr_to_source_string(&a.value)).collect();
            format!("{}.{}({})", expr_to_source_string(receiver), method, args_str.join(", "))
        }
        Expr::FieldAccess { receiver, field } => {
            format!("{}.{}", expr_to_source_string(receiver), field)
        }
        Expr::Index { receiver, index } => {
            format!("{}[{}]", expr_to_source_string(receiver), expr_to_source_string(index))
        }
        Expr::Array(items) => {
            let items_str: Vec<String> = items.iter().map(|i| expr_to_source_string(i)).collect();
            format!("[{}]", items_str.join(", "))
        }
        Expr::Tuple(items) => {
            let items_str: Vec<String> = items.iter().map(|i| expr_to_source_string(i)).collect();
            format!("({})", items_str.join(", "))
        }
        Expr::Lambda { params, body, .. } => {
            let params_str: Vec<String> = params.iter().map(|p| p.name.clone()).collect();
            format!("fn({}) -> ...", params_str.join(", "))
        }
        Expr::If { condition, then_branch, else_branch } => {
            let else_str = else_branch.as_ref()
                .map(|e| format!(" else {}", expr_to_source_string(e)))
                .unwrap_or_default();
            format!("if {}: ...{}", expr_to_source_string(condition), else_str)
        }
        Expr::Nil => "nil".to_string(),
        _ => format!("{:?}", expr), // Fallback for complex expressions
    }
}

pub(crate) fn evaluate_macro_invocation(
    name: &str,
    macro_args: &[MacroArg],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    match name {
        "println" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            println!("{}", output);
            Ok(Value::Nil)
        }
        "print" => {
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                print!("{}", val.to_display_string());
            }
            Ok(Value::Nil)
        }
        "vec" => {
            let mut items = Vec::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                items.push(evaluate_expr(e, env, functions, classes, enums, impl_methods)?);
            }
            Ok(Value::Array(items))
        }
        "assert" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                if !val.truthy() {
                    return Err(CompileError::Semantic("assertion failed".into()));
                }
            }
            Ok(Value::Nil)
        }
        "assert_eq" => {
            if macro_args.len() >= 2 {
                let (MacroArg::Expr(left), MacroArg::Expr(right)) = (&macro_args[0], &macro_args[1]);
                let left_val = evaluate_expr(left, env, functions, classes, enums, impl_methods)?;
                let right_val = evaluate_expr(right, env, functions, classes, enums, impl_methods)?;
                if left_val != right_val {
                    return Err(CompileError::Semantic(format!(
                        "assertion failed: {:?} != {:?}",
                        left_val, right_val
                    )));
                }
            }
            Ok(Value::Nil)
        }
        "assert_unit" => {
            // assert_unit!(value, "unit_type") - validate value is of expected unit type
            if macro_args.len() >= 2 {
                let (MacroArg::Expr(value_expr), MacroArg::Expr(type_expr)) =
                    (&macro_args[0], &macro_args[1]);
                let value = evaluate_expr(value_expr, env, functions, classes, enums, impl_methods)?;
                let type_val = evaluate_expr(type_expr, env, functions, classes, enums, impl_methods)?;

                // Extract type name from string or symbol
                let type_name = match &type_val {
                    Value::Str(s) => s.clone(),
                    Value::Symbol(s) => s.clone(),
                    _ => {
                        return Err(CompileError::Semantic(
                            "assert_unit: second argument must be a string or symbol representing the unit type".into(),
                        ));
                    }
                };

                // Check if the type is a valid unit type
                if !is_unit_type(&type_name) {
                    return Err(CompileError::Semantic(format!(
                        "assert_unit: '{}' is not a registered unit type (family or compound unit)",
                        type_name
                    )));
                }

                // Validate the value against the unit type
                if let Err(e) = validate_unit_type(&value, &type_name) {
                    return Err(CompileError::Semantic(format!(
                        "unit assertion failed: {}",
                        e
                    )));
                }
            } else {
                return Err(CompileError::Semantic(
                    "assert_unit requires two arguments: assert_unit!(value, \"unit_type\")".into(),
                ));
            }
            Ok(Value::Nil)
        }
        "panic" => {
            let msg = macro_args
                .first()
                .map(|arg| {
                    if let MacroArg::Expr(e) = arg {
                        evaluate_expr(e, env, functions, classes, enums, impl_methods)
                            .map(|v| v.to_display_string())
                            .unwrap_or_else(|_| "panic".into())
                    } else {
                        "panic".into()
                    }
                })
                .unwrap_or_else(|| "explicit panic".into());
            Err(CompileError::Semantic(format!("panic: {}", msg)))
        }
        "format" => {
            let mut output = String::new();
            for arg in macro_args {
                let MacroArg::Expr(e) = arg;
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                output.push_str(&val.to_display_string());
            }
            Ok(Value::Str(output))
        }
        "dbg" => {
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                eprintln!("[dbg] {:?}", val);
                Ok(val)
            } else {
                Ok(Value::Nil)
            }
        }
        "stringify" => {
            // Convert expression to its source code string representation
            if let Some(MacroArg::Expr(e)) = macro_args.first() {
                Ok(Value::Str(expr_to_source_string(e)))
            } else {
                Ok(Value::Str(String::new()))
            }
        }
        _ => {
            let macro_def = USER_MACROS.with(|cell| cell.borrow().get(name).cloned());
            if let Some(m) = macro_def {
                expand_user_macro(&m, macro_args, env, functions, classes, enums, impl_methods)
            } else {
                Err(CompileError::Semantic(format!("unknown macro: {}!", name)))
            }
        }
    }
}

/// Expand a user-defined macro with given arguments
fn expand_user_macro(
    macro_def: &MacroDef,
    args: &[MacroArg],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Check and increment macro expansion depth (prevents infinite recursion)
    push_macro_depth(&macro_def.name)?;

    // Use inner function to ensure we always pop depth, even on error
    let result = expand_user_macro_inner(macro_def, args, env, functions, classes, enums, impl_methods);
    pop_macro_depth();
    result
}

/// Inner implementation of expand_user_macro (separated for depth tracking)
fn expand_user_macro_inner(
    macro_def: &MacroDef,
    args: &[MacroArg],
    env: &Env,
    functions: &mut HashMap<String, FunctionDef>,
    classes: &mut HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    macro_trace(&format!("expanding {}!(...)", macro_def.name));

    // Validate ordering: macro must be defined before use (#1304)
    let definition_order = MACRO_DEFINITION_ORDER.with(|cell| cell.borrow().clone());
    validate_macro_defined_before_use(&macro_def.name, 0, &definition_order)?;

    let mut local_env = env.clone();
    let const_bindings = build_macro_const_bindings(macro_def, args, env, functions, classes, enums, impl_methods)?;
    let mut hygiene_ctx = MacroHygieneContext::new();

    // Process macro contracts to determine introduced symbols (#1303)
    // Also performs shadowing validation (#1304)
    let mut contract_result = process_macro_contract(macro_def, &const_bindings, env, functions, classes)?;

    // Find if there's a variadic parameter (must be last if present)
    if let Some(variadic_idx) = macro_def.params.iter().position(|p| p.is_variadic) {
        if variadic_idx != macro_def.params.len() - 1 {
            return Err(CompileError::Semantic(
                "Variadic parameter must be the last parameter".to_string()
            ));
        }
    }

    for (idx, param) in macro_def.params.iter().enumerate() {
        if param.is_variadic {
            // Variadic parameter: collect all remaining arguments into an array
            let mut variadic_values = Vec::new();
            for arg in args.iter().skip(idx) {
                if let MacroArg::Expr(e) = arg {
                    let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
                    variadic_values.push(val);
                }
            }
            local_env.insert(param.name.clone(), Value::Array(variadic_values));
        } else if let Some(MacroArg::Expr(e)) = args.get(idx) {
            let val = evaluate_expr(e, env, functions, classes, enums, impl_methods)?;
            local_env.insert(param.name.clone(), val);
        }
    }

    let return_label = macro_def
        .contract
        .iter()
        .find_map(|item| match item {
            MacroContractItem::Returns(ret) => ret.label.clone(),
            _ => None,
        });

    let mut last_value = Value::Nil;

    for stmt in &macro_def.body {
        match stmt {
            MacroStmt::ConstEval(block) => {
                let hygienic_block = apply_macro_hygiene_block(block, &mut hygiene_ctx, false);
                match exec_block(&hygienic_block, &mut local_env, functions, classes, enums, impl_methods)? {
                    Control::Return(v) => return Ok(v),
                    Control::Break(_) | Control::Continue => {}
                    Control::Next => {}
                }
            }
            MacroStmt::Emit { label, block } => {
                // Check if this emit block is for an inject (code injection)
                let inject_anchor = contract_result.inject_labels.get(label).cloned();

                // Snapshot current functions in local_env before executing emit block
                let functions_before: HashSet<String> = local_env.iter()
                    .filter_map(|(k, v)| if matches!(v, Value::Function { .. }) { Some(k.clone()) } else { None })
                    .collect();

                let expanded_block = substitute_block_templates(block, &const_bindings);
                let hygienic_block = apply_macro_hygiene_block(&expanded_block, &mut hygiene_ctx, false);

                // Handle inject blocks specially based on anchor type
                let (control, maybe_value) = if let Some(anchor) = inject_anchor {
                    match anchor {
                        MacroAnchor::Tail => {
                            // Queue for execution at block exit
                            queue_tail_injection(hygienic_block.clone());
                            (Control::Next, None)
                        }
                        MacroAnchor::Head => {
                            // Head injection cannot go back in time in an interpreter model
                            // Execute immediately as a fallback (with a warning in trace mode)
                            if is_macro_trace_enabled() {
                                macro_trace("  [warning] 'head' inject executes at callsite (cannot rewind)");
                            }
                            exec_block_fn(&hygienic_block, &mut local_env, functions, classes, enums, impl_methods)?
                        }
                        MacroAnchor::Here => {
                            // Execute immediately at the callsite
                            exec_block_fn(&hygienic_block, &mut local_env, functions, classes, enums, impl_methods)?
                        }
                    }
                } else {
                    // Not an inject block - execute normally
                    exec_block_fn(&hygienic_block, &mut local_env, functions, classes, enums, impl_methods)?
                };

                // Find new functions defined in this emit block and match to intro stubs
                // Track which stubs were matched by name (for for-loop cases)
                let mut matched_by_name = false;
                for (name, value) in local_env.iter() {
                    if let Value::Function { def, .. } = value {
                        // Check if this function was newly defined in this emit block
                        if !functions_before.contains(name) {
                            // Strip gensym suffix to get the original function name
                            let original_name = strip_gensym_suffix(&def.name);

                            // Check if this matches an intro stub by name
                            if contract_result.introduced_functions.contains_key(&original_name) {
                                // Replace stub with real function definition
                                let mut real_func = (**def).clone();
                                real_func.name = original_name.clone();
                                contract_result.introduced_functions.insert(original_name, real_func);
                                matched_by_name = true;
                            }
                        }
                    }
                }

                // Fallback: if no name-based match, use label-based matching
                // This handles cases where emit function name differs from intro stub name
                if !matched_by_name {
                    if let Some(public_name) = contract_result.intro_function_labels.get(label) {
                        for (name, value) in local_env.iter() {
                            if let Value::Function { def, .. } = value {
                                if !functions_before.contains(name) {
                                    // Register with the public name from intro contract
                                    let mut real_func = (**def).clone();
                                    real_func.name = public_name.clone();
                                    contract_result.introduced_functions.insert(public_name.clone(), real_func);
                                }
                            }
                        }
                    }
                }

                if let Control::Return(v) = control {
                    return Ok(v);
                }
                let should_capture = if let Some(expected) = &return_label {
                    expected == label
                } else {
                    label == "result"
                };
                if should_capture {
                    if let Some(val) = maybe_value {
                        last_value = val;
                    }
                }
            }
            MacroStmt::Stmt(node) => {
                let hygienic_node = apply_macro_hygiene_node(node, &mut hygiene_ctx);
                match exec_node(&hygienic_node, &mut local_env, functions, classes, enums, impl_methods)? {
                Control::Return(v) => return Ok(v),
                Control::Break(_) | Control::Continue => {}
                Control::Next => {}
                }
            }
        }
    }

    // Extract functions from local_env and update contract_result
    // Functions defined in emit blocks are now in local_env as Value::Function
    extract_introduced_functions(&local_env, &mut contract_result);

    // Trace introduced functions
    if is_macro_trace_enabled() && !contract_result.introduced_functions.is_empty() {
        let func_names: Vec<_> = contract_result.introduced_functions.keys().collect();
        macro_trace(&format!("  intro functions: {:?}", func_names));
    }

    // Store contract result in thread-local for caller to retrieve
    store_macro_introduced_symbols(contract_result);

    Ok(last_value)
}

/// Extract function definitions from local_env and add to contract result
fn extract_introduced_functions(local_env: &Env, contract_result: &mut MacroContractResult) {
    for (name, value) in local_env.iter() {
        if let Value::Function { name: func_name, def, .. } = value {
            // Strip gensym suffix to get the original function name
            let original_name = strip_gensym_suffix(func_name);

            // Check if this function matches an intro stub (by original name)
            if contract_result.introduced_functions.contains_key(&original_name) {
                // Replace stub with real function definition
                contract_result.introduced_functions.insert(original_name, (**def).clone());
            } else {
                // Check if the env key (which might also be gensym'd) matches an intro stub
                let original_key = strip_gensym_suffix(name);
                if contract_result.introduced_functions.contains_key(&original_key) {
                    // Replace stub with real function, using original key as the public name
                    let mut real_func = (**def).clone();
                    real_func.name = original_key.clone();
                    contract_result.introduced_functions.insert(original_key, real_func);
                }
            }
        }
    }
}

/// Strip the _gensym_N suffix from a name
fn strip_gensym_suffix(name: &str) -> String {
    if let Some(pos) = name.find("_gensym_") {
        name[..pos].to_string()
    } else {
        name.to_string()
    }
}

#[derive(Debug, Default)]
struct MacroHygieneContext {
    gensym_counter: usize,
    scopes: Vec<HashMap<String, String>>,
}

impl MacroHygieneContext {
    fn new() -> Self {
        Self {
            gensym_counter: 0,
            scopes: vec![HashMap::new()],
        }
    }

    fn push_scope(&mut self) {
        self.scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        self.scopes.pop();
    }

    fn resolve(&self, name: &str) -> Option<String> {
        self.scopes.iter().rev().find_map(|scope| scope.get(name).cloned())
    }

    fn bind(&mut self, name: &str, reuse_if_bound: bool) -> String {
        if reuse_if_bound {
            if let Some(scope) = self.scopes.last() {
                if let Some(existing) = scope.get(name) {
                    return existing.clone();
                }
            }
        }
        self.gensym_counter += 1;
        let new_name = format!("{name}_gensym_{}", self.gensym_counter);
        if let Some(scope) = self.scopes.last_mut() {
            scope.insert(name.to_string(), new_name.clone());
        }
        new_name
    }
}

fn apply_macro_hygiene_block(
    block: &Block,
    ctx: &mut MacroHygieneContext,
    push_scope: bool,
) -> Block {
    if push_scope {
        ctx.push_scope();
    }
    let mut statements = Vec::new();
    for stmt in &block.statements {
        statements.push(apply_macro_hygiene_node(stmt, ctx));
    }
    if push_scope {
        ctx.pop_scope();
    }
    Block {
        span: block.span,
        statements,
    }
}

fn apply_macro_hygiene_node(
    node: &Node,
    ctx: &mut MacroHygieneContext,
) -> Node {
    match node {
        Node::Let(let_stmt) => {
            let value = let_stmt
                .value
                .as_ref()
                .map(|expr| apply_macro_hygiene_expr(expr, ctx));
            let pattern = apply_macro_hygiene_pattern(&let_stmt.pattern, ctx, false);
            Node::Let(LetStmt {
                span: let_stmt.span,
                pattern,
                ty: let_stmt.ty.clone(),
                value,
                mutability: let_stmt.mutability,
                storage_class: let_stmt.storage_class,
                is_ghost: let_stmt.is_ghost,
            })
        }
        Node::Const(const_stmt) => {
            let mut new_stmt = const_stmt.clone();
            new_stmt.value = apply_macro_hygiene_expr(&const_stmt.value, ctx);
            new_stmt.name = ctx.bind(&const_stmt.name, false);
            Node::Const(new_stmt)
        }
        Node::Static(static_stmt) => {
            let mut new_stmt = static_stmt.clone();
            new_stmt.value = apply_macro_hygiene_expr(&static_stmt.value, ctx);
            new_stmt.name = ctx.bind(&static_stmt.name, false);
            Node::Static(new_stmt)
        }
        Node::Assignment(assign) => Node::Assignment(AssignmentStmt {
            span: assign.span,
            target: apply_macro_hygiene_expr(&assign.target, ctx),
            op: assign.op,
            value: apply_macro_hygiene_expr(&assign.value, ctx),
        }),
        Node::Return(ret) => Node::Return(ReturnStmt {
            span: ret.span,
            value: ret
                .value
                .as_ref()
                .map(|expr| apply_macro_hygiene_expr(expr, ctx)),
        }),
        Node::If(stmt) => {
            if let Some(let_pattern) = &stmt.let_pattern {
                let condition = apply_macro_hygiene_expr(&stmt.condition, ctx);
                ctx.push_scope();
                let new_pattern = apply_macro_hygiene_pattern(let_pattern, ctx, false);
                let then_block = apply_macro_hygiene_block(&stmt.then_block, ctx, false);
                ctx.pop_scope();
                let elif_branches = stmt
                    .elif_branches
                    .iter()
                    .map(|(cond, block)| {
                        (
                            apply_macro_hygiene_expr(cond, ctx),
                            apply_macro_hygiene_block(block, ctx, true),
                        )
                    })
                    .collect();
                let else_block = stmt
                    .else_block
                    .as_ref()
                    .map(|block| apply_macro_hygiene_block(block, ctx, true));
                Node::If(IfStmt {
                    span: stmt.span,
                    condition,
                    then_block,
                    elif_branches,
                    else_block,
                    let_pattern: Some(new_pattern),
                    is_suspend: stmt.is_suspend,
                })
            } else {
                Node::If(IfStmt {
                    span: stmt.span,
                    condition: apply_macro_hygiene_expr(&stmt.condition, ctx),
                    then_block: apply_macro_hygiene_block(&stmt.then_block, ctx, true),
                    elif_branches: stmt
                        .elif_branches
                        .iter()
                        .map(|(cond, block)| {
                            (
                                apply_macro_hygiene_expr(cond, ctx),
                                apply_macro_hygiene_block(block, ctx, true),
                            )
                        })
                        .collect(),
                    else_block: stmt
                        .else_block
                        .as_ref()
                        .map(|block| apply_macro_hygiene_block(block, ctx, true)),
                    let_pattern: None,
                    is_suspend: stmt.is_suspend,
                })
            }
        }
        Node::Match(stmt) => Node::Match(MatchStmt {
            span: stmt.span,
            subject: apply_macro_hygiene_expr(&stmt.subject, ctx),
            arms: stmt
                .arms
                .iter()
                .map(|arm| {
                    ctx.push_scope();
                    let pattern = apply_macro_hygiene_pattern(&arm.pattern, ctx, true);
                    let guard = arm
                        .guard
                        .as_ref()
                        .map(|expr| apply_macro_hygiene_expr(expr, ctx));
                    let body = apply_macro_hygiene_block(&arm.body, ctx, false);
                    ctx.pop_scope();
                    MatchArm {
                        span: arm.span,
                        pattern,
                        guard,
                        body,
                    }
                })
                .collect(),
        }),
        Node::For(stmt) => {
            let iterable = apply_macro_hygiene_expr(&stmt.iterable, ctx);
            ctx.push_scope();
            let pattern = apply_macro_hygiene_pattern(&stmt.pattern, ctx, false);
            let body = apply_macro_hygiene_block(&stmt.body, ctx, false);
            ctx.pop_scope();
            Node::For(ForStmt {
                span: stmt.span,
                pattern,
                iterable,
                body,
                is_suspend: stmt.is_suspend,
            })
        }
        Node::While(stmt) => {
            let condition = apply_macro_hygiene_expr(&stmt.condition, ctx);
            let (let_pattern, body) = if let Some(let_pattern) = &stmt.let_pattern {
                ctx.push_scope();
                let new_pattern = apply_macro_hygiene_pattern(let_pattern, ctx, false);
                let new_body = apply_macro_hygiene_block(&stmt.body, ctx, false);
                ctx.pop_scope();
                (Some(new_pattern), new_body)
            } else {
                (None, apply_macro_hygiene_block(&stmt.body, ctx, true))
            };
            Node::While(WhileStmt {
                span: stmt.span,
                condition,
                body,
                let_pattern,
                is_suspend: stmt.is_suspend,
            })
        }
        Node::Loop(stmt) => Node::Loop(LoopStmt {
            span: stmt.span,
            body: apply_macro_hygiene_block(&stmt.body, ctx, true),
        }),
        Node::Context(stmt) => Node::Context(ContextStmt {
            span: stmt.span,
            context: apply_macro_hygiene_expr(&stmt.context, ctx),
            body: apply_macro_hygiene_block(&stmt.body, ctx, true),
        }),
        Node::With(stmt) => {
            let resource = apply_macro_hygiene_expr(&stmt.resource, ctx);
            if let Some(name) = &stmt.name {
                ctx.push_scope();
                let new_name = ctx.bind(name, false);
                let body = apply_macro_hygiene_block(&stmt.body, ctx, false);
                ctx.pop_scope();
                Node::With(WithStmt {
                    span: stmt.span,
                    resource,
                    name: Some(new_name),
                    body,
                })
            } else {
                Node::With(WithStmt {
                    span: stmt.span,
                    resource,
                    name: None,
                    body: apply_macro_hygiene_block(&stmt.body, ctx, true),
                })
            }
        }
        Node::Function(def) => {
            let mut new_def = def.clone();
            new_def.name = ctx.bind(&def.name, false);
            ctx.push_scope();
            let mut params = Vec::with_capacity(def.params.len());
            for param in &def.params {
                let default = param
                    .default
                    .as_ref()
                    .map(|expr| apply_macro_hygiene_expr(expr, ctx));
                let new_name = ctx.bind(&param.name, false);
                let mut new_param = param.clone();
                new_param.name = new_name;
                new_param.default = default;
                params.push(new_param);
            }
            new_def.params = params;
            new_def.body = apply_macro_hygiene_block(&def.body, ctx, false);
            ctx.pop_scope();
            Node::Function(new_def)
        }
        Node::Expression(expr) => Node::Expression(apply_macro_hygiene_expr(expr, ctx)),
        _ => node.clone(),
    }
}

fn apply_macro_hygiene_expr(
    expr: &Expr,
    ctx: &mut MacroHygieneContext,
) -> Expr {
    match expr {
        Expr::Identifier(name) => ctx
            .resolve(name)
            .map(Expr::Identifier)
            .unwrap_or_else(|| expr.clone()),
        Expr::FString(parts) => Expr::FString(
            parts
                .iter()
                .map(|part| match part {
                    FStringPart::Literal(text) => FStringPart::Literal(text.clone()),
                    FStringPart::Expr(expr) => FStringPart::Expr(apply_macro_hygiene_expr(expr, ctx)),
                })
                .collect(),
        ),
        Expr::Binary { op, left, right } => Expr::Binary {
            op: op.clone(),
            left: Box::new(apply_macro_hygiene_expr(left, ctx)),
            right: Box::new(apply_macro_hygiene_expr(right, ctx)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op: *op,
            operand: Box::new(apply_macro_hygiene_expr(operand, ctx)),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(apply_macro_hygiene_expr(callee, ctx)),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: apply_macro_hygiene_expr(&arg.value, ctx),
                })
                .collect(),
        },
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => Expr::MethodCall {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: apply_macro_hygiene_expr(&arg.value, ctx),
                })
                .collect(),
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            field: field.clone(),
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            index: Box::new(apply_macro_hygiene_expr(index, ctx)),
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            index: *index,
        },
        Expr::Lambda {
            params,
            body,
            move_mode,
        } => {
            ctx.push_scope();
            let new_params = params
                .iter()
                .map(|param| {
                    let new_name = ctx.bind(&param.name, false);
                    simple_parser::ast::LambdaParam {
                        name: new_name,
                        ty: param.ty.clone(),
                    }
                })
                .collect();
            let new_body = apply_macro_hygiene_expr(body, ctx);
            ctx.pop_scope();
            Expr::Lambda {
                params: new_params,
                body: Box::new(new_body),
                move_mode: *move_mode,
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: Box::new(apply_macro_hygiene_expr(condition, ctx)),
            then_branch: Box::new(apply_macro_hygiene_expr(then_branch, ctx)),
            else_branch: else_branch
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
        },
        Expr::Match { subject, arms } => Expr::Match {
            subject: Box::new(apply_macro_hygiene_expr(subject, ctx)),
            arms: arms
                .iter()
                .map(|arm| {
                    ctx.push_scope();
                    let pattern = apply_macro_hygiene_pattern(&arm.pattern, ctx, true);
                    let guard = arm
                        .guard
                        .as_ref()
                        .map(|expr| apply_macro_hygiene_expr(expr, ctx));
                    let body = apply_macro_hygiene_block(&arm.body, ctx, false);
                    ctx.pop_scope();
                    MatchArm {
                        span: arm.span,
                        pattern,
                        guard,
                        body,
                    }
                })
                .collect(),
        },
        Expr::Tuple(items) => {
            Expr::Tuple(items.iter().map(|item| apply_macro_hygiene_expr(item, ctx)).collect())
        }
        Expr::Array(items) => {
            Expr::Array(items.iter().map(|item| apply_macro_hygiene_expr(item, ctx)).collect())
        }
        Expr::VecLiteral(items) => Expr::VecLiteral(
            items
                .iter()
                .map(|item| apply_macro_hygiene_expr(item, ctx))
                .collect(),
        ),
        Expr::Dict(entries) => Expr::Dict(
            entries
                .iter()
                .map(|(k, v)| {
                    (
                        apply_macro_hygiene_expr(k, ctx),
                        apply_macro_hygiene_expr(v, ctx),
                    )
                })
                .collect(),
        ),
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => {
            let iterable = apply_macro_hygiene_expr(iterable, ctx);
            ctx.push_scope();
            let pattern = apply_macro_hygiene_pattern(pattern, ctx, false);
            let expr = apply_macro_hygiene_expr(expr, ctx);
            let condition = condition
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx)));
            ctx.pop_scope();
            Expr::ListComprehension {
                expr: Box::new(expr),
                pattern,
                iterable: Box::new(iterable),
                condition,
            }
        }
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => {
            let iterable = apply_macro_hygiene_expr(iterable, ctx);
            ctx.push_scope();
            let pattern = apply_macro_hygiene_pattern(pattern, ctx, false);
            let key = apply_macro_hygiene_expr(key, ctx);
            let value = apply_macro_hygiene_expr(value, ctx);
            let condition = condition
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx)));
            ctx.pop_scope();
            Expr::DictComprehension {
                key: Box::new(key),
                value: Box::new(value),
                pattern,
                iterable: Box::new(iterable),
                condition,
            }
        }
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: Box::new(apply_macro_hygiene_expr(receiver, ctx)),
            start: start
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            end: end
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            step: step
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
        },
        Expr::Spread(expr) => Expr::Spread(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::DictSpread(expr) => {
            Expr::DictSpread(Box::new(apply_macro_hygiene_expr(expr, ctx)))
        }
        Expr::StructInit { name, fields } => Expr::StructInit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(field, expr)| {
                    (
                        field.clone(),
                        apply_macro_hygiene_expr(expr, ctx),
                    )
                })
                .collect(),
        },
        Expr::Spawn(expr) => Expr::Spawn(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::Await(expr) => Expr::Await(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::Yield(expr) => Expr::Yield(
            expr
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
        ),
        Expr::New { kind, expr } => Expr::New {
            kind: *kind,
            expr: Box::new(apply_macro_hygiene_expr(expr, ctx)),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: Box::new(apply_macro_hygiene_expr(expr, ctx)),
            target_type: target_type.clone(),
        },
        Expr::Range { start, end, bound } => Expr::Range {
            start: start
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            end: end
                .as_ref()
                .map(|expr| Box::new(apply_macro_hygiene_expr(expr, ctx))),
            bound: *bound,
        },
        Expr::FunctionalUpdate { target, method, args } => Expr::FunctionalUpdate {
            target: Box::new(apply_macro_hygiene_expr(target, ctx)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: apply_macro_hygiene_expr(&arg.value, ctx),
                })
                .collect(),
        },
        Expr::MacroInvocation { name, args } => Expr::MacroInvocation {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| match arg {
                    MacroArg::Expr(expr) => MacroArg::Expr(apply_macro_hygiene_expr(expr, ctx)),
                })
                .collect(),
        },
        Expr::Try(expr) => Expr::Try(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::ContractOld(expr) => Expr::ContractOld(Box::new(apply_macro_hygiene_expr(expr, ctx))),
        Expr::DoBlock(nodes) => {
            ctx.push_scope();
            let mut statements = Vec::new();
            for node in nodes {
                statements.push(apply_macro_hygiene_node(node, ctx));
            }
            ctx.pop_scope();
            Expr::DoBlock(statements)
        }
        _ => expr.clone(),
    }
}

fn apply_macro_hygiene_pattern(
    pattern: &Pattern,
    ctx: &mut MacroHygieneContext,
    reuse_if_bound: bool,
) -> Pattern {
    match pattern {
        Pattern::Identifier(name) => Pattern::Identifier(ctx.bind(name, reuse_if_bound)),
        Pattern::MutIdentifier(name) => Pattern::MutIdentifier(ctx.bind(name, reuse_if_bound)),
        Pattern::Literal(expr) => {
            Pattern::Literal(Box::new(apply_macro_hygiene_expr(expr, ctx)))
        }
        Pattern::Tuple(items) => Pattern::Tuple(
            items
                .iter()
                .map(|item| apply_macro_hygiene_pattern(item, ctx, reuse_if_bound))
                .collect(),
        ),
        Pattern::Array(items) => Pattern::Array(
            items
                .iter()
                .map(|item| apply_macro_hygiene_pattern(item, ctx, reuse_if_bound))
                .collect(),
        ),
        Pattern::Struct { name, fields } => Pattern::Struct {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(field, pat)| {
                    (
                        field.clone(),
                        apply_macro_hygiene_pattern(pat, ctx, reuse_if_bound),
                    )
                })
                .collect(),
        },
        Pattern::Enum {
            name,
            variant,
            payload,
        } => Pattern::Enum {
            name: name.clone(),
            variant: variant.clone(),
            payload: payload.as_ref().map(|payload| {
                payload
                    .iter()
                    .map(|pat| apply_macro_hygiene_pattern(pat, ctx, reuse_if_bound))
                    .collect()
            }),
        },
        Pattern::Or(patterns) => Pattern::Or(
            patterns
                .iter()
                .map(|pat| apply_macro_hygiene_pattern(pat, ctx, true))
                .collect(),
        ),
        Pattern::Typed { pattern, ty } => Pattern::Typed {
            pattern: Box::new(apply_macro_hygiene_pattern(pattern, ctx, reuse_if_bound)),
            ty: ty.clone(),
        },
        Pattern::Range {
            start,
            end,
            inclusive,
        } => Pattern::Range {
            start: Box::new(apply_macro_hygiene_expr(start, ctx)),
            end: Box::new(apply_macro_hygiene_expr(end, ctx)),
            inclusive: *inclusive,
        },
        _ => pattern.clone(),
    }
}

fn substitute_block_templates(
    block: &Block,
    const_bindings: &HashMap<String, String>,
) -> Block {
    let mut statements = Vec::new();
    for stmt in &block.statements {
        // Check if this is a for-loop that can be unrolled at const-eval time
        if let Some(unrolled) = try_unroll_const_for_loop(stmt, const_bindings) {
            statements.extend(unrolled);
        } else {
            statements.push(substitute_node_templates(stmt, const_bindings));
        }
    }
    Block {
        span: block.span,
        statements,
    }
}

/// Try to unroll a for-loop at const-eval time if it has const bounds
/// Returns None if the loop can't be unrolled (not a const range)
fn try_unroll_const_for_loop(
    node: &Node,
    const_bindings: &HashMap<String, String>,
) -> Option<Vec<Node>> {
    // Only handle Node::For
    let for_stmt = match node {
        Node::For(stmt) => stmt,
        _ => return None,
    };

    // Check if the iterable is a range expression with const bounds
    let (start, end) = match &for_stmt.iterable {
        Expr::Range { start, end, bound: RangeBound::Exclusive } => {
            let start_val = eval_const_expr_to_i64(start.as_ref()?, const_bindings)?;
            let end_val = eval_const_expr_to_i64(end.as_ref()?, const_bindings)?;
            (start_val, end_val)
        }
        Expr::Range { start, end, bound: RangeBound::Inclusive } => {
            let start_val = eval_const_expr_to_i64(start.as_ref()?, const_bindings)?;
            let end_val = eval_const_expr_to_i64(end.as_ref()?, const_bindings)?;
            (start_val, end_val + 1) // Inclusive, so add 1 to end
        }
        _ => return None,
    };

    // Get the loop variable name from the pattern
    let loop_var = match &for_stmt.pattern {
        Pattern::Identifier(name) => name.clone(),
        _ => return None, // Only simple identifier patterns for now
    };

    // Unroll the loop
    let mut unrolled_statements = Vec::new();
    for i in start..end {
        // Create new bindings with the loop variable
        let mut iter_bindings = const_bindings.clone();
        iter_bindings.insert(loop_var.clone(), i.to_string());

        // Substitute and add all statements from the loop body
        for body_stmt in &for_stmt.body.statements {
            // Recursively try to unroll nested const for-loops
            if let Some(nested_unrolled) = try_unroll_const_for_loop(body_stmt, &iter_bindings) {
                unrolled_statements.extend(nested_unrolled);
            } else {
                unrolled_statements.push(substitute_node_templates(body_stmt, &iter_bindings));
            }
        }
    }

    Some(unrolled_statements)
}

/// Evaluate a const expression to i64
fn eval_const_expr_to_i64(expr: &Expr, const_bindings: &HashMap<String, String>) -> Option<i64> {
    match expr {
        Expr::Integer(i) => Some(*i),
        Expr::Identifier(name) => {
            const_bindings.get(name).and_then(|v| v.parse::<i64>().ok())
        }
        Expr::Binary { op, left, right } => {
            let l = eval_const_expr_to_i64(left, const_bindings)?;
            let r = eval_const_expr_to_i64(right, const_bindings)?;
            match op {
                BinOp::Add => Some(l + r),
                BinOp::Sub => Some(l - r),
                BinOp::Mul => Some(l * r),
                BinOp::Div => Some(l / r),
                BinOp::Mod => Some(l % r),
                _ => None,
            }
        }
        _ => None,
    }
}

fn substitute_node_templates(
    node: &Node,
    const_bindings: &HashMap<String, String>,
) -> Node {
    match node {
        Node::Expression(expr) => Node::Expression(substitute_expr_templates(expr, const_bindings)),
        Node::Let(let_stmt) => Node::Let(LetStmt {
            span: let_stmt.span,
            pattern: let_stmt.pattern.clone(),
            ty: let_stmt.ty.clone(),
            value: let_stmt
                .value
                .as_ref()
                .map(|expr| substitute_expr_templates(expr, const_bindings)),
            mutability: let_stmt.mutability,
            storage_class: let_stmt.storage_class,
            is_ghost: let_stmt.is_ghost,
        }),
        Node::Assignment(assign) => Node::Assignment(AssignmentStmt {
            span: assign.span,
            target: substitute_expr_templates(&assign.target, const_bindings),
            op: assign.op,
            value: substitute_expr_templates(&assign.value, const_bindings),
        }),
        Node::Return(ret) => Node::Return(ReturnStmt {
            span: ret.span,
            value: ret
                .value
                .as_ref()
                .map(|expr| substitute_expr_templates(expr, const_bindings)),
        }),
        Node::If(stmt) => Node::If(IfStmt {
            span: stmt.span,
            condition: substitute_expr_templates(&stmt.condition, const_bindings),
            then_block: substitute_block_templates(&stmt.then_block, const_bindings),
            elif_branches: stmt
                .elif_branches
                .iter()
                .map(|(cond, block)| {
                    (
                        substitute_expr_templates(cond, const_bindings),
                        substitute_block_templates(block, const_bindings),
                    )
                })
                .collect(),
            else_block: stmt
                .else_block
                .as_ref()
                .map(|block| substitute_block_templates(block, const_bindings)),
            let_pattern: stmt.let_pattern.clone(),
            is_suspend: stmt.is_suspend,
        }),
        Node::Match(stmt) => Node::Match(MatchStmt {
            span: stmt.span,
            subject: substitute_expr_templates(&stmt.subject, const_bindings),
            arms: stmt
                .arms
                .iter()
                .map(|arm| MatchArm {
                    span: arm.span,
                    pattern: arm.pattern.clone(),
                    guard: arm
                        .guard
                        .as_ref()
                        .map(|expr| substitute_expr_templates(expr, const_bindings)),
                    body: substitute_block_templates(&arm.body, const_bindings),
                })
                .collect(),
        }),
        Node::For(stmt) => Node::For(ForStmt {
            span: stmt.span,
            pattern: stmt.pattern.clone(),
            iterable: substitute_expr_templates(&stmt.iterable, const_bindings),
            body: substitute_block_templates(&stmt.body, const_bindings),
            is_suspend: stmt.is_suspend,
        }),
        Node::While(stmt) => Node::While(WhileStmt {
            span: stmt.span,
            condition: substitute_expr_templates(&stmt.condition, const_bindings),
            body: substitute_block_templates(&stmt.body, const_bindings),
            let_pattern: stmt.let_pattern.clone(),
            is_suspend: stmt.is_suspend,
        }),
        Node::Loop(stmt) => Node::Loop(LoopStmt {
            span: stmt.span,
            body: substitute_block_templates(&stmt.body, const_bindings),
        }),
        Node::Context(stmt) => Node::Context(ContextStmt {
            span: stmt.span,
            context: substitute_expr_templates(&stmt.context, const_bindings),
            body: substitute_block_templates(&stmt.body, const_bindings),
        }),
        Node::With(stmt) => Node::With(WithStmt {
            span: stmt.span,
            resource: substitute_expr_templates(&stmt.resource, const_bindings),
            name: stmt.name.clone(),
            body: substitute_block_templates(&stmt.body, const_bindings),
        }),
        Node::Break(_) | Node::Continue(_) => node.clone(),
        Node::Function(def) => {
            // Substitute templates in function name, body, and parameters
            let mut new_def = def.clone();
            // Substitute template in function name (e.g., "get_{i}" -> "get_0")
            // Also strip quotes if the name was quoted in the source (for templated names)
            let substituted_name = substitute_template_string(&def.name, const_bindings);
            new_def.name = if substituted_name.starts_with('"') && substituted_name.ends_with('"') && substituted_name.len() > 2 {
                substituted_name[1..substituted_name.len()-1].to_string()
            } else {
                substituted_name
            };
            new_def.body = substitute_block_templates(&def.body, const_bindings);
            // Also substitute in default parameter values
            new_def.params = def.params.iter().map(|param| {
                let mut new_param = param.clone();
                new_param.default = param.default
                    .as_ref()
                    .map(|expr| substitute_expr_templates(expr, const_bindings));
                new_param
            }).collect();
            Node::Function(new_def)
        }
        _ => node.clone(),
    }
}

fn substitute_expr_templates(
    expr: &Expr,
    const_bindings: &HashMap<String, String>,
) -> Expr {
    match expr {
        Expr::String(value) => Expr::String(substitute_template_string(value, const_bindings)),
        Expr::TypedString(value, suffix) => Expr::TypedString(
            substitute_template_string(value, const_bindings),
            suffix.clone(),
        ),
        Expr::FString(parts) => Expr::FString(
            parts
                .iter()
                .map(|part| match part {
                    FStringPart::Literal(text) => FStringPart::Literal(
                        substitute_template_string(text, const_bindings),
                    ),
                    FStringPart::Expr(expr_text) => FStringPart::Expr(expr_text.clone()),
                })
                .collect(),
        ),
        Expr::Binary { op, left, right } => Expr::Binary {
            op: op.clone(),
            left: Box::new(substitute_expr_templates(left, const_bindings)),
            right: Box::new(substitute_expr_templates(right, const_bindings)),
        },
        Expr::Unary { op, operand } => Expr::Unary {
            op: op.clone(),
            operand: Box::new(substitute_expr_templates(operand, const_bindings)),
        },
        Expr::Call { callee, args } => Expr::Call {
            callee: Box::new(substitute_expr_templates(callee, const_bindings)),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: substitute_expr_templates(&arg.value, const_bindings),
                })
                .collect(),
        },
        Expr::MethodCall {
            receiver,
            method,
            args,
        } => Expr::MethodCall {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: substitute_expr_templates(&arg.value, const_bindings),
                })
                .collect(),
        },
        Expr::FieldAccess { receiver, field } => Expr::FieldAccess {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            field: field.clone(),
        },
        Expr::Index { receiver, index } => Expr::Index {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            index: Box::new(substitute_expr_templates(index, const_bindings)),
        },
        Expr::TupleIndex { receiver, index } => Expr::TupleIndex {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            index: *index,
        },
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: Box::new(substitute_expr_templates(condition, const_bindings)),
            then_branch: Box::new(substitute_expr_templates(then_branch, const_bindings)),
            else_branch: else_branch
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::Match { subject, arms } => Expr::Match {
            subject: Box::new(substitute_expr_templates(subject, const_bindings)),
            arms: arms
                .iter()
                .map(|arm| MatchArm {
                    span: arm.span,
                    pattern: arm.pattern.clone(),
                    guard: arm
                        .guard
                        .as_ref()
                        .map(|expr| substitute_expr_templates(expr, const_bindings)),
                    body: substitute_block_templates(&arm.body, const_bindings),
                })
                .collect(),
        },
        Expr::Tuple(items) => Expr::Tuple(
            items
                .iter()
                .map(|item| substitute_expr_templates(item, const_bindings))
                .collect(),
        ),
        Expr::Array(items) => Expr::Array(
            items
                .iter()
                .map(|item| substitute_expr_templates(item, const_bindings))
                .collect(),
        ),
        Expr::VecLiteral(items) => Expr::VecLiteral(
            items
                .iter()
                .map(|item| substitute_expr_templates(item, const_bindings))
                .collect(),
        ),
        Expr::Dict(entries) => Expr::Dict(
            entries
                .iter()
                .map(|(k, v)| {
                    (
                        substitute_expr_templates(k, const_bindings),
                        substitute_expr_templates(v, const_bindings),
                    )
                })
                .collect(),
        ),
        Expr::ListComprehension {
            expr,
            pattern,
            iterable,
            condition,
        } => Expr::ListComprehension {
            expr: Box::new(substitute_expr_templates(expr, const_bindings)),
            pattern: pattern.clone(),
            iterable: Box::new(substitute_expr_templates(iterable, const_bindings)),
            condition: condition
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::DictComprehension {
            key,
            value,
            pattern,
            iterable,
            condition,
        } => Expr::DictComprehension {
            key: Box::new(substitute_expr_templates(key, const_bindings)),
            value: Box::new(substitute_expr_templates(value, const_bindings)),
            pattern: pattern.clone(),
            iterable: Box::new(substitute_expr_templates(iterable, const_bindings)),
            condition: condition
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::Slice {
            receiver,
            start,
            end,
            step,
        } => Expr::Slice {
            receiver: Box::new(substitute_expr_templates(receiver, const_bindings)),
            start: start
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            end: end
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            step: step
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
        },
        Expr::Spread(expr) => Expr::Spread(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::DictSpread(expr) => {
            Expr::DictSpread(Box::new(substitute_expr_templates(expr, const_bindings)))
        }
        Expr::StructInit { name, fields } => Expr::StructInit {
            name: name.clone(),
            fields: fields
                .iter()
                .map(|(field, expr)| {
                    (
                        field.clone(),
                        substitute_expr_templates(expr, const_bindings),
                    )
                })
                .collect(),
        },
        Expr::Spawn(expr) => Expr::Spawn(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::Await(expr) => Expr::Await(Box::new(substitute_expr_templates(expr, const_bindings))),
        Expr::Yield(expr) => {
            Expr::Yield(expr.as_ref().map(|e| Box::new(substitute_expr_templates(e, const_bindings))))
        }
        Expr::New { kind, expr } => Expr::New {
            kind: *kind,
            expr: Box::new(substitute_expr_templates(expr, const_bindings)),
        },
        Expr::Cast { expr, target_type } => Expr::Cast {
            expr: Box::new(substitute_expr_templates(expr, const_bindings)),
            target_type: target_type.clone(),
        },
        Expr::Range { start, end, bound } => Expr::Range {
            start: start
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            end: end
                .as_ref()
                .map(|expr| Box::new(substitute_expr_templates(expr, const_bindings))),
            bound: *bound,
        },
        Expr::FunctionalUpdate { target, method, args } => Expr::FunctionalUpdate {
            target: Box::new(substitute_expr_templates(target, const_bindings)),
            method: method.clone(),
            args: args
                .iter()
                .map(|arg| simple_parser::ast::Argument {
                    name: arg.name.clone(),
                    value: substitute_expr_templates(&arg.value, const_bindings),
                })
                .collect(),
        },
        Expr::MacroInvocation { name, args } => Expr::MacroInvocation {
            name: name.clone(),
            args: args
                .iter()
                .map(|arg| match arg {
                    MacroArg::Expr(expr) => {
                        MacroArg::Expr(substitute_expr_templates(expr, const_bindings))
                    }
                })
                .collect(),
        },
        Expr::Try(expr) => Expr::Try(Box::new(substitute_expr_templates(expr, const_bindings))),
        // Handle bare identifiers that match const parameters
        Expr::Identifier(name) => {
            if let Some(value) = const_bindings.get(name) {
                // Try to parse as integer first, then as string
                if let Ok(i) = value.parse::<i64>() {
                    Expr::Integer(i)
                } else {
                    // Keep as string literal if it's a string const
                    Expr::String(value.clone())
                }
            } else {
                expr.clone()
            }
        }
        _ => expr.clone(),
    }
}

fn substitute_template_string(
    input: &str,
    const_bindings: &HashMap<String, String>,
) -> String {
    let mut output = input.to_string();
    for (key, value) in const_bindings {
        let needle = format!("{{{}}}", key);
        if output.contains(&needle) {
            output = output.replace(&needle, value);
        }
    }
    output
}
