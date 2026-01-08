use crate::error::CompileError;
use crate::interpreter::{evaluate_expr, exec_block, exec_block_fn, exec_node, Control, Enums, ImplMethods};
use crate::macro_contracts::{process_macro_contract, MacroContractResult};
use crate::macro_validation::validate_macro_defined_before_use;
use crate::value::{Env, Value};
use simple_parser::ast::{ClassDef, FunctionDef, MacroAnchor, MacroArg, MacroContractItem, MacroDef, MacroStmt};
use std::collections::{HashMap, HashSet};

use super::helpers::build_macro_const_bindings;
use super::hygiene::{apply_macro_hygiene_block, apply_macro_hygiene_node, MacroHygieneContext};
use super::state::{
    is_macro_trace_enabled, macro_trace, pop_macro_depth, push_macro_depth,
    queue_tail_injection, store_macro_introduced_symbols,
};
use super::substitution::substitute_block_templates;

/// Expand a user-defined macro with given arguments
pub(super) fn expand_user_macro(
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
    let definition_order = crate::interpreter::MACRO_DEFINITION_ORDER.with(|cell| cell.borrow().clone());
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
                "Variadic parameter must be the last parameter".to_string(),
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

    let return_label = macro_def.contract.iter().find_map(|item| match item {
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
                let functions_before: HashSet<String> = local_env
                    .iter()
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
                                contract_result
                                    .introduced_functions
                                    .insert(original_name, real_func);
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
                                    contract_result
                                        .introduced_functions
                                        .insert(public_name.clone(), real_func);
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
                contract_result
                    .introduced_functions
                    .insert(original_name, (**def).clone());
            } else {
                // Check if the env key (which might also be gensym'd) matches an intro stub
                let original_key = strip_gensym_suffix(name);
                if contract_result.introduced_functions.contains_key(&original_key) {
                    // Replace stub with real function, using original key as the public name
                    let mut real_func = (**def).clone();
                    real_func.name = original_key.clone();
                    contract_result
                        .introduced_functions
                        .insert(original_key, real_func);
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
