//! User-defined macro expansion
//!
//! Handles expansion of user-defined macros with const evaluation, hygiene,
//! and template substitution. Validates macro contracts and ordering.

use crate::value::{Control, Env, Value};
use crate::{CompileError, evaluate_expr, exec_block, exec_block_fn, exec_node};
use crate::macro_contracts::{process_macro_contract, MacroContractResult};
use crate::macro_validation::validate_macro_defined_before_use;
use simple_parser::ast::*;
use std::cell::RefCell;
use std::collections::HashMap;

use super::helpers::{build_macro_const_bindings};
use super::hygiene::{MacroHygieneContext, apply_macro_hygiene_block, apply_macro_hygiene_node};
use super::substitution::substitute_block_templates;

// Note: MACRO_DEFINITION_ORDER is defined in interpreter.rs
thread_local! {
    static MACRO_DEFINITION_ORDER: RefCell<HashMap<String, usize>> = RefCell::new(HashMap::new());
}

thread_local! {
    /// Accumulates symbols introduced by macro expansion
    /// These need to be registered by the caller after macro invocation
    static MACRO_INTRODUCED_SYMBOLS: RefCell<Option<MacroContractResult>> = RefCell::new(None);
}

/// Get and clear introduced symbols from last macro expansion
pub fn take_macro_introduced_symbols() -> Option<MacroContractResult> {
    MACRO_INTRODUCED_SYMBOLS.with(|cell| cell.borrow_mut().take())
}

/// Expand a user-defined macro with given arguments
pub(super) fn expand_user_macro(
    macro_def: &MacroDef,
    args: &[MacroArg],
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
    enums: &Enums,
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    // Validate ordering: macro must be defined before use (#1304)
    let definition_order = MACRO_DEFINITION_ORDER.with(|cell| cell.borrow().clone());
    validate_macro_defined_before_use(&macro_def.name, 0, &definition_order)?;

    let mut local_env = env.clone();
    let const_bindings = build_macro_const_bindings(macro_def, args, env, functions, classes, enums, impl_methods)?;
    let mut hygiene_ctx = MacroHygieneContext::new();

    // Process macro contracts to determine introduced symbols (#1303)
    // Also performs shadowing validation (#1304)
    let contract_result = process_macro_contract(macro_def, &const_bindings, env, functions, classes)?;

    // Store introduced symbols in thread-local for caller to register
    // This is necessary because symbol tables are immutable during evaluation
    MACRO_INTRODUCED_SYMBOLS.with(|cell| {
        *cell.borrow_mut() = Some(contract_result);
    });

    for (idx, param) in macro_def.params.iter().enumerate() {
        if let Some(MacroArg::Expr(e)) = args.get(idx) {
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
                let expanded_block = substitute_block_templates(block, &const_bindings);
                let hygienic_block = apply_macro_hygiene_block(&expanded_block, &mut hygiene_ctx, false);
                let (control, maybe_value) =
                    exec_block_fn(&hygienic_block, &mut local_env, functions, classes, enums, impl_methods)?;
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

    Ok(last_value)
}
