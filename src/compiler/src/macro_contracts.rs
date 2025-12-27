// src/compiler/src/macro_contracts.rs
//! Macro contract processing: intro, inject, and returns items
//!
//! This module implements symbol table integration for contract-first macros (#1303).
//! Macros can declare symbols they introduce (intro), code they inject (inject),
//! and their return type (returns) in a contract header, enabling IDE autocomplete
//! without macro expansion.

use std::collections::{HashMap, HashSet};

use simple_parser::ast::{
    Block, ClassDef, Expr, FunctionDef, MacroAnchor, MacroCodeKind, MacroConstRange,
    MacroContractItem, MacroDeclStub, MacroDef, MacroFieldStub, MacroFnStub, MacroInject,
    MacroInjectSpec, MacroIntro, MacroIntroDecl, MacroIntroKind, MacroIntroSpec, MacroParamSig,
    MacroReturns, MacroTarget, MacroTypeStub, MacroVarStub, Parameter, Type, Visibility,
    EnclosingTarget, Mutability,
};
use simple_parser::token::Span;

use crate::error::CompileError;
use crate::value::{Env, Value};
use crate::macro_validation::{
    extract_symbol_scope, validate_intro_no_shadowing, validate_macro_contract, SymbolScope
};

/// Result of processing macro contract items
#[derive(Debug, Default, Clone)]
pub struct MacroContractResult {
    /// Functions introduced by the macro (for enclosing scope)
    pub introduced_functions: HashMap<String, FunctionDef>,

    /// Classes introduced by the macro (for enclosing scope)
    pub introduced_classes: HashMap<String, ClassDef>,

    /// Type aliases introduced by the macro
    pub introduced_types: HashMap<String, Type>,

    /// Variables introduced at callsite block
    pub introduced_vars: Vec<(String, Type, bool)>, // (name, type, is_const)

    /// Code to inject at callsite (anchor -> blocks)
    pub injections: HashMap<MacroAnchor, Vec<Block>>,

    /// Mapping from emit label to inject anchor (for code extraction)
    pub inject_labels: HashMap<String, MacroAnchor>,

    /// Return type of the macro (if declared)
    pub return_type: Option<Type>,

    /// Return label (if declared)
    pub return_label: Option<String>,
}

/// Process all contract items in a macro definition
pub fn process_macro_contract(
    macro_def: &MacroDef,
    const_bindings: &HashMap<String, String>,
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
) -> Result<MacroContractResult, CompileError> {
    let mut result = MacroContractResult::default();

    // Extract current symbol scope for shadowing detection (#1304)
    let existing_symbols = extract_symbol_scope(env, functions, classes);
    let mut introduced_symbols = HashSet::new();

    // Perform comprehensive validation: type annotations, QIDENT bindings, shadowing (#1304)
    validate_macro_contract(&macro_def.contract, const_bindings, &existing_symbols)?;

    for item in &macro_def.contract {
        match item {
            MacroContractItem::Returns(returns) => {
                process_returns_item(returns, &mut result)?;
            }
            MacroContractItem::Intro(intro) => {
                process_intro_item(intro, const_bindings, env, &existing_symbols, &mut introduced_symbols, &mut result)?;
            }
            MacroContractItem::Inject(inject) => {
                process_inject_item(inject, &mut result)?;
            }
        }
    }

    Ok(result)
}

/// Process a returns contract item
fn process_returns_item(
    returns: &MacroReturns,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    result.return_type = Some(returns.ty.clone());
    result.return_label = returns.label.clone();
    Ok(())
}

/// Process an intro contract item
fn process_intro_item(
    intro: &MacroIntro,
    const_bindings: &HashMap<String, String>,
    env: &Env,
    existing_symbols: &SymbolScope,
    introduced_symbols: &mut HashSet<String>,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    process_intro_spec(&intro.spec, const_bindings, env, existing_symbols, introduced_symbols, result)
}

/// Process an intro spec (handles Decl, For, If recursively)
fn process_intro_spec(
    spec: &MacroIntroSpec,
    const_bindings: &HashMap<String, String>,
    env: &Env,
    existing_symbols: &SymbolScope,
    introduced_symbols: &mut HashSet<String>,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    match spec {
        MacroIntroSpec::Decl(decl) => {
            process_intro_decl(decl, const_bindings, existing_symbols, introduced_symbols, result)
        }
        MacroIntroSpec::For { name, range, body } => {
            // Const-eval the range and expand the body for each iteration
            let (start, end) = eval_const_range(range, const_bindings, env)?;

            for i in start..end {
                // Create new const bindings with loop variable
                let mut iter_bindings = const_bindings.clone();
                iter_bindings.insert(name.clone(), i.to_string());

                // Process each intro spec in the body
                for spec in body {
                    process_intro_spec(spec, &iter_bindings, env, existing_symbols, introduced_symbols, result)?;
                }
            }
            Ok(())
        }
        MacroIntroSpec::If { condition, then_body, else_body } => {
            // Const-eval the condition
            let cond_result = eval_const_condition(condition, const_bindings, env)?;

            // Process the appropriate branch
            let body = if cond_result { then_body } else { else_body };
            for spec in body {
                process_intro_spec(spec, const_bindings, env, existing_symbols, introduced_symbols, result)?;
            }
            Ok(())
        }
    }
}

/// Process a single intro declaration
fn process_intro_decl(
    decl: &MacroIntroDecl,
    const_bindings: &HashMap<String, String>,
    existing_symbols: &SymbolScope,
    introduced_symbols: &mut HashSet<String>,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    match &decl.target {
        MacroTarget::Enclosing(enclosing) => {
            match &decl.stub {
                MacroDeclStub::Fn(fn_stub) => {
                    let func_def = create_function_from_stub(fn_stub, const_bindings)?;

                    // Validate shadowing (#1304)
                    validate_intro_no_shadowing(&func_def.name, existing_symbols, introduced_symbols)?;
                    introduced_symbols.insert(func_def.name.clone());

                    result.introduced_functions.insert(func_def.name.clone(), func_def);
                }
                MacroDeclStub::Field(field_stub) => {
                    // Fields require a class context - will be handled when macro is in a class
                    // For now, store as pending
                    // TODO: Implement field introduction in enclosing class
                    let field_name = substitute_template(&field_stub.name, const_bindings);

                    // Validate shadowing for field names
                    validate_intro_no_shadowing(&field_name, existing_symbols, introduced_symbols)?;
                    introduced_symbols.insert(field_name);
                }
                MacroDeclStub::Type(type_stub) => {
                    let type_name = substitute_template(&type_stub.name, const_bindings);

                    // Validate shadowing for type names
                    validate_intro_no_shadowing(&type_name, existing_symbols, introduced_symbols)?;
                    introduced_symbols.insert(type_name.clone());

                    result.introduced_types.insert(type_name, Type::Simple("_".to_string()));
                }
                MacroDeclStub::Var(var_stub) => {
                    let var_name = substitute_template(&var_stub.name, const_bindings);

                    // Validate shadowing for variables
                    validate_intro_no_shadowing(&var_name, existing_symbols, introduced_symbols)?;
                    introduced_symbols.insert(var_name.clone());

                    let is_const = matches!(decl.kind, MacroIntroKind::Const);
                    result.introduced_vars.push((var_name, var_stub.ty.clone(), is_const));
                }
            }
        }
        MacroTarget::CallsiteBlock(anchor) => {
            // Callsite block introductions are handled differently
            // Variables introduced at callsite go into introduced_vars
            match &decl.stub {
                MacroDeclStub::Var(var_stub) => {
                    let var_name = substitute_template(&var_stub.name, const_bindings);

                    // Validate shadowing for callsite variables
                    validate_intro_no_shadowing(&var_name, existing_symbols, introduced_symbols)?;
                    introduced_symbols.insert(var_name.clone());

                    let is_const = matches!(decl.kind, MacroIntroKind::Const);
                    result.introduced_vars.push((var_name, var_stub.ty.clone(), is_const));
                }
                _ => {
                    return Err(CompileError::Semantic(
                        "Only var/const introductions are allowed at callsite block".to_string()
                    ));
                }
            }
        }
    }

    Ok(())
}

/// Process an inject contract item
fn process_inject_item(
    inject: &MacroInject,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    // Store the mapping from emit label to inject anchor
    // This allows macro expansion to know which emit blocks contain injection code
    result.inject_labels.insert(inject.label.clone(), inject.spec.anchor.clone());

    // Initialize the injection vector for this anchor if not present
    result.injections.entry(inject.spec.anchor.clone()).or_insert_with(Vec::new);

    Ok(())
}

/// Evaluate a const range expression
fn eval_const_range(
    range: &MacroConstRange,
    const_bindings: &HashMap<String, String>,
    env: &Env,
) -> Result<(i64, i64), CompileError> {
    let start = eval_const_int_expr(&range.start, const_bindings, env)?;
    let end = eval_const_int_expr(&range.end, const_bindings, env)?;

    if range.inclusive {
        Ok((start, end + 1))
    } else {
        Ok((start, end))
    }
}

/// Evaluate a const condition expression
fn eval_const_condition(
    expr: &Expr,
    const_bindings: &HashMap<String, String>,
    env: &Env,
) -> Result<bool, CompileError> {
    // For now, support simple boolean literals and comparisons
    match expr {
        Expr::Bool(b) => Ok(*b),
        Expr::Binary { op, left, right } => {
            // Support basic comparisons
            use simple_parser::ast::BinOp;
            match op {
                BinOp::Eq | BinOp::NotEq | BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
                    let left_val = eval_const_int_expr(left, const_bindings, env)?;
                    let right_val = eval_const_int_expr(right, const_bindings, env)?;

                    Ok(match op {
                        BinOp::Eq => left_val == right_val,
                        BinOp::NotEq => left_val != right_val,
                        BinOp::Lt => left_val < right_val,
                        BinOp::LtEq => left_val <= right_val,
                        BinOp::Gt => left_val > right_val,
                        BinOp::GtEq => left_val >= right_val,
                        _ => unreachable!(),
                    })
                }
                _ => Err(CompileError::Semantic(
                    "Only comparison operators are supported in macro if conditions".to_string()
                ))
            }
        }
        _ => Err(CompileError::Semantic(
            "Complex expressions not yet supported in macro if conditions".to_string()
        ))
    }
}

/// Evaluate a const integer expression
fn eval_const_int_expr(
    expr: &Expr,
    const_bindings: &HashMap<String, String>,
    env: &Env,
) -> Result<i64, CompileError> {
    match expr {
        Expr::Integer(i) => Ok(*i),
        Expr::Identifier(name) => {
            // Check const bindings first
            if let Some(value_str) = const_bindings.get(name) {
                value_str.parse::<i64>().map_err(|_| {
                    CompileError::Semantic(format!(
                        "Const binding '{}' is not an integer: {}",
                        name, value_str
                    ))
                })
            } else {
                Err(CompileError::Semantic(format!(
                    "Undefined const binding in macro range: {}",
                    name
                )))
            }
        }
        Expr::Binary { op, left, right } => {
            use simple_parser::ast::BinOp;
            let left_val = eval_const_int_expr(left, const_bindings, env)?;
            let right_val = eval_const_int_expr(right, const_bindings, env)?;

            Ok(match op {
                BinOp::Add => left_val + right_val,
                BinOp::Sub => left_val - right_val,
                BinOp::Mul => left_val * right_val,
                BinOp::Div => left_val / right_val,
                BinOp::Mod => left_val % right_val,
                _ => return Err(CompileError::Semantic(
                    "Only arithmetic operators are supported in macro const expressions".to_string()
                )),
            })
        }
        _ => Err(CompileError::Semantic(
            "Complex expressions not yet supported in macro const eval".to_string()
        ))
    }
}

/// Create a FunctionDef from a MacroFnStub
fn create_function_from_stub(
    stub: &MacroFnStub,
    const_bindings: &HashMap<String, String>,
) -> Result<FunctionDef, CompileError> {
    let name = substitute_template(&stub.name, const_bindings);

    let params = stub.params.iter().map(|p| {
        Parameter {
            span: Span::new(0, 0, 0, 0),
            name: p.name.clone(),
            ty: Some(p.ty.clone()),
            default: None,
            mutability: Mutability::Immutable,
            inject: false,
        }
    }).collect();

    Ok(FunctionDef {
        span: Span::new(0, 0, 0, 0),
        name,
        generic_params: vec![],
        params,
        return_type: stub.ret.clone(),
        where_clause: vec![],
        body: Block {
            span: Span::new(0, 0, 0, 0),
            statements: vec![],
        },
        visibility: Visibility::Private,
        effects: vec![],
        decorators: vec![],
        attributes: vec![],
        doc_comment: None,
        contract: None,
        is_abstract: false,
        bounds_block: None,
    })
}

/// Substitute template variables in a string (e.g., "{NAME}" -> "User")
fn substitute_template(template: &str, const_bindings: &HashMap<String, String>) -> String {
    let mut result = template.to_string();

    for (name, value) in const_bindings {
        let placeholder = format!("{{{}}}", name);
        result = result.replace(&placeholder, value);
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_substitute_template() {
        let mut bindings = HashMap::new();
        bindings.insert("NAME".to_string(), "User".to_string());
        bindings.insert("COUNT".to_string(), "42".to_string());

        assert_eq!(substitute_template("{NAME}Counter", &bindings), "UserCounter");
        assert_eq!(substitute_template("get_{NAME}_{COUNT}", &bindings), "get_User_42");
        assert_eq!(substitute_template("no_template", &bindings), "no_template");
    }

    #[test]
    fn test_eval_const_int_expr() {
        let mut bindings = HashMap::new();
        bindings.insert("N".to_string(), "10".to_string());

        let env = Env::new();

        // Test literal
        let expr = Expr::Integer(5);
        assert_eq!(eval_const_int_expr(&expr, &bindings, &env).unwrap(), 5);

        // Test identifier
        let expr = Expr::Identifier("N".to_string());
        assert_eq!(eval_const_int_expr(&expr, &bindings, &env).unwrap(), 10);
    }
}
