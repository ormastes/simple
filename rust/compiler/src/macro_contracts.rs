// src/compiler/src/macro_contracts.rs
//! Macro contract processing: intro, inject, and returns items
//!
//! This module implements symbol table integration for contract-first macros (#1303).
//! Macros can declare symbols they introduce (intro), code they inject (inject),
//! and their return type (returns) in a contract header, enabling IDE autocomplete
//! without macro expansion.

use std::collections::{HashMap, HashSet};

use simple_parser::ast::{
    Block, ClassDef, EnclosingTarget, Expr, Field, FunctionDef, MacroAnchor, MacroCodeKind, MacroConstRange,
    MacroContractItem, MacroDeclStub, MacroDef, MacroFieldStub, MacroFnStub, MacroInject, MacroInjectSpec, MacroIntro,
    MacroIntroDecl, MacroIntroKind, MacroIntroSpec, MacroParamSig, MacroReturns, MacroTarget, MacroTypeStub,
    MacroVarStub, Mutability, Parameter, Type, Visibility,
};
use simple_parser::token::Span;

use crate::error::{codes, CompileError, ErrorContext};
use crate::macro_validation::{extract_symbol_scope, validate_intro_no_shadowing, validate_macro_contract, SymbolScope};
use crate::value::{Env, Value};

/// Result of processing macro contract items
#[derive(Debug, Default, Clone)]
pub struct MacroContractResult {
    /// Functions introduced by the macro (for enclosing scope)
    pub introduced_functions: HashMap<String, FunctionDef>,

    /// Classes introduced by the macro (for enclosing scope)
    pub introduced_classes: HashMap<String, ClassDef>,

    /// Type aliases introduced by the macro
    pub introduced_types: HashMap<String, Type>,

    /// Fields introduced by the macro (for enclosing class)
    pub introduced_fields: Vec<Field>,

    /// Variables introduced at callsite block
    pub introduced_vars: Vec<(String, Type, bool)>, // (name, type, is_const)

    /// Code to inject at callsite (anchor -> blocks)
    pub injections: HashMap<MacroAnchor, Vec<Block>>,

    /// Mapping from emit label to inject anchor (for code extraction)
    pub inject_labels: HashMap<String, MacroAnchor>,

    /// Mapping from intro label to expected public function name
    /// Used to rename functions from emit blocks to their public names
    pub intro_function_labels: HashMap<String, String>,

    /// Return type of the macro (if declared)
    pub return_type: Option<Type>,

    /// Return label (if declared)
    pub return_label: Option<String>,
}

/// Process all contract items in a macro definition
pub fn process_macro_contract(
    macro_def: &MacroDef,
    const_bindings: &HashMap<String, String>,
    env: &mut Env,
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
                process_intro_item(
                    intro,
                    const_bindings,
                    env,
                    &existing_symbols,
                    &mut introduced_symbols,
                    &mut result,
                )?;
            }
            MacroContractItem::Inject(inject) => {
                process_inject_item(inject, &mut result)?;
            }
        }
    }

    Ok(result)
}

/// Process a returns contract item
fn process_returns_item(returns: &MacroReturns, result: &mut MacroContractResult) -> Result<(), CompileError> {
    result.return_type = Some(returns.ty.clone());
    result.return_label = returns.label.clone();
    Ok(())
}

/// Process an intro contract item
fn process_intro_item(
    intro: &MacroIntro,
    const_bindings: &HashMap<String, String>,
    env: &mut Env,
    existing_symbols: &SymbolScope,
    introduced_symbols: &mut HashSet<String>,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    // Pass the intro label through to track emit label -> function name mapping
    process_intro_spec(
        &intro.spec,
        const_bindings,
        env,
        existing_symbols,
        introduced_symbols,
        &intro.label,
        result,
    )
}

/// Process an intro spec (handles Decl, For, If recursively)
fn process_intro_spec(
    spec: &MacroIntroSpec,
    const_bindings: &HashMap<String, String>,
    env: &mut Env,
    existing_symbols: &SymbolScope,
    introduced_symbols: &mut HashSet<String>,
    intro_label: &str,
    result: &mut MacroContractResult,
) -> Result<(), CompileError> {
    match spec {
        MacroIntroSpec::Decl(decl) => process_intro_decl(
            decl,
            const_bindings,
            existing_symbols,
            introduced_symbols,
            intro_label,
            result,
        ),
        MacroIntroSpec::For { name, range, body } => {
            // Const-eval the range and expand the body for each iteration
            let (start, end) = eval_const_range(range, const_bindings, env)?;

            for i in start..end {
                // Create new const bindings with loop variable
                let mut iter_bindings = const_bindings.clone();
                iter_bindings.insert(name.clone(), i.to_string());

                // Process each intro spec in the body
                for spec in body {
                    process_intro_spec(
                        spec,
                        &iter_bindings,
                        env,
                        existing_symbols,
                        introduced_symbols,
                        intro_label,
                        result,
                    )?;
                }
            }
            Ok(())
        }
        MacroIntroSpec::If {
            condition,
            then_body,
            else_body,
        } => {
            // Const-eval the condition
            let cond_result = eval_const_condition(condition, const_bindings, env)?;

            // Process the appropriate branch
            let body = if cond_result { then_body } else { else_body };
            for spec in body {
                process_intro_spec(
                    spec,
                    const_bindings,
                    env,
                    existing_symbols,
                    introduced_symbols,
                    intro_label,
                    result,
                )?;
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
    intro_label: &str,
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

                    // Record the mapping from intro label to public function name
                    // This allows functions in emit blocks to be registered with the correct public name
                    result
                        .intro_function_labels
                        .insert(intro_label.to_string(), func_def.name.clone());

                    result.introduced_functions.insert(func_def.name.clone(), func_def);
                }
                MacroDeclStub::Field(field_stub) => {
                    let field = create_field_from_stub(field_stub, const_bindings)?;

                    // Validate shadowing for field names
                    validate_intro_no_shadowing(&field.name, existing_symbols, introduced_symbols)?;
                    introduced_symbols.insert(field.name.clone());

                    result.introduced_fields.push(field);
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
                    let ctx = ErrorContext::new()
                        .with_code(codes::UNSUPPORTED_FEATURE)
                        .with_help("Only variable and constant introductions are supported at callsite block");
                    return Err(CompileError::semantic_with_context(
                        "Only var/const introductions are allowed at callsite block".to_string(),
                        ctx,
                    ));
                }
            }
        }
    }

    Ok(())
}

/// Process an inject contract item
fn process_inject_item(inject: &MacroInject, result: &mut MacroContractResult) -> Result<(), CompileError> {
    // Store the mapping from emit label to inject anchor
    // This allows macro expansion to know which emit blocks contain injection code
    result
        .inject_labels
        .insert(inject.label.clone(), inject.spec.anchor.clone());

    // Initialize the injection vector for this anchor if not present
    result
        .injections
        .entry(inject.spec.anchor.clone())
        .or_insert_with(Vec::new);

    Ok(())
}

/// Evaluate a const range expression
fn eval_const_range(
    range: &MacroConstRange,
    const_bindings: &HashMap<String, String>,
    env: &mut Env,
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
    env: &mut Env,
) -> Result<bool, CompileError> {
    // Support boolean literals, identifiers (const params), and comparisons
    match expr {
        Expr::Bool(b) => Ok(*b),
        Expr::Identifier(name) => {
            // Check const bindings for boolean parameter
            if let Some(value_str) = const_bindings.get(name) {
                value_str
                    .parse::<bool>()
                    .map_err(|_| crate::error::factory::const_binding_wrong_type(name, "a boolean", value_str))
            } else {
                Err(crate::error::factory::const_binding_not_found(name))
            }
        }
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
                _ => {
                    let ctx = ErrorContext::new().with_code(codes::INVALID_OPERATION).with_help(
                        "Only comparison operators (==, !=, <, <=, >, >=) are supported in macro if conditions",
                    );
                    Err(CompileError::semantic_with_context(
                        "Only comparison operators are supported in macro if conditions".to_string(),
                        ctx,
                    ))
                }
            }
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("Only boolean literals, identifiers (const params), and comparison expressions are supported in macro if conditions");
            Err(CompileError::semantic_with_context(
                "Complex expressions not yet supported in macro if conditions".to_string(),
                ctx,
            ))
        }
    }
}

/// Evaluate a const integer expression
fn eval_const_int_expr(expr: &Expr, const_bindings: &HashMap<String, String>, env: &Env) -> Result<i64, CompileError> {
    match expr {
        Expr::Integer(i) => Ok(*i),
        Expr::Identifier(name) => {
            // Check const bindings first
            if let Some(value_str) = const_bindings.get(name) {
                value_str
                    .parse::<i64>()
                    .map_err(|_| crate::error::factory::const_binding_wrong_type(name, "integer", value_str))
            } else {
                Err(crate::error::factory::const_binding_not_found(name))
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
                _ => {
                    let ctx = ErrorContext::new().with_code(codes::INVALID_OPERATION).with_help(
                        "Only arithmetic operators (+, -, *, /, %) are supported in macro const expressions",
                    );
                    return Err(CompileError::semantic_with_context(
                        "Only arithmetic operators are supported in macro const expressions".to_string(),
                        ctx,
                    ));
                }
            })
        }
        _ => {
            let ctx = ErrorContext::new()
                .with_code(codes::UNSUPPORTED_FEATURE)
                .with_help("Only integer literals, identifiers (const params), and binary arithmetic expressions are supported in macro const evaluation");
            Err(CompileError::semantic_with_context(
                "Complex expressions not yet supported in macro const eval".to_string(),
                ctx,
            ))
        }
    }
}

/// Create a FunctionDef from a MacroFnStub
fn create_function_from_stub(
    stub: &MacroFnStub,
    const_bindings: &HashMap<String, String>,
) -> Result<FunctionDef, CompileError> {
    let name = substitute_template(&stub.name, const_bindings);

    let params = stub
        .params
        .iter()
        .map(|p| Parameter {
            span: Span::new(0, 0, 0, 0),
            name: p.name.clone(),
            ty: Some(p.ty.clone()),
            default: None,
            mutability: Mutability::Immutable,
            inject: false,
            variadic: false,
            call_site_label: None,
        })
        .collect();

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
        is_sync: false,
        is_static: false,
        is_me_method: false,
        is_generator: false,
        bounds_block: None,
        return_constraint: None,
        is_generic_template: false,
        specialization_of: None,
        type_bindings: HashMap::new(),
    })
}

/// Create a Field from a MacroFieldStub
fn create_field_from_stub(
    stub: &MacroFieldStub,
    const_bindings: &HashMap<String, String>,
) -> Result<Field, CompileError> {
    let name = substitute_template(&stub.name, const_bindings);

    Ok(Field {
        span: Span::new(0, 0, 0, 0),
        name,
        ty: stub.ty.clone(),
        default: None,
        mutability: Mutability::Mutable,
        visibility: Visibility::Private,
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
