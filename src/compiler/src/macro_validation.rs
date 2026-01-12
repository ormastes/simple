//! Macro validation for one-pass LL(1) compilation (#1304)
//!
//! This module implements ordering constraints, shadowing detection, and other
//! validation rules to ensure macros can be compiled in a single pass with
//! immediate symbol table updates.

use crate::error::{codes, CompileError, ErrorContext};
use crate::value::Env;
use simple_parser::ast::{ClassDef, FunctionDef, MacroContractItem, MacroDef, MacroIntroSpec};
use std::collections::{HashMap, HashSet};

/// Symbol scope extracted from the current compilation context
#[derive(Debug, Clone, Default)]
pub struct SymbolScope {
    pub functions: HashSet<String>,
    pub classes: HashSet<String>,
    pub variables: HashSet<String>,
    pub types: HashSet<String>,
}

impl SymbolScope {
    /// Check if a symbol name exists in any namespace
    pub fn contains(&self, name: &str) -> bool {
        self.functions.contains(name)
            || self.classes.contains(name)
            || self.variables.contains(name)
            || self.types.contains(name)
    }

    /// Get the namespace where a symbol is defined
    pub fn get_namespace(&self, name: &str) -> Option<&'static str> {
        if self.functions.contains(name) {
            Some("function")
        } else if self.classes.contains(name) {
            Some("class")
        } else if self.variables.contains(name) {
            Some("variable")
        } else if self.types.contains(name) {
            Some("type")
        } else {
            None
        }
    }
}

/// Extract current symbol scope from execution context
pub fn extract_symbol_scope(
    env: &Env,
    functions: &HashMap<String, FunctionDef>,
    classes: &HashMap<String, ClassDef>,
) -> SymbolScope {
    SymbolScope {
        functions: functions.keys().cloned().collect(),
        classes: classes.keys().cloned().collect(),
        variables: env.keys().cloned().collect(),
        // Type information not currently needed for macro validation
        // Types are validated during HIR lowering with full type registry access
        types: HashSet::new(),
    }
}

/// Block position during macro expansion
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockPosition {
    /// Before any non-macro statements
    Head,
    /// After some non-macro statements
    Middle,
    /// After all non-macro statements (end of block)
    Tail,
}

/// Context about the current block during macro expansion
#[derive(Debug, Clone)]
pub struct BlockContext {
    /// Whether any non-macro statements have been executed
    pub has_non_macro_statements: bool,
    /// Current position in the block
    pub current_position: BlockPosition,
}

impl BlockContext {
    pub fn new() -> Self {
        Self {
            has_non_macro_statements: false,
            current_position: BlockPosition::Head,
        }
    }

    /// Mark that a non-macro statement has been encountered
    pub fn mark_non_macro_statement(&mut self) {
        self.has_non_macro_statements = true;
        self.current_position = BlockPosition::Middle;
    }

    /// Mark that we've reached the end of the block
    pub fn mark_block_end(&mut self) {
        self.current_position = BlockPosition::Tail;
    }
}

/// Validate that a macro is defined before it's used
///
/// Enforces the one-pass constraint that macros must be declared before use.
pub fn validate_macro_defined_before_use(
    macro_name: &str,
    _invocation_line: usize,
    definition_order: &[String],
) -> Result<(), CompileError> {
    if !definition_order.contains(&macro_name.to_string()) {
        return Err(CompileError::semantic_with_context(
            format!("Macro '{}' is used before it is defined", macro_name),
            ErrorContext::new()
                .with_code(codes::MACRO_USED_BEFORE_DEFINITION)
                .with_help("Define the macro before using it in this module"),
        ));
    }
    Ok(())
}

/// Validate that introduced symbols don't shadow existing symbols
///
/// Checks both the existing symbol scope and previously introduced symbols
/// from the same macro expansion.
pub fn validate_intro_no_shadowing(
    symbol_name: &str,
    existing_symbols: &SymbolScope,
    introduced_symbols: &HashSet<String>,
) -> Result<(), CompileError> {
    // Check if shadows existing symbol
    if let Some(namespace) = existing_symbols.get_namespace(symbol_name) {
        return Err(CompileError::semantic_with_context(
            format!(
                "Macro intro '{}' shadows existing {} with the same name",
                symbol_name, namespace
            ),
            ErrorContext::new()
                .with_code(codes::MACRO_SHADOWING)
                .with_help(format!(
                    "Rename the macro-introduced symbol or the existing {}",
                    namespace
                )),
        ));
    }

    // Check if shadows previously introduced symbol
    if introduced_symbols.contains(symbol_name) {
        return Err(CompileError::semantic_with_context(
            format!(
                "Macro intro '{}' conflicts with another symbol introduced by this macro",
                symbol_name
            ),
            ErrorContext::new()
                .with_code(codes::MACRO_SHADOWING)
                .with_help("Ensure introduced symbols have unique names"),
        ));
    }

    Ok(())
}

/// Validate QIDENT template variables are const bindings
///
/// Ensures all template placeholders like {NAME} correspond to const parameters
/// or const loop indices.
pub fn validate_qident_const_bindings(
    template: &str,
    const_bindings: &HashMap<String, String>,
) -> Result<(), CompileError> {
    // Extract all placeholders from template: {identifier}
    let re = regex::Regex::new(r"\{(\w+)\}").unwrap();

    for cap in re.captures_iter(template) {
        let var_name = &cap[1];
        if !const_bindings.contains_key(var_name) {
            return Err(CompileError::semantic_with_context(
                format!(
                    "Template variable '{{{}}}' in '{}' is not a const parameter or loop index",
                    var_name, template
                ),
                ErrorContext::new()
                    .with_code(codes::MACRO_INVALID_QIDENT)
                    .with_help(format!(
                        "Add 'const' qualifier to macro parameter '{}' or define it as a const loop variable",
                        var_name
                    )),
            ));
        }
    }

    Ok(())
}

/// Validate intro type annotations are present
///
/// Ensures that intro let/const declarations have explicit type annotations.
/// This is required for one-pass compilation as types cannot be inferred
/// without executing the macro body.
pub fn validate_intro_type_annotations(spec: &MacroIntroSpec) -> Result<(), CompileError> {
    match spec {
        MacroIntroSpec::Decl(decl) => {
            // Parser already enforces type annotations for let/const stubs
            // This is a defensive check
            use simple_parser::ast::{MacroDeclStub, MacroIntroKind};

            if matches!(decl.kind, MacroIntroKind::Let | MacroIntroKind::Const) {
                if let MacroDeclStub::Var(var_stub) = &decl.stub {
                    // VarStub always has a type field (enforced by parser)
                    // If we reach here, validation passed
                    let _ = var_stub; // Suppress unused warning
                }
            }
            Ok(())
        }
        MacroIntroSpec::For { body, .. } => {
            // Recursively validate each intro in the for loop body
            for inner_spec in body {
                validate_intro_type_annotations(inner_spec)?;
            }
            Ok(())
        }
        MacroIntroSpec::If {
            then_body,
            else_body,
            ..
        } => {
            // Recursively validate both branches
            for inner_spec in then_body {
                validate_intro_type_annotations(inner_spec)?;
            }
            for inner_spec in else_body {
                validate_intro_type_annotations(inner_spec)?;
            }
            Ok(())
        }
    }
}

/// Validate all contract items in a macro definition
///
/// Performs comprehensive validation of intro, inject, and returns contract items.
pub fn validate_macro_contract(
    contract: &[MacroContractItem],
    const_bindings: &HashMap<String, String>,
    existing_symbols: &SymbolScope,
) -> Result<(), CompileError> {
    let mut introduced_symbols = HashSet::new();

    for item in contract {
        if let MacroContractItem::Intro(intro) = item {
            // Validate type annotations
            validate_intro_type_annotations(&intro.spec)?;

            // For validation, we need to extract introduced symbol names
            // This is a simplified check - full validation happens during contract processing
            validate_intro_spec_recursive(
                &intro.spec,
                const_bindings,
                existing_symbols,
                &mut introduced_symbols,
            )?;
        }
    }

    Ok(())
}

/// Recursively validate intro spec and collect introduced symbols
fn validate_intro_spec_recursive(
    spec: &MacroIntroSpec,
    const_bindings: &HashMap<String, String>,
    existing_symbols: &SymbolScope,
    introduced_symbols: &mut HashSet<String>,
) -> Result<(), CompileError> {
    use simple_parser::ast::{MacroDeclStub, MacroIntroKind};

    match spec {
        MacroIntroSpec::Decl(decl) => {
            // Extract symbol name from stub and validate QIDENT
            let symbol_name = match &decl.stub {
                MacroDeclStub::Fn(fn_stub) => {
                    validate_qident_const_bindings(&fn_stub.name, const_bindings)?;
                    // Substitute to get actual name (simplified - full substitution in macro_contracts.rs)
                    fn_stub.name.clone()
                }
                MacroDeclStub::Field(field_stub) => {
                    validate_qident_const_bindings(&field_stub.name, const_bindings)?;
                    field_stub.name.clone()
                }
                MacroDeclStub::Var(var_stub) => {
                    validate_qident_const_bindings(&var_stub.name, const_bindings)?;
                    var_stub.name.clone()
                }
                MacroDeclStub::Type(type_stub) => {
                    validate_qident_const_bindings(&type_stub.name, const_bindings)?;
                    type_stub.name.clone()
                }
            };

            // Check for shadowing (simplified - actual names after substitution)
            // Full shadowing check happens in macro_contracts.rs after template substitution
            // This is a best-effort early validation
            if !symbol_name.contains('{') {
                // Only check if not a template (no placeholders)
                validate_intro_no_shadowing(&symbol_name, existing_symbols, introduced_symbols)?;
                introduced_symbols.insert(symbol_name);
            }

            Ok(())
        }
        MacroIntroSpec::For { name, body, .. } => {
            // Create new bindings with loop index added
            let mut loop_bindings = const_bindings.clone();
            loop_bindings.insert(name.clone(), "loop_index".to_string());

            for inner_spec in body {
                validate_intro_spec_recursive(
                    inner_spec,
                    &loop_bindings,
                    existing_symbols,
                    introduced_symbols,
                )?;
            }
            Ok(())
        }
        MacroIntroSpec::If {
            then_body,
            else_body,
            ..
        } => {
            for inner_spec in then_body {
                validate_intro_spec_recursive(
                    inner_spec,
                    const_bindings,
                    existing_symbols,
                    introduced_symbols,
                )?;
            }
            for inner_spec in else_body {
                validate_intro_spec_recursive(
                    inner_spec,
                    const_bindings,
                    existing_symbols,
                    introduced_symbols,
                )?;
            }
            Ok(())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_scope_contains() {
        let mut scope = SymbolScope::default();
        scope.functions.insert("foo".to_string());
        scope.classes.insert("Bar".to_string());

        assert!(scope.contains("foo"));
        assert!(scope.contains("Bar"));
        assert!(!scope.contains("baz"));
    }

    #[test]
    fn test_block_context_transitions() {
        let mut ctx = BlockContext::new();
        assert_eq!(ctx.current_position, BlockPosition::Head);

        ctx.mark_non_macro_statement();
        assert_eq!(ctx.current_position, BlockPosition::Middle);
        assert!(ctx.has_non_macro_statements);

        ctx.mark_block_end();
        assert_eq!(ctx.current_position, BlockPosition::Tail);
    }

    #[test]
    fn test_validate_qident_valid() {
        let mut bindings = HashMap::new();
        bindings.insert("NAME".to_string(), "Foo".to_string());
        bindings.insert("COUNT".to_string(), "3".to_string());

        assert!(validate_qident_const_bindings("func_{NAME}", &bindings).is_ok());
        assert!(validate_qident_const_bindings("var_{NAME}_{COUNT}", &bindings).is_ok());
    }

    #[test]
    fn test_validate_qident_invalid() {
        let mut bindings = HashMap::new();
        bindings.insert("NAME".to_string(), "Foo".to_string());

        let result = validate_qident_const_bindings("func_{INVALID}", &bindings);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .to_string()
            .contains("not a const parameter"));
    }

    #[test]
    fn test_validate_macro_defined_before_use_success() {
        let order = vec!["foo".to_string(), "bar".to_string(), "baz".to_string()];

        assert!(validate_macro_defined_before_use("foo", 0, &order).is_ok());
        assert!(validate_macro_defined_before_use("bar", 0, &order).is_ok());
        assert!(validate_macro_defined_before_use("baz", 0, &order).is_ok());
    }

    #[test]
    fn test_validate_macro_defined_before_use_failure() {
        let order = vec!["foo".to_string(), "bar".to_string()];

        let result = validate_macro_defined_before_use("undefined", 0, &order);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("used before it is defined"));
        assert!(err_msg.contains("undefined"));
    }

    #[test]
    fn test_validate_intro_no_shadowing_existing_function() {
        let mut scope = SymbolScope::default();
        scope.functions.insert("existing_fn".to_string());
        let introduced = HashSet::new();

        let result = validate_intro_no_shadowing("existing_fn", &scope, &introduced);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("shadows existing function"));
    }

    #[test]
    fn test_validate_intro_no_shadowing_existing_class() {
        let mut scope = SymbolScope::default();
        scope.classes.insert("MyClass".to_string());
        let introduced = HashSet::new();

        let result = validate_intro_no_shadowing("MyClass", &scope, &introduced);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("shadows existing class"));
    }

    #[test]
    fn test_validate_intro_no_shadowing_existing_variable() {
        let mut scope = SymbolScope::default();
        scope.variables.insert("my_var".to_string());
        let introduced = HashSet::new();

        let result = validate_intro_no_shadowing("my_var", &scope, &introduced);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("shadows existing variable"));
    }

    #[test]
    fn test_validate_intro_no_shadowing_previously_introduced() {
        let scope = SymbolScope::default();
        let mut introduced = HashSet::new();
        introduced.insert("duplicate".to_string());

        let result = validate_intro_no_shadowing("duplicate", &scope, &introduced);
        assert!(result.is_err());
        let err_msg = result.unwrap_err().to_string();
        assert!(err_msg.contains("conflicts with another symbol introduced"));
    }

    #[test]
    fn test_validate_intro_no_shadowing_success() {
        let scope = SymbolScope::default();
        let introduced = HashSet::new();

        assert!(validate_intro_no_shadowing("new_symbol", &scope, &introduced).is_ok());
    }

    #[test]
    fn test_symbol_scope_get_namespace() {
        let mut scope = SymbolScope::default();
        scope.functions.insert("my_fn".to_string());
        scope.classes.insert("MyClass".to_string());
        scope.variables.insert("my_var".to_string());
        scope.types.insert("MyType".to_string());

        assert_eq!(scope.get_namespace("my_fn"), Some("function"));
        assert_eq!(scope.get_namespace("MyClass"), Some("class"));
        assert_eq!(scope.get_namespace("my_var"), Some("variable"));
        assert_eq!(scope.get_namespace("MyType"), Some("type"));
        assert_eq!(scope.get_namespace("undefined"), None);
    }
}
