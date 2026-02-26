//! Common test utilities shared across integration tests

use simple_compiler::{di, hir, mir};
use simple_parser::Parser;

// ============================================================================
// Parsing and Lowering Helpers
// ============================================================================

/// Parse source code and lower to HIR
pub fn parse_and_lower(source: &str) -> hir::HirModule {
    let mut parser = Parser::new(source);
    let ast = parser.parse().expect("Failed to parse");
    hir::lower(&ast).expect("Failed to lower to HIR")
}

/// Parse DI TOML configuration
pub fn parse_di_toml(toml_str: &str) -> di::DiConfig {
    let toml_value: toml::Value = toml::from_str(toml_str).expect("Failed to parse TOML");
    di::parse_di_config(&toml_value)
        .expect("Failed to parse DI config")
        .expect("Should have DI config")
}

/// Lower HIR to MIR with optional DI config
pub fn lower_to_mir(
    hir_module: &hir::HirModule,
    di_config: Option<di::DiConfig>,
) -> Result<mir::MirModule, mir::MirLowerError> {
    let lowerer = mir::MirLowerer::new().with_di_config(di_config);
    lowerer.lower_module(hir_module)
}

/// Parse source, lower to HIR, and lower to MIR with DI config
pub fn parse_and_lower_with_di(source: &str, di_toml: &str) -> Result<mir::MirModule, mir::MirLowerError> {
    let hir_module = parse_and_lower(source);
    let di_config = parse_di_toml(di_toml);
    lower_to_mir(&hir_module, Some(di_config))
}

/// Create empty DI config
pub fn empty_di_config() -> di::DiConfig {
    di::DiConfig {
        mode: di::DiMode::Hybrid,
        profiles: std::collections::HashMap::new(),
        concurrent_backend: Default::default(),
    }
}

// ============================================================================
// Search Helpers
// ============================================================================

/// Find a function in HIR module by name
pub fn find_hir_function<'a>(module: &'a hir::HirModule, name: &str) -> Option<&'a hir::HirFunction> {
    module.functions.iter().find(|f| f.name == name)
}

/// Find a function in MIR module by name
pub fn find_mir_function<'a>(module: &'a mir::MirModule, name: &str) -> Option<&'a mir::MirFunction> {
    module.functions.iter().find(|f| f.name == name)
}

// ============================================================================
// Assertion Helpers
// ============================================================================

/// Assert that a function is marked as @inject in HIR
pub fn assert_inject(module: &hir::HirModule, function_name: &str) {
    let func =
        find_hir_function(module, function_name).unwrap_or_else(|| panic!("Function '{}' not found", function_name));
    assert!(func.inject, "Function '{}' should be marked as @inject", function_name);
}

/// Assert that MIR lowering fails with a message containing the expected text
pub fn assert_mir_error_contains(result: Result<mir::MirModule, mir::MirLowerError>, expected: &str) {
    match result {
        Ok(_) => panic!("Expected MIR lowering to fail, but it succeeded"),
        Err(e) => {
            let err_msg = format!("{:?}", e);
            assert!(
                err_msg.contains(expected),
                "Error message should contain '{}', but got: {}",
                expected,
                err_msg
            );
        }
    }
}

/// Assert that MIR lowering succeeds and module has functions
pub fn assert_mir_success(result: Result<mir::MirModule, mir::MirLowerError>) -> mir::MirModule {
    match result {
        Ok(module) => {
            assert!(!module.functions.is_empty(), "MIR module should have functions");
            module
        }
        Err(e) => panic!("Expected MIR lowering to succeed, but got error: {:?}", e),
    }
}
