//! System Tests for Simple Language Compiler
//!
//! Test Level: System
//! Mock Policy: No mocks allowed
//! Coverage: Class/struct (100% required)
//! Coverage Data: Separate

use ctor::ctor;
use simple_mock_helper::{init_system_tests, validate_test_config};

#[ctor]
fn init() {
    init_system_tests!("simple_system");
}

mod abi_event_pattern_tests;
mod ast_enum_concurrency_tests;
mod backend_jit_lint_tests;
mod builtin_class_cross_tests;
mod cli_tests;
mod command_dispatch_tests;
mod compiler_enum_lint_tests;
mod contract_bitfield_tests;
mod core_tests;
mod coverage_extended_tests;
mod coverage_tests;
mod coverage_verification_tests;
mod execution_tests;
mod feature_tests_advanced;
mod feature_tests_basic;
mod hir_compilability_tests;
mod integration_extended_tests;
mod integration_tests;
mod jj_state_actor_tests;
mod lexer_parser_resolver_tests;
mod memory_effect_doctest_tests;
mod memory_tests;
mod mir_types_table_tests;
mod module_api_functional_tests;
mod package_format_tests;
mod parser_macro_loader_tests;
mod parser_token_type_tests;
mod public_api_coverage_tests;
mod runner_tests;
mod runtime_ffi_value_tests;
mod runtime_object_mono_tests;
mod runtime_parser_extended_tests;
mod simple_basic;
mod smf_linker_tests;
mod smf_project_coverage_tests;
mod smf_settlement_types_tests;
mod smf_symbol_lint_tests;
mod smf_tests;
mod struct_coverage_tests;
mod target_async_value_tests;
mod test_framework_docgen_tests;
mod type_unification_tests;
mod unit_arithmetic_lowering_tests;
mod value_effect_identifier_tests;

#[test]
fn validate_config() {
    validate_test_config().expect_pass();
}
