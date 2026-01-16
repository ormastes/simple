pub mod api_scanner;
pub mod coverage;
pub mod coverage_extended;
pub mod fluent;
pub mod mock_policy;
pub mod test_check;

// Re-export commonly used items
pub use api_scanner::{generate_yaml, merge_with_existing, scan_directory, write_yaml, ScannedApi, ScannedType};
pub use coverage::{
    compute_class_coverage, load_llvm_cov_export, load_public_api_spec, parse_llvm_cov_export, parse_public_api_spec,
    print_class_coverage_table, ClassCoverage, CoverageSummary, LlvmCovExport, MethodCoverage, NeighborSpec,
    PublicApiSpec, PublicTypeSpec,
};
pub use coverage_extended::{
    print_coverage_summary, CoverageAnalyzer, CoverageType, ExtendedCoverageReport, ExtendedCoverageSummary,
    ExternalLibCoverage, FunctionCoverage, InterfaceCoverage, NeighborCoverage, TypeCoverage,
};
pub use fluent::{ArgMatcher, MethodSetup, MethodVerification, MockSetup, MockVerify, Spy, VerifyCount};
pub use mock_policy::{
    are_mocks_enabled, check_mock_use_from, get_allowed_patterns, init_mocks_for_only, init_mocks_for_only_default,
    init_mocks_for_system, is_policy_initialized, try_check_mock_use_from, MockCheckResult, DEFAULT_ENV_PATTERNS,
    DEFAULT_HAL_PATTERNS,
};
pub use test_check::{
    assert_mocks_allowed, assert_mocks_forbidden, assert_test_level, get_test_level, get_test_level_name,
    init_test_level, init_test_level_named, try_get_test_level, validate_test_config, TestCheckResult, TestLevel,
};
