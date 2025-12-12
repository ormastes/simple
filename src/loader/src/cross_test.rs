//! Cross-platform testing infrastructure.
//!
//! This module provides utilities for testing code generation and loading
//! across different target architectures without requiring actual hardware.

use simple_common::target::{Target, TargetArch, TargetOS, TargetConfig};

use crate::smf::header::{SmfHeader, Arch, Platform};
use crate::smf::settlement::SettlementHeader;

/// Test fixture for a specific target architecture.
///
/// Provides mock headers and configuration for testing architecture-specific
/// code paths without actual cross-compilation.
#[derive(Debug, Clone)]
pub struct TargetFixture {
    /// Target specification.
    pub target: Target,
    /// Target configuration.
    pub config: TargetConfig,
}

impl TargetFixture {
    /// Create a fixture for the given target.
    pub fn new(target: Target) -> Self {
        Self {
            target,
            config: target.config(),
        }
    }

    /// Create a fixture for x86_64 Linux.
    pub fn x86_64_linux() -> Self {
        Self::new(Target::new(TargetArch::X86_64, TargetOS::Linux))
    }

    /// Create a fixture for aarch64 Linux.
    pub fn aarch64_linux() -> Self {
        Self::new(Target::new(TargetArch::Aarch64, TargetOS::Linux))
    }

    /// Create a fixture for x86_64 Windows.
    pub fn x86_64_windows() -> Self {
        Self::new(Target::new(TargetArch::X86_64, TargetOS::Windows))
    }

    /// Create a fixture for aarch64 macOS.
    pub fn aarch64_macos() -> Self {
        Self::new(Target::new(TargetArch::Aarch64, TargetOS::MacOS))
    }

    /// Create a fixture for RISC-V 64 Linux.
    pub fn riscv64_linux() -> Self {
        Self::new(Target::new(TargetArch::Riscv64, TargetOS::Linux))
    }

    /// Create fixtures for all supported 64-bit targets.
    pub fn all_64bit() -> Vec<Self> {
        vec![
            Self::x86_64_linux(),
            Self::x86_64_windows(),
            Self::aarch64_linux(),
            Self::aarch64_macos(),
            Self::riscv64_linux(),
        ]
    }

    /// Create a mock SMF header for this target.
    pub fn mock_smf_header(&self) -> SmfHeader {
        SmfHeader::new_for_target(self.target.arch, self.target.os)
    }

    /// Create a mock settlement header for this target.
    ///
    /// Note: SettlementHeader only contains arch, not platform.
    pub fn mock_settlement_header(&self) -> SettlementHeader {
        let mut header = SettlementHeader::default();
        header.magic = crate::smf::settlement::SSMF_MAGIC;
        header.version = 1;
        header.arch = Arch::from_target_arch(self.target.arch) as u8;
        // SettlementHeader doesn't have platform field - only arch
        header
    }

    /// Check if this target is the host target.
    pub fn is_host(&self) -> bool {
        self.target == Target::host()
    }

    /// Check if code for this target can be executed on the host.
    pub fn can_execute(&self) -> bool {
        self.is_host()
    }
}

/// Test matrix for cross-platform testing.
///
/// Generates test cases for multiple target combinations.
pub struct TestMatrix {
    /// Targets to test.
    targets: Vec<Target>,
    /// Operating systems to test.
    operating_systems: Vec<TargetOS>,
}

impl TestMatrix {
    /// Create a new test matrix with default targets.
    pub fn new() -> Self {
        Self {
            targets: vec![
                Target::new(TargetArch::X86_64, TargetOS::Linux),
                Target::new(TargetArch::Aarch64, TargetOS::Linux),
                Target::new(TargetArch::X86_64, TargetOS::Windows),
                Target::new(TargetArch::Aarch64, TargetOS::MacOS),
            ],
            operating_systems: vec![
                TargetOS::Linux,
                TargetOS::Windows,
                TargetOS::MacOS,
            ],
        }
    }

    /// Create a minimal test matrix (host only).
    pub fn minimal() -> Self {
        Self {
            targets: vec![Target::host()],
            operating_systems: vec![TargetOS::host()],
        }
    }

    /// Create a comprehensive test matrix (all combinations).
    pub fn comprehensive() -> Self {
        let arches = [
            TargetArch::X86_64,
            TargetArch::Aarch64,
            TargetArch::Riscv64,
        ];
        let oses = [
            TargetOS::Linux,
            TargetOS::Windows,
            TargetOS::MacOS,
        ];

        let mut targets = Vec::new();
        for arch in arches {
            for os in oses {
                targets.push(Target::new(arch, os));
            }
        }

        Self {
            targets,
            operating_systems: oses.to_vec(),
        }
    }

    /// Add a target to the matrix.
    pub fn with_target(mut self, target: Target) -> Self {
        if !self.targets.contains(&target) {
            self.targets.push(target);
        }
        self
    }

    /// Add an OS to test.
    pub fn with_os(mut self, os: TargetOS) -> Self {
        if !self.operating_systems.contains(&os) {
            self.operating_systems.push(os);
        }
        self
    }

    /// Get all targets in the matrix.
    pub fn targets(&self) -> &[Target] {
        &self.targets
    }

    /// Get all operating systems in the matrix.
    pub fn operating_systems(&self) -> &[TargetOS] {
        &self.operating_systems
    }

    /// Generate fixtures for all targets.
    pub fn fixtures(&self) -> Vec<TargetFixture> {
        self.targets.iter().map(|&t| TargetFixture::new(t)).collect()
    }

    /// Iterate over target/OS combinations for testing.
    pub fn iter(&self) -> impl Iterator<Item = Target> + '_ {
        self.targets.iter().copied()
    }
}

impl Default for TestMatrix {
    fn default() -> Self {
        Self::new()
    }
}

/// Helper macro for generating cross-platform tests.
///
/// This macro generates a test for each target in the fixture list.
#[macro_export]
macro_rules! cross_platform_test {
    ($test_name:ident, $fixture:ident, $body:block) => {
        #[test]
        fn $test_name() {
            use $crate::cross_test::TargetFixture;

            for $fixture in TargetFixture::all_64bit() {
                $body
            }
        }
    };
}

/// Test result aggregator for cross-platform tests.
#[derive(Debug, Default)]
pub struct CrossTestResults {
    /// Results per target.
    results: Vec<(Target, TestOutcome)>,
}

/// Outcome of a single test.
#[derive(Debug, Clone)]
pub enum TestOutcome {
    /// Test passed.
    Passed,
    /// Test failed with message.
    Failed(String),
    /// Test was skipped (e.g., unsupported target).
    Skipped(String),
}

impl CrossTestResults {
    /// Create a new result aggregator.
    pub fn new() -> Self {
        Self::default()
    }

    /// Record a passed test.
    pub fn record_pass(&mut self, target: Target) {
        self.results.push((target, TestOutcome::Passed));
    }

    /// Record a failed test.
    pub fn record_fail(&mut self, target: Target, message: impl Into<String>) {
        self.results.push((target, TestOutcome::Failed(message.into())));
    }

    /// Record a skipped test.
    pub fn record_skip(&mut self, target: Target, reason: impl Into<String>) {
        self.results.push((target, TestOutcome::Skipped(reason.into())));
    }

    /// Check if all tests passed.
    pub fn all_passed(&self) -> bool {
        self.results.iter().all(|(_, outcome)| matches!(outcome, TestOutcome::Passed | TestOutcome::Skipped(_)))
    }

    /// Get the number of passed tests.
    pub fn passed_count(&self) -> usize {
        self.results.iter().filter(|(_, o)| matches!(o, TestOutcome::Passed)).count()
    }

    /// Get the number of failed tests.
    pub fn failed_count(&self) -> usize {
        self.results.iter().filter(|(_, o)| matches!(o, TestOutcome::Failed(_))).count()
    }

    /// Get the number of skipped tests.
    pub fn skipped_count(&self) -> usize {
        self.results.iter().filter(|(_, o)| matches!(o, TestOutcome::Skipped(_))).count()
    }

    /// Get a summary of the results.
    pub fn summary(&self) -> String {
        format!(
            "{} passed, {} failed, {} skipped",
            self.passed_count(),
            self.failed_count(),
            self.skipped_count()
        )
    }

    /// Assert that all tests passed (for use in test functions).
    pub fn assert_all_passed(&self) {
        if !self.all_passed() {
            let failures: Vec<_> = self.results
                .iter()
                .filter_map(|(t, o)| {
                    if let TestOutcome::Failed(msg) = o {
                        Some(format!("{}: {}", t, msg))
                    } else {
                        None
                    }
                })
                .collect();
            panic!("Cross-platform tests failed:\n{}", failures.join("\n"));
        }
    }
}

impl std::fmt::Display for CrossTestResults {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Cross-platform test results: {}", self.summary())?;

        for (target, outcome) in &self.results {
            let status = match outcome {
                TestOutcome::Passed => "PASS",
                TestOutcome::Failed(_) => "FAIL",
                TestOutcome::Skipped(_) => "SKIP",
            };
            write!(f, "  [{}] {}", status, target)?;
            match outcome {
                TestOutcome::Failed(msg) => writeln!(f, ": {}", msg)?,
                TestOutcome::Skipped(reason) => writeln!(f, ": {}", reason)?,
                TestOutcome::Passed => writeln!(f)?,
            }
        }

        Ok(())
    }
}

/// CI/CD configuration generator for multi-architecture builds.
pub struct CiConfig {
    /// Targets to build.
    targets: Vec<Target>,
    /// Whether to include tests.
    include_tests: bool,
}

impl CiConfig {
    /// Create a new CI config.
    pub fn new() -> Self {
        Self {
            targets: vec![Target::host()],
            include_tests: true,
        }
    }

    /// Add a target to build.
    pub fn with_target(mut self, target: Target) -> Self {
        if !self.targets.contains(&target) {
            self.targets.push(target);
        }
        self
    }

    /// Add all supported 64-bit targets.
    pub fn with_all_64bit(mut self) -> Self {
        for fixture in TargetFixture::all_64bit() {
            if !self.targets.contains(&fixture.target) {
                self.targets.push(fixture.target);
            }
        }
        self
    }

    /// Set whether to include tests.
    pub fn include_tests(mut self, include: bool) -> Self {
        self.include_tests = include;
        self
    }

    /// Generate GitHub Actions workflow YAML.
    pub fn to_github_actions(&self) -> String {
        let mut yaml = String::new();
        yaml.push_str("name: Multi-Architecture Build\n\n");
        yaml.push_str("on:\n  push:\n  pull_request:\n\n");
        yaml.push_str("jobs:\n");

        for target in &self.targets {
            let job_name = format!("build-{}-{}", target.arch.name(), target.os.name());
            let runner = match target.os {
                TargetOS::Linux => "ubuntu-latest",
                TargetOS::Windows => "windows-latest",
                TargetOS::MacOS => "macos-latest",
                _ => "ubuntu-latest",
            };

            yaml.push_str(&format!("  {}:\n", job_name));
            yaml.push_str(&format!("    runs-on: {}\n", runner));
            yaml.push_str("    steps:\n");
            yaml.push_str("      - uses: actions/checkout@v4\n");
            yaml.push_str("      - uses: dtolnay/rust-toolchain@stable\n");

            // Add cross-compilation target if not native
            if target.arch != TargetArch::host() {
                yaml.push_str(&format!(
                    "        with:\n          targets: {}\n",
                    target.arch.triple_str()
                ));
            }

            yaml.push_str(&format!(
                "      - run: cargo build --target {}\n",
                target.arch.triple_str()
            ));

            if self.include_tests && target.is_host() {
                yaml.push_str("      - run: cargo test\n");
            }

            yaml.push('\n');
        }

        yaml
    }
}

impl Default for CiConfig {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_target_fixture_host() {
        let fixture = TargetFixture::new(Target::host());
        assert!(fixture.is_host());
        assert!(fixture.can_execute());
    }

    #[test]
    fn test_target_fixture_non_host() {
        // Pick a target that's different from host
        let non_host = if TargetArch::host() == TargetArch::X86_64 {
            Target::new(TargetArch::Aarch64, TargetOS::Linux)
        } else {
            Target::new(TargetArch::X86_64, TargetOS::Linux)
        };

        let fixture = TargetFixture::new(non_host);
        assert!(!fixture.is_host());
        assert!(!fixture.can_execute());
    }

    #[test]
    fn test_target_fixture_mock_headers() {
        use crate::smf::header::SMF_MAGIC;

        let fixture = TargetFixture::x86_64_linux();

        let smf = fixture.mock_smf_header();
        assert_eq!(smf.magic, *SMF_MAGIC);
        assert_eq!(smf.arch, Arch::X86_64 as u8);
        assert_eq!(smf.platform, Platform::Linux as u8);

        let settlement = fixture.mock_settlement_header();
        assert_eq!(settlement.arch, Arch::X86_64 as u8);
    }

    #[test]
    fn test_test_matrix_default() {
        let matrix = TestMatrix::new();
        assert!(!matrix.targets().is_empty());
        assert!(!matrix.operating_systems().is_empty());
    }

    #[test]
    fn test_test_matrix_minimal() {
        let matrix = TestMatrix::minimal();
        assert_eq!(matrix.targets().len(), 1);
        assert_eq!(matrix.targets()[0], Target::host());
    }

    #[test]
    fn test_test_matrix_comprehensive() {
        let matrix = TestMatrix::comprehensive();
        assert!(matrix.targets().len() >= 9); // 3 arches * 3 OSes
    }

    #[test]
    fn test_cross_test_results() {
        let mut results = CrossTestResults::new();

        results.record_pass(Target::new(TargetArch::X86_64, TargetOS::Linux));
        results.record_fail(Target::new(TargetArch::Aarch64, TargetOS::Linux), "test error");
        results.record_skip(Target::new(TargetArch::Riscv64, TargetOS::Linux), "unsupported");

        assert_eq!(results.passed_count(), 1);
        assert_eq!(results.failed_count(), 1);
        assert_eq!(results.skipped_count(), 1);
        assert!(!results.all_passed());
    }

    #[test]
    fn test_cross_test_results_all_passed() {
        let mut results = CrossTestResults::new();

        results.record_pass(Target::new(TargetArch::X86_64, TargetOS::Linux));
        results.record_skip(Target::new(TargetArch::Riscv64, TargetOS::Linux), "unsupported");

        assert!(results.all_passed());
    }

    #[test]
    fn test_ci_config_github_actions() {
        let config = CiConfig::new()
            .with_target(Target::new(TargetArch::X86_64, TargetOS::Linux))
            .include_tests(true);

        let yaml = config.to_github_actions();
        assert!(yaml.contains("Multi-Architecture Build"));
        assert!(yaml.contains("ubuntu-latest"));
    }

    #[test]
    fn test_all_64bit_fixtures() {
        let fixtures = TargetFixture::all_64bit();
        assert!(fixtures.len() >= 5);

        for fixture in &fixtures {
            assert!(fixture.config.pointer_bytes == 8);
        }
    }
}
