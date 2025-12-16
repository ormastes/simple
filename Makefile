# Simple Language Project - Development Commands
#
# Usage:
#   make test        - Run all tests
#   make coverage    - Generate test coverage report
#   make duplication - Check for code duplication
#   make lint        - Run clippy lints
#   make check       - Run all checks (lint, test, duplication)
#   make clean       - Clean build artifacts

.PHONY: all test test-verbose test-unit test-integration test-system test-environment \
        test-full test-full-quick test-full-coverage test-full-extended test-full-check \
        coverage coverage-html coverage-lcov coverage-json coverage-summary \
        coverage-unit coverage-integration coverage-system coverage-environment coverage-merged coverage-all \
        coverage-check coverage-check-unit coverage-check-integration coverage-check-system \
        coverage-extended coverage-extended-system coverage-extended-integration coverage-extended-all coverage-extended-check \
        duplication duplication-simple lint lint-fix fmt fmt-check \
        check check-full unused-deps outdated audit build build-release \
        clean clean-coverage clean-duplication install-tools help

# Default target
all: check

# ============================================================================
# Testing
# ============================================================================

test:
	cargo test --workspace

test-verbose:
	cargo test --workspace -- --nocapture

# Test by level (per test.md policy)
# Unit tests: all workspace tests (631+ tests)
test-unit:
	cargo test --workspace

# Integration tests: tests/ crate integration level
test-integration:
	cargo test -p simple-tests --test integration

# System tests: tests/ crate system level
test-system:
	cargo test -p simple-tests --test system

# Environment tests: tests/ crate environment level
test-environment:
	cargo test -p simple-tests --test environment

# ============================================================================
# Full Test Mode with Automatic Coverage
# ============================================================================
# Runs all tests with LLVM coverage instrumentation and automatically generates
# extended coverage reports (system, integration, merged).
#
# Usage:
#   make test-full         - Run tests with coverage + generate all reports
#   make test-full-quick   - Run tests with coverage (skip extended reports)
#
# Environment variables:
#   SIMPLE_COVERAGE=0      - Disable coverage (just run tests)
#   SIMPLE_COV_THRESHOLD=80 - Coverage threshold for pass/fail (default: 80)
# ============================================================================

SIMPLE_COV_THRESHOLD ?= 80

test-full: test-full-coverage test-full-extended
	@echo ""
	@echo "=============================================="
	@echo "FULL TEST COMPLETE"
	@echo "=============================================="
	@echo "Coverage reports:"
	@echo "  HTML:        $(COVERAGE_DIR)/html/index.html"
	@echo "  System:      $(COVERAGE_DIR)/extended/coverage_system.json"
	@echo "  Integration: $(COVERAGE_DIR)/extended/coverage_integration.json"
	@echo "  Merged:      $(COVERAGE_DIR)/extended/coverage_merged.json"
	@echo ""

test-full-quick: test-full-coverage
	@echo "Quick test complete (coverage collected, extended reports skipped)"

test-full-coverage:
	@echo "=== RUNNING FULL TESTS WITH LLVM COVERAGE ==="
	@mkdir -p $(COVERAGE_DIR)
	@if [ "$${SIMPLE_COVERAGE:-1}" = "0" ]; then \
		echo "Coverage disabled (SIMPLE_COVERAGE=0), running plain tests..."; \
		cargo test --workspace; \
	else \
		echo "Running tests with LLVM coverage instrumentation..."; \
		cargo llvm-cov --workspace --json --output-path=$(COVERAGE_DIR)/coverage.json; \
		cargo llvm-cov --workspace --html --output-dir=$(COVERAGE_DIR)/html; \
		echo "Base coverage collected: $(COVERAGE_DIR)/coverage.json"; \
	fi

test-full-extended:
	@echo ""
	@echo "=== GENERATING EXTENDED COVERAGE REPORTS ==="
	@mkdir -p $(COVERAGE_DIR)/extended
	@if [ -f $(COVERAGE_DIR)/coverage.json ] && [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- generate \
			--llvm-cov $(COVERAGE_DIR)/coverage.json \
			--api public_api.yml \
			--output-dir $(COVERAGE_DIR)/extended \
			--report-type all; \
	else \
		echo "Skipping extended reports (missing coverage.json or public_api.yml)"; \
	fi

test-full-check: test-full
	@echo ""
	@echo "=== CHECKING COVERAGE THRESHOLDS ==="
	@if [ -f $(COVERAGE_DIR)/extended/coverage_system.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_system.json \
			--threshold $(SIMPLE_COV_THRESHOLD) || exit 1; \
	fi
	@if [ -f $(COVERAGE_DIR)/extended/coverage_integration.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_integration.json \
			--threshold $(SIMPLE_COV_THRESHOLD) || exit 1; \
	fi
	@echo "All coverage thresholds passed!"

# ============================================================================
# Coverage (requires cargo-llvm-cov)
# Install: cargo install cargo-llvm-cov
# Per test.md policy:
#   - Merged: UT + environment (line/branch/condition) - 100% threshold
#   - Integration: public function touch (separate) - 100% threshold
#   - System: public class/struct touch (separate) - 100% threshold
# ============================================================================

COVERAGE_DIR := target/coverage

coverage: coverage-html
	@echo "Coverage report: $(COVERAGE_DIR)/html/index.html"

coverage-html:
	@mkdir -p $(COVERAGE_DIR)
	cargo llvm-cov --workspace --html --output-dir $(COVERAGE_DIR)/html

coverage-lcov:
	@mkdir -p $(COVERAGE_DIR)
	cargo llvm-cov --workspace --lcov --output-path $(COVERAGE_DIR)/lcov.info

coverage-json:
	@mkdir -p $(COVERAGE_DIR)
	cargo llvm-cov --workspace --json --output-path $(COVERAGE_DIR)/coverage.json

coverage-summary:
	cargo llvm-cov --workspace

# Coverage by test level (per test.md policy)
# Unit: Branch/Condition coverage (all workspace tests)
coverage-unit:
	@mkdir -p $(COVERAGE_DIR)/unit
	@echo "=== UNIT TEST COVERAGE (Branch/Condition) ==="
	cargo llvm-cov --workspace --branch \
		--json --output-path=$(COVERAGE_DIR)/unit/coverage.json
	cargo llvm-cov --workspace --branch \
		--html --output-dir=$(COVERAGE_DIR)/unit/html
	@echo "Unit coverage report: $(COVERAGE_DIR)/unit/html/index.html"

# Integration: Public function touch
coverage-integration:
	@mkdir -p $(COVERAGE_DIR)/integration
	@echo "=== INTEGRATION TEST COVERAGE (Public Function Touch) ==="
	cargo llvm-cov -p simple-tests --test integration \
		--json --output-path=$(COVERAGE_DIR)/integration/coverage.json
	@echo "Analyzing public function touch..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/integration/coverage.json \
			--api public_api.yml --type public-func-touch 2>/dev/null || \
			cargo llvm-cov -p simple-tests --test integration; \
	else \
		cargo llvm-cov -p simple-tests --test integration; \
	fi

# System: Public class/struct touch
coverage-system:
	@mkdir -p $(COVERAGE_DIR)/system
	@echo "=== SYSTEM TEST COVERAGE (Public Class/Struct Touch) ==="
	cargo llvm-cov -p simple-tests --test system \
		--json --output-path=$(COVERAGE_DIR)/system/coverage.json
	@echo "Analyzing public class/struct touch..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/system/coverage.json \
			--api public_api.yml --type class-struct-touch 2>/dev/null || \
			cargo llvm-cov -p simple-tests --test system; \
	else \
		cargo llvm-cov -p simple-tests --test system; \
	fi

# Environment: Branch/Condition coverage (merged with unit)
coverage-environment:
	@mkdir -p $(COVERAGE_DIR)/environment
	@echo "=== ENVIRONMENT TEST COVERAGE (Branch/Condition) ==="
	cargo llvm-cov -p simple-tests --test environment --branch \
		--json --output-path=$(COVERAGE_DIR)/environment/coverage.json
	cargo llvm-cov -p simple-tests --test environment --branch

# Merged coverage: Unit + Environment (Branch/Condition)
coverage-merged:
	@mkdir -p $(COVERAGE_DIR)/merged
	@echo "=== MERGED COVERAGE (Unit + Environment) ==="
	cargo llvm-cov --workspace --branch \
		--json --output-path=$(COVERAGE_DIR)/merged/coverage.json
	cargo llvm-cov --workspace --branch \
		--html --output-dir=$(COVERAGE_DIR)/merged/html
	@echo "Merged coverage report: $(COVERAGE_DIR)/merged/html/index.html"

coverage-all: coverage-unit coverage-integration coverage-system coverage-environment
	@echo ""
	@echo "All coverage reports generated:"
	@echo "  Unit (branch/condition):         $(COVERAGE_DIR)/unit/"
	@echo "  Integration (public func touch): $(COVERAGE_DIR)/integration/"
	@echo "  System (class/struct touch):     $(COVERAGE_DIR)/system/"
	@echo "  Environment (branch/cond):       $(COVERAGE_DIR)/environment/"

# Extended coverage reports (per coverage_json_format.md spec)
# Generates: coverage_system.json, coverage_integration.json, coverage_merged.json
coverage-extended: coverage-json
	@echo "=== GENERATING EXTENDED COVERAGE REPORTS ==="
	@mkdir -p $(COVERAGE_DIR)/extended
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- generate \
			--llvm-cov $(COVERAGE_DIR)/coverage.json \
			--api public_api.yml \
			--output-dir $(COVERAGE_DIR)/extended; \
	else \
		echo "Warning: public_api.yml not found, skipping extended reports"; \
	fi

# Extended coverage by test level
coverage-extended-system:
	@mkdir -p $(COVERAGE_DIR)/extended
	@echo "=== EXTENDED SYSTEM COVERAGE ==="
	cargo llvm-cov -p simple-tests --test system \
		--json --output-path=$(COVERAGE_DIR)/system_raw.json
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- generate \
			--llvm-cov $(COVERAGE_DIR)/system_raw.json \
			--api public_api.yml \
			--output-dir $(COVERAGE_DIR)/extended \
			--report-type system; \
	fi

coverage-extended-integration:
	@mkdir -p $(COVERAGE_DIR)/extended
	@echo "=== EXTENDED INTEGRATION COVERAGE ==="
	cargo llvm-cov -p simple-tests --test integration \
		--json --output-path=$(COVERAGE_DIR)/integration_raw.json
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- generate \
			--llvm-cov $(COVERAGE_DIR)/integration_raw.json \
			--api public_api.yml \
			--output-dir $(COVERAGE_DIR)/extended \
			--report-type integration; \
	fi

coverage-extended-all: coverage-extended-system coverage-extended-integration coverage-extended
	@echo ""
	@echo "Extended coverage reports generated:"
	@echo "  System (class/struct methods): $(COVERAGE_DIR)/extended/coverage_system.json"
	@echo "  Integration (public functions): $(COVERAGE_DIR)/extended/coverage_integration.json"
	@echo "  Merged (all metrics): $(COVERAGE_DIR)/extended/coverage_merged.json"

# Check extended coverage thresholds
coverage-extended-check:
	@echo "=== CHECKING EXTENDED COVERAGE THRESHOLDS ==="
	@if [ -f $(COVERAGE_DIR)/extended/coverage_system.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_system.json \
			--threshold 80; \
	fi
	@if [ -f $(COVERAGE_DIR)/extended/coverage_integration.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_integration.json \
			--threshold 80; \
	fi

# Coverage threshold checks (per test.md: 100% for all)
coverage-check: coverage-check-unit coverage-check-integration coverage-check-system
	@echo "All coverage thresholds passed!"

coverage-check-unit:
	@echo "Checking unit test coverage (branch/condition)..."
	cargo llvm-cov --workspace --branch --fail-under-lines 100
	cargo llvm-cov --workspace --branch --fail-under-branches 100

coverage-check-integration:
	@echo "Checking integration public function touch..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/integration/coverage.json \
			--api public_api.yml --type public-func-touch --threshold 100; \
	else \
		echo "Warning: public_api.yml not found, skipping integration coverage check"; \
	fi

coverage-check-system:
	@echo "Checking system public class/struct touch..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/system/coverage.json \
			--api public_api.yml --type class-struct-touch --threshold 100; \
	else \
		echo "Warning: public_api.yml not found, skipping system coverage check"; \
	fi

# ============================================================================
# Code Duplication Detection (requires jscpd)
# Install: npm install -g jscpd
# ============================================================================

DUPLICATION_DIR := target/duplication

duplication:
	@mkdir -p $(DUPLICATION_DIR)
	@echo "Checking for code duplication..."
	@if command -v jscpd >/dev/null 2>&1; then \
		jscpd src/ --reporters html,console --output $(DUPLICATION_DIR) \
			--min-lines 5 --min-tokens 50 \
			--ignore "**/target/**,**/*.md" \
			--format "rust"; \
		echo "Duplication report: $(DUPLICATION_DIR)/html/index.html"; \
	else \
		echo "jscpd not found. Install with: npm install -g jscpd"; \
		echo "Running fallback duplicate detection..."; \
		$(MAKE) duplication-simple; \
	fi

# Simple duplicate detection using grep (fallback)
duplication-simple:
	@echo "=== Potential duplicate patterns ==="
	@echo ""
	@echo "Functions with similar names:"
	@grep -rh "^fn \|^pub fn \|^pub(crate) fn " src/ --include="*.rs" | \
		sed 's/.*fn \([a-z_]*\).*/\1/' | sort | uniq -c | sort -rn | head -20
	@echo ""
	@echo "Structs with similar names:"
	@grep -rh "^struct \|^pub struct " src/ --include="*.rs" | \
		sed 's/.*struct \([A-Za-z_]*\).*/\1/' | sort | uniq -c | sort -rn | head -10
	@echo ""
	@echo "Large functions (>50 lines) - candidates for refactoring:"
	@find src/ -name "*.rs" -exec awk '/^[[:space:]]*(pub )?fn / {name=$$0; count=0} /^[[:space:]]*(pub )?fn /,/^}/ {count++} count>50 {print FILENAME": "name" ("count" lines)"; count=0}' {} \;

# ============================================================================
# Linting
# ============================================================================

lint:
	cargo clippy --workspace --all-targets -- -D warnings

lint-fix:
	cargo clippy --workspace --all-targets --fix --allow-dirty

fmt:
	cargo fmt --all

fmt-check:
	cargo fmt --all -- --check

# ============================================================================
# Combined Checks
# ============================================================================

check: fmt-check lint test
	@echo "All checks passed!"

check-full: fmt-check lint test coverage-summary duplication
	@echo "Full check complete!"

# ============================================================================
# Dependency Analysis
# ============================================================================

# Check for unused dependencies (requires cargo-udeps, nightly)
unused-deps:
	cargo +nightly udeps --workspace

# Check for outdated dependencies
outdated:
	cargo outdated --workspace

# Security audit
audit:
	cargo audit

# ============================================================================
# Build
# ============================================================================

build:
	cargo build --workspace

build-release:
	cargo build --workspace --release

# ============================================================================
# Cleanup
# ============================================================================

clean:
	cargo clean
	rm -rf $(COVERAGE_DIR) $(DUPLICATION_DIR)

clean-coverage:
	rm -rf $(COVERAGE_DIR)

clean-duplication:
	rm -rf $(DUPLICATION_DIR)

# ============================================================================
# Tool Installation
# ============================================================================

install-tools:
	@echo "Installing development tools..."
	cargo install cargo-llvm-cov
	cargo install cargo-audit
	cargo install cargo-outdated
	@echo ""
	@echo "Optional (requires npm):"
	@echo "  npm install -g jscpd"
	@echo ""
	@echo "Optional (requires nightly):"
	@echo "  cargo install cargo-udeps"

# ============================================================================
# Help
# ============================================================================

help:
	@echo "Simple Language Project - Available Commands"
	@echo ""
	@echo "Testing (807+ tests total):"
	@echo "  make test               - Run all tests"
	@echo "  make test-verbose       - Run tests with output"
	@echo "  make test-unit          - Run all workspace unit tests"
	@echo "  make test-integration   - Run integration tests only"
	@echo "  make test-system        - Run system tests only"
	@echo "  make test-environment   - Run environment tests only"
	@echo ""
	@echo "Full Test Mode (automatic coverage):"
	@echo "  make test-full          - Run tests + generate all coverage reports"
	@echo "  make test-full-quick    - Run tests + collect coverage (no extended reports)"
	@echo "  make test-full-check    - Run test-full + verify thresholds"
	@echo "  Environment variables:"
	@echo "    SIMPLE_COVERAGE=0       - Disable coverage (just run tests)"
	@echo "    SIMPLE_COV_THRESHOLD=80 - Coverage threshold % (default: 80)"
	@echo ""
	@echo "Coverage (per test.md policy):"
	@echo "  make coverage              - Generate HTML coverage report"
	@echo "  make coverage-unit         - Unit tests (branch/condition)"
	@echo "  make coverage-integration  - Integration (public function touch)"
	@echo "  make coverage-system       - System (public class/struct touch)"
	@echo "  make coverage-environment  - Environment (branch/condition)"
	@echo "  make coverage-merged       - Merged unit + environment (branch/condition)"
	@echo "  make coverage-all          - Generate all coverage reports"
	@echo "  make coverage-check        - Verify all coverage thresholds (100%)"
	@echo "  make coverage-summary      - Print coverage summary"
	@echo ""
	@echo "Extended Coverage (public API):"
	@echo "  make coverage-extended     - Generate extended reports from existing data"
	@echo "  make coverage-extended-all - Generate all extended report types"
	@echo ""
	@echo "Duplication:"
	@echo "  make duplication   - Check for code duplication"
	@echo ""
	@echo "Linting:"
	@echo "  make lint          - Run clippy"
	@echo "  make lint-fix      - Auto-fix clippy warnings"
	@echo "  make fmt           - Format code"
	@echo "  make fmt-check     - Check formatting"
	@echo ""
	@echo "Combined:"
	@echo "  make check         - Run fmt, lint, test"
	@echo "  make check-full    - Run all checks + coverage + duplication"
	@echo ""
	@echo "Other:"
	@echo "  make install-tools - Install required tools"
	@echo "  make clean         - Clean all artifacts"
	@echo "  make help          - Show this help"
