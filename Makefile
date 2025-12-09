# Simple Language Project - Development Commands
#
# Usage:
#   make test        - Run all tests
#   make coverage    - Generate test coverage report
#   make duplication - Check for code duplication
#   make lint        - Run clippy lints
#   make check       - Run all checks (lint, test, duplication)
#   make clean       - Clean build artifacts

.PHONY: all test test-verbose test-unit test-it test-system test-env \
        coverage coverage-html coverage-lcov coverage-json coverage-summary \
        coverage-unit coverage-it coverage-system coverage-env coverage-merged coverage-all \
        coverage-check coverage-check-unit coverage-check-it coverage-check-system \
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

# Integration tests: tests/ crate IT level
test-it:
	cargo test -p simple-tests --test it

# System tests: tests/ crate system level
test-system:
	cargo test -p simple-tests --test system

# Environment tests: tests/ crate env_test level
test-env:
	cargo test -p simple-tests --test env_test

# ============================================================================
# Coverage (requires cargo-llvm-cov)
# Install: cargo install cargo-llvm-cov
# Per test.md policy:
#   - Merged: UT + env_test (line/branch/condition) - 100% threshold
#   - IT: public function coverage (separate) - 100% threshold
#   - System: class/struct coverage (separate) - 100% threshold
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

# Integration: Public function coverage on class/struct
coverage-it:
	@mkdir -p $(COVERAGE_DIR)/it
	@echo "=== INTEGRATION TEST COVERAGE (Public Functions) ==="
	cargo llvm-cov -p simple-tests --test it \
		--json --output-path=$(COVERAGE_DIR)/it/coverage.json
	@echo "Analyzing public function coverage..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/it/coverage.json \
			--api public_api.yml --type public-func 2>/dev/null || \
			cargo llvm-cov -p simple-tests --test it; \
	else \
		cargo llvm-cov -p simple-tests --test it; \
	fi

# System: Class/struct method coverage
coverage-system:
	@mkdir -p $(COVERAGE_DIR)/system
	@echo "=== SYSTEM TEST COVERAGE (Class/Struct Methods) ==="
	cargo llvm-cov -p simple-tests --test system \
		--json --output-path=$(COVERAGE_DIR)/system/coverage.json
	@echo "Analyzing class/struct coverage..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/system/coverage.json \
			--api public_api.yml --type class-struct 2>/dev/null || \
			cargo llvm-cov -p simple-tests --test system; \
	else \
		cargo llvm-cov -p simple-tests --test system; \
	fi

# Environment: Branch/Condition coverage (merged with unit)
coverage-env:
	@mkdir -p $(COVERAGE_DIR)/env
	@echo "=== ENVIRONMENT TEST COVERAGE (Branch/Condition) ==="
	cargo llvm-cov -p simple-tests --test env_test --branch \
		--json --output-path=$(COVERAGE_DIR)/env/coverage.json
	cargo llvm-cov -p simple-tests --test env_test --branch

# Merged coverage: Unit + Environment (Branch/Condition)
coverage-merged:
	@mkdir -p $(COVERAGE_DIR)/merged
	@echo "=== MERGED COVERAGE (Unit + Environment) ==="
	cargo llvm-cov --workspace --branch \
		--json --output-path=$(COVERAGE_DIR)/merged/coverage.json
	cargo llvm-cov --workspace --branch \
		--html --output-dir=$(COVERAGE_DIR)/merged/html
	@echo "Merged coverage report: $(COVERAGE_DIR)/merged/html/index.html"

coverage-all: coverage-unit coverage-it coverage-system coverage-env
	@echo ""
	@echo "All coverage reports generated:"
	@echo "  Unit (branch/condition):    $(COVERAGE_DIR)/unit/"
	@echo "  Integration (public func):  $(COVERAGE_DIR)/it/"
	@echo "  System (class/struct):      $(COVERAGE_DIR)/system/"
	@echo "  Environment (branch/cond):  $(COVERAGE_DIR)/env/"

# Coverage threshold checks (per test.md: 100% for all)
coverage-check: coverage-check-unit coverage-check-it coverage-check-system
	@echo "All coverage thresholds passed!"

coverage-check-unit:
	@echo "Checking unit test coverage (branch/condition)..."
	cargo llvm-cov --workspace --branch --fail-under-lines 100
	cargo llvm-cov --workspace --branch --fail-under-branches 100

coverage-check-it:
	@echo "Checking IT public function coverage..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/it/coverage.json \
			--api public_api.yml --type public-func --threshold 100; \
	else \
		echo "Warning: public_api.yml not found, skipping IT coverage check"; \
	fi

coverage-check-system:
	@echo "Checking system class/struct coverage..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/system/coverage.json \
			--api public_api.yml --type class-struct --threshold 100; \
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
	@echo "Testing (631+ tests total):"
	@echo "  make test          - Run all tests"
	@echo "  make test-verbose  - Run tests with output"
	@echo "  make test-unit     - Run all workspace unit tests"
	@echo "  make test-it       - Run integration tests only"
	@echo "  make test-system   - Run system tests only"
	@echo "  make test-env      - Run environment tests only"
	@echo ""
	@echo "Coverage (per test.md policy):"
	@echo "  make coverage         - Generate HTML coverage report"
	@echo "  make coverage-unit    - Unit tests (branch/condition)"
	@echo "  make coverage-it      - Integration (public function on class/struct)"
	@echo "  make coverage-system  - System (class/struct method coverage)"
	@echo "  make coverage-env     - Environment (branch/condition)"
	@echo "  make coverage-merged  - Merged unit + env (branch/condition)"
	@echo "  make coverage-all     - Generate all coverage reports"
	@echo "  make coverage-check   - Verify all coverage thresholds (100%)"
	@echo "  make coverage-summary - Print coverage summary"
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
