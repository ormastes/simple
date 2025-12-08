# Simple Language Project - Development Commands
#
# Usage:
#   make test        - Run all tests
#   make coverage    - Generate test coverage report
#   make duplication - Check for code duplication
#   make lint        - Run clippy lints
#   make check       - Run all checks (lint, test, duplication)
#   make clean       - Clean build artifacts

.PHONY: all test coverage duplication lint check clean install-tools help

# Default target
all: check

# ============================================================================
# Testing
# ============================================================================

test:
	cargo test --workspace

test-verbose:
	cargo test --workspace -- --nocapture

# ============================================================================
# Coverage (requires cargo-llvm-cov)
# Install: cargo install cargo-llvm-cov
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
	@echo "Testing:"
	@echo "  make test          - Run all tests"
	@echo "  make test-verbose  - Run tests with output"
	@echo ""
	@echo "Coverage:"
	@echo "  make coverage      - Generate HTML coverage report"
	@echo "  make coverage-lcov - Generate LCOV format"
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
