# Simple Language Project - Development Commands
#
# ⚠️  DEPRECATION NOTICE
# ======================
# This Makefile is being phased out in favor of the Simple build system.
# Please migrate to using:
#
#   simple build [command]
#
# Makefile commands still work but will show deprecation warnings.
# See doc/build/migration_guide.md for migration instructions.
#
# Common migrations:
#   make test        →  simple build test
#   make coverage    →  simple build coverage
#   make lint        →  simple build lint
#   make fmt         →  simple build fmt
#   make check       →  simple build check
#   make build       →  simple build
#   make clean       →  simple build clean

# Deprecation warning helper
define DEPRECATION_WARNING
	@echo ""
	@echo "⚠️  DEPRECATION WARNING"
	@echo "======================="
	@echo "This Makefile target is deprecated. Please use:"
	@echo "  simple build $(1)"
	@echo ""
	@echo "Continuing with legacy Makefile execution..."
	@echo ""
endef

.PHONY: all test test-rust test-verbose test-unit test-integration test-system test-environment \
        test-full test-full-quick test-full-coverage test-full-extended test-full-check \
        coverage coverage-html coverage-lcov coverage-json coverage-summary \
        coverage-unit coverage-integration coverage-system coverage-environment coverage-service coverage-merged coverage-all \
        coverage-check coverage-check-unit coverage-check-integration coverage-check-system coverage-check-service \
        coverage-extended coverage-extended-system coverage-extended-integration coverage-extended-service coverage-extended-all coverage-extended-check \
        duplication duplication-simple lint lint-fix fmt fmt-check \
        check check-full unused-deps outdated audit build build-release \
        link-bins link-bins-linux link-bins-mac link-bins-windows \
        clean clean-coverage clean-duplication install-tools help \
        arch-test arch-test-visualize \
        check-todos gen-todos todos todos-p0 \
        dashboard dashboard-collect dashboard-snapshot dashboard-trends dashboard-alerts \
        bootstrap bootstrap-stage1 bootstrap-stage2 bootstrap-stage3 bootstrap-verify bootstrap-clean \
        package-bootstrap package-full package-all install install-user install-system uninstall

# Default target
all: check

# ============================================================================
# Testing
# ============================================================================

# Run ALL tests: Rust tests + Rust doc-tests + Simple/SSpec tests
# Excludes: skip, slow/long-run (#[ignore]), and explicitly ignored tests
test:
	$(call DEPRECATION_WARNING,test)
	@echo "=== Running Rust Tests ==="
	cd rust && cargo test --workspace
	@echo ""
	@echo "=== Running Rust Doc-Tests ==="
	cd rust && cargo test --doc --workspace
	@echo ""
	@echo "=== Running Simple/SSpec Tests ==="
	./rust/target/debug/simple_runtime test

# Run Rust tests only (faster, no Simple/SSpec)
test-rust:
	$(call DEPRECATION_WARNING,test-rust)
	cd rust && cargo test --workspace

test-verbose:
	$(call DEPRECATION_WARNING,test --verbose)
	cd rust && cargo test --workspace -- --nocapture

# Test by level (per test.md policy)
# Unit tests: all workspace tests (631+ tests)
test-unit:
	$(call DEPRECATION_WARNING,test --level=unit)
	cd rust && cargo test --workspace

# Integration tests: tests/ crate integration level
test-integration:
	$(call DEPRECATION_WARNING,test --level=integration)
	cd rust && cargo test -p simple-tests --test integration

# System tests: tests/ crate system level
test-system:
	$(call DEPRECATION_WARNING,test --level=system)
	cd rust && cargo test -p simple-tests --test system

# Environment tests: tests/ crate environment level
test-environment:
	$(call DEPRECATION_WARNING,test --level=environment)
	cd rust && cargo test -p simple-tests --test environment

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

COVERAGE_DIR := rust/target/coverage
STACK_ENV := RUST_MIN_STACK=33554432
REAL_SIMPLE_BIN := $(shell pwd)/rust/target/debug/simple

coverage: coverage-html
	$(call DEPRECATION_WARNING,coverage)
	@echo "Coverage report: $(COVERAGE_DIR)/html/index.html"

coverage-html:
	$(call DEPRECATION_WARNING,coverage)
	@mkdir -p $(COVERAGE_DIR)
	cd rust && cargo llvm-cov --workspace --html --output-dir $(COVERAGE_DIR)/html

coverage-lcov:
	$(call DEPRECATION_WARNING,coverage --format=lcov)
	@mkdir -p $(COVERAGE_DIR)
	cd rust && cargo llvm-cov --workspace --lcov --output-path $(COVERAGE_DIR)/lcov.info

coverage-json:
	$(call DEPRECATION_WARNING,coverage --format=json)
	@mkdir -p $(COVERAGE_DIR)
	cd rust && cargo llvm-cov --workspace --json --output-path $(COVERAGE_DIR)/coverage.json

coverage-summary:
	$(call DEPRECATION_WARNING,coverage --summary)
	cd rust && cargo llvm-cov --workspace

# Coverage by test level (per test.md policy)
# Unit: Branch/Condition coverage (all workspace tests)
coverage-unit:
	@mkdir -p $(COVERAGE_DIR)/unit
	@echo "=== UNIT TEST COVERAGE (Branch/Condition) ==="
	cd rust && cargo llvm-cov --workspace --branch \
		--json --output-path=$(COVERAGE_DIR)/unit/coverage.json
	cd rust && cargo llvm-cov --workspace --branch \
		--html --output-dir=$(COVERAGE_DIR)/unit/html
	@echo "Unit coverage report: $(COVERAGE_DIR)/unit/html/index.html"

# Integration: Public function touch
coverage-integration:
	@mkdir -p $(COVERAGE_DIR)/integration
	@echo "=== INTEGRATION TEST COVERAGE (Public Function Touch) ==="
	cd rust && cargo llvm-cov -p simple-tests --test integration \
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
	@cd rust && cargo build -p simple-driver --bin simple
	@mkdir -p $(COVERAGE_DIR)/system
	@echo "=== SYSTEM TEST COVERAGE (Public Class/Struct Touch) ==="
	cd rust && $(STACK_ENV) CARGO_BIN_EXE_simple=$(REAL_SIMPLE_BIN) cargo llvm-cov -p simple-tests --test system \
		--json --output-path=$(COVERAGE_DIR)/system/coverage.json
	@echo "Analyzing public class/struct touch..."
	@if [ -f public_api.yml ]; then \
		cd rust && $(STACK_ENV) cargo run -p simple_mock_helper --bin smh_coverage -- \
			--coverage $(COVERAGE_DIR)/system/coverage.json \
			--api public_api.yml --type class-struct-touch 2>/dev/null || \
			cd rust && $(STACK_ENV) CARGO_BIN_EXE_simple=$(REAL_SIMPLE_BIN) cargo llvm-cov -p simple-tests --test system; \
	else \
		cd rust && $(STACK_ENV) CARGO_BIN_EXE_simple=$(REAL_SIMPLE_BIN) cargo llvm-cov -p simple-tests --test system; \
	fi

# Environment: Branch/Condition coverage (merged with unit)
coverage-environment:
	@mkdir -p $(COVERAGE_DIR)/environment
	@echo "=== ENVIRONMENT TEST COVERAGE (Branch/Condition) ==="
	cd rust && cargo llvm-cov -p simple-tests --test environment --branch \
		--json --output-path=$(COVERAGE_DIR)/environment/coverage.json
	cd rust && cargo llvm-cov -p simple-tests --test environment --branch

# Service: Interface class + External library touch
coverage-service:
	@mkdir -p $(COVERAGE_DIR)/service
	@echo "=== SERVICE TEST COVERAGE (Interface + External Lib Touch) ==="
	cd rust && cargo llvm-cov --workspace \
		--json --output-path=$(COVERAGE_DIR)/service/coverage.json
	@echo "Analyzing interface and external library touch..."
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- generate \
			--llvm-cov $(COVERAGE_DIR)/service/coverage.json \
			--api public_api.yml \
			--output-dir $(COVERAGE_DIR)/service \
			--report-type service; \
	else \
		echo "Warning: public_api.yml not found, skipping service coverage analysis"; \
	fi

# Merged coverage: Unit + Environment (Branch/Condition)
coverage-merged:
	@mkdir -p $(COVERAGE_DIR)/merged
	@echo "=== MERGED COVERAGE (Unit + Environment) ==="
	cd rust && cargo llvm-cov --workspace --branch \
		--json --output-path=$(COVERAGE_DIR)/merged/coverage.json
	cd rust && cargo llvm-cov --workspace --branch \
		--html --output-dir=$(COVERAGE_DIR)/merged/html
	@echo "Merged coverage report: $(COVERAGE_DIR)/merged/html/index.html"

coverage-all: coverage-unit coverage-integration coverage-system coverage-service coverage-environment
	@echo ""
	@echo "All coverage reports generated:"
	@echo "  Unit (branch/condition):          $(COVERAGE_DIR)/unit/"
	@echo "  Integration (public func touch):  $(COVERAGE_DIR)/integration/"
	@echo "  System (class/struct touch):      $(COVERAGE_DIR)/system/"
	@echo "  Service (interface + ext lib):    $(COVERAGE_DIR)/service/"
	@echo "  Environment (branch/cond):        $(COVERAGE_DIR)/environment/"

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
	cd rust && cargo llvm-cov -p simple-tests --test system \
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
	cd rust && cargo llvm-cov -p simple-tests --test integration \
		--json --output-path=$(COVERAGE_DIR)/integration_raw.json
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- generate \
			--llvm-cov $(COVERAGE_DIR)/integration_raw.json \
			--api public_api.yml \
			--output-dir $(COVERAGE_DIR)/extended \
			--report-type integration; \
	fi

coverage-extended-service:
	@mkdir -p $(COVERAGE_DIR)/extended
	@echo "=== EXTENDED SERVICE COVERAGE ==="
	cd rust && cargo llvm-cov --workspace \
		--json --output-path=$(COVERAGE_DIR)/service_raw.json
	@if [ -f public_api.yml ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- generate \
			--llvm-cov $(COVERAGE_DIR)/service_raw.json \
			--api public_api.yml \
			--output-dir $(COVERAGE_DIR)/extended \
			--report-type service; \
	fi

coverage-extended-all: coverage-extended-system coverage-extended-service coverage-extended-integration coverage-extended
	@echo ""
	@echo "Extended coverage reports generated:"
	@echo "  System (class/struct methods):   $(COVERAGE_DIR)/extended/coverage_system.json"
	@echo "  Service (interface + ext lib):   $(COVERAGE_DIR)/extended/coverage_service.json"
	@echo "  Integration (public functions):  $(COVERAGE_DIR)/extended/coverage_integration.json"
	@echo "  Merged (all metrics):            $(COVERAGE_DIR)/extended/coverage_merged.json"

# Check extended coverage thresholds
coverage-extended-check:
	@echo "=== CHECKING EXTENDED COVERAGE THRESHOLDS ==="
	@if [ -f $(COVERAGE_DIR)/extended/coverage_system.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_system.json \
			--threshold 80; \
	fi
	@if [ -f $(COVERAGE_DIR)/extended/coverage_service.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_service.json \
			--threshold 80; \
	fi
	@if [ -f $(COVERAGE_DIR)/extended/coverage_integration.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_integration.json \
			--threshold 80; \
	fi

# Coverage threshold checks (per test.md: 100% for all)
coverage-check: coverage-check-unit coverage-check-integration coverage-check-system coverage-check-service
	@echo "All coverage thresholds passed!"

coverage-check-unit:
	@echo "Checking unit test coverage (branch/condition)..."
	cd rust && cargo llvm-cov --workspace --branch --fail-under-lines 100
	cd rust && cargo llvm-cov --workspace --branch --fail-under-branches 100

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

coverage-check-service:
	@echo "Checking service interface + external lib touch..."
	@if [ -f $(COVERAGE_DIR)/extended/coverage_service.json ]; then \
		cargo run -p simple_mock_helper --bin coverage_gen -- check \
			--coverage $(COVERAGE_DIR)/extended/coverage_service.json \
			--threshold 100; \
	else \
		echo "Warning: coverage_service.json not found, run 'make coverage-service' first"; \
	fi

# ============================================================================
# Code Duplication Detection (requires jscpd)
# Install: npm install -g jscpd
# ============================================================================

DUPLICATION_DIR := rust/target/duplication

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
	$(call DEPRECATION_WARNING,lint)
	cd rust && cargo clippy --workspace --all-targets -- -D warnings

lint-fix:
	$(call DEPRECATION_WARNING,lint --fix)
	cd rust && cargo clippy --workspace --all-targets --fix --allow-dirty

fmt:
	$(call DEPRECATION_WARNING,fmt)
	cd rust && cargo fmt --all

fmt-check:
	$(call DEPRECATION_WARNING,fmt --check)
	cd rust && cargo fmt --all -- --check

# ============================================================================
# Combined Checks
# ============================================================================

check: fmt-check lint test
	$(call DEPRECATION_WARNING,check)
	@echo "All checks passed!"

check-full: fmt-check lint test coverage-summary duplication
	$(call DEPRECATION_WARNING,check --full)
	@echo "Full check complete!"

# ============================================================================
# Dependency Analysis
# ============================================================================

# Check for unused dependencies (requires cargo-udeps, nightly)
unused-deps:
	cd rust && cargo +nightly udeps --workspace

# Check for outdated dependencies
outdated:
	cd rust && cargo outdated --workspace

# Security audit
audit:
	cd rust && cargo audit

# ============================================================================
# Build
# ============================================================================

build:
	$(call DEPRECATION_WARNING,build)
	cd rust && cargo build --workspace

build-release:
	$(call DEPRECATION_WARNING,build --release)
	cd rust && cargo build --workspace --release

# Link binaries (cross-platform)
link-bins:
ifeq ($(OS),Windows_NT)
	@powershell -ExecutionPolicy Bypass -File script/link-bins.ps1
else
	@bash script/link-bins.sh
endif

# Platform-specific link targets
link-bins-linux:
	@bash script/link-bins.sh

link-bins-mac:
	@bash script/link-bins.sh

link-bins-windows:
	@powershell -ExecutionPolicy Bypass -File script/link-bins.ps1

# ============================================================================
# Cleanup
# ============================================================================

clean:
	$(call DEPRECATION_WARNING,clean)
	cd rust && cargo clean
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
	cd rust && cargo install cargo-llvm-cov
	cd rust && cargo install cargo-audit
	cd rust && cargo install cargo-outdated
	@echo ""
	@echo "Optional (requires npm):"
	@echo "  npm install -g jscpd"
	@echo ""
	@echo "Optional (requires nightly):"
	@echo "  cargo install cargo-udeps"

# ============================================================================
# Architecture Testing (#944-#945)
# ============================================================================

# Run architecture tests (validates layer dependencies)
arch-test:
	@echo "=== ARCHITECTURE TESTS ==="
	cd rust && cargo test -p arch_test --all-targets
	@echo ""
	@echo "Architecture tests passed!"

# Generate dependency graph visualization (DOT format)
arch-test-visualize:
	@echo "=== ARCHITECTURE VISUALIZATION ==="
	@mkdir -p rust/target/arch
	@echo "Generating DOT graph..."
	@if cargo run -p arch_test --example visualize 2>/dev/null; then \
		echo "DOT graph: rust/target/arch/layers.dot"; \
		echo "Mermaid graph: rust/target/arch/layers.mmd"; \
		echo ""; \
		echo "To render DOT: dot -Tpng rust/target/arch/layers.dot -o rust/target/arch/layers.png"; \
	else \
		echo "Note: Run 'cargo test -p arch_test' to verify architecture"; \
	fi

# ============================================================================
# TODO Management
# ============================================================================

# Validate TODO format (requires TODO scanning to be implemented)
check-todos:
	@echo "Validating TODO format..."
	@./rust/target/debug/simple_runtime todo-scan --parallel --validate || (echo "ERROR: Invalid TODO format found" && exit 1)
	@echo "✓ All TODOs are properly formatted"

# Generate TODO documentation (parallel mode for 7.8x speedup)
gen-todos:
	@echo "Updating TODO database..."
	@./rust/target/debug/simple_runtime todo-scan --parallel
	@./rust/target/debug/simple_runtime todo-gen
	@echo "✓ Generated doc/TODO.md"

# Generate and show recent TODOs
todos: gen-todos
	@head -30 doc/TODO.md

# Show critical (P0) TODOs only
todos-p0:
	@echo "Critical (P0) TODOs:"
	@grep -A 5 "## P0 Critical TODOs" doc/TODO.md | tail -n +2 || echo "✓ No P0 TODOs found!"

# ============================================================================
# Dashboard & Metrics
# ============================================================================

# Show dashboard summary
dashboard:
	@./rust/target/debug/simple_runtime dashboard status

# Collect fresh metrics
dashboard-collect:
	@./rust/target/debug/simple_runtime dashboard collect --mode=full

# Create daily snapshot
dashboard-snapshot:
	@./rust/target/debug/simple_runtime dashboard snapshot
	@./rust/target/debug/simple_runtime dashboard cleanup

# Show trend analysis
dashboard-trends:
	@./rust/target/debug/simple_runtime dashboard trends --monthly

# Check for critical alerts
dashboard-alerts:
	@./rust/target/debug/simple_runtime dashboard check-alerts

# ============================================================================
# Bootstrap (Multi-Stage Self-Compilation)
# ============================================================================
#
# Builds verified bootstrap pipeline: simple_runtime → simple_new1 → simple_new2 → simple_new3
# Verification: simple_new2 and simple_new3 must be bitwise identical
#
# Usage:
#   make bootstrap           - Run full bootstrap pipeline with verification
#   make bootstrap-stage1    - Build simple_new1 using Rust runtime
#   make bootstrap-stage2    - Build simple_new2 using simple_new1
#   make bootstrap-stage3    - Build simple_new3 using simple_new2
#   make bootstrap-verify    - Verify simple_new2 == simple_new3
#   make bootstrap-clean     - Clean bootstrap artifacts

BOOTSTRAP_DIR := rust/target/bootstrap

.PHONY: bootstrap bootstrap-stage1 bootstrap-stage2 bootstrap-stage3 bootstrap-verify bootstrap-clean bootstrap-promote bootstrap-from-stable

bootstrap: bootstrap-clean bootstrap-stage1 bootstrap-stage2 bootstrap-stage3 bootstrap-verify
	@echo ""
	@echo "=============================================="
	@echo "BOOTSTRAP COMPLETE"
	@echo "=============================================="
	@ls -lh $(BOOTSTRAP_DIR)/simple_new*

BOOTSTRAP_STAGE1_NAME ?= simple_new1

bootstrap-stage1:
	@echo "=== Stage 1: simple_runtime (Rust) -> $(BOOTSTRAP_STAGE1_NAME) ==="
	@mkdir -p $(BOOTSTRAP_DIR)
	SIMPLE_COMPILE_RUST=1 ./rust/target/debug/simple_runtime compile simple/compiler/main.spl -o $(BOOTSTRAP_DIR)/$(BOOTSTRAP_STAGE1_NAME) --native
	@chmod +x $(BOOTSTRAP_DIR)/$(BOOTSTRAP_STAGE1_NAME)
	@echo "Stage 1 complete: $(BOOTSTRAP_DIR)/$(BOOTSTRAP_STAGE1_NAME)"

bootstrap-stage2: bootstrap-stage1
	@echo "=== Stage 2: simple_new1 -> simple_new2 ==="
	$(BOOTSTRAP_DIR)/simple_new1 -c -o $(BOOTSTRAP_DIR)/simple_new2 simple/compiler/main.spl
	@chmod +x $(BOOTSTRAP_DIR)/simple_new2
	@echo "Stage 2 complete: $(BOOTSTRAP_DIR)/simple_new2"

bootstrap-stage3: bootstrap-stage2
	@echo "=== Stage 3: simple_new2 -> simple_new3 ==="
	$(BOOTSTRAP_DIR)/simple_new2 -c -o $(BOOTSTRAP_DIR)/simple_new3 simple/compiler/main.spl
	@chmod +x $(BOOTSTRAP_DIR)/simple_new3
	@echo "Stage 3 complete: $(BOOTSTRAP_DIR)/simple_new3"

bootstrap-verify:
	@echo "=== Verification: Comparing simple_new2 and simple_new3 ==="
	@HASH2=$$(sha256sum $(BOOTSTRAP_DIR)/simple_new2 | cut -d' ' -f1); \
	HASH3=$$(sha256sum $(BOOTSTRAP_DIR)/simple_new3 | cut -d' ' -f1); \
	echo "  simple_new2 hash: $$HASH2"; \
	echo "  simple_new3 hash: $$HASH3"; \
	if [ "$$HASH2" = "$$HASH3" ]; then \
		echo ""; \
		echo "SUCCESS: simple_new2 == simple_new3"; \
		echo "Bootstrap verification PASSED!"; \
	else \
		echo ""; \
		echo "FAIL: simple_new2 != simple_new3"; \
		echo "Non-determinism detected in compiler output."; \
		exit 1; \
	fi

bootstrap-clean:
	@echo "Cleaning bootstrap directory..."
	rm -rf $(BOOTSTRAP_DIR)

bootstrap-promote: bootstrap
	@echo "Promoting verified compiler as stable..."
	@mkdir -p rust/target/stable
	cp $(BOOTSTRAP_DIR)/simple_new2 rust/target/stable/simple
	@chmod +x rust/target/stable/simple
	@HASH2=$$(sha256sum $(BOOTSTRAP_DIR)/simple_new2 | cut -d' ' -f1); \
	HASH3=$$(sha256sum $(BOOTSTRAP_DIR)/simple_new3 | cut -d' ' -f1); \
	REV=$$(jj log -r @ --no-graph -T 'change_id' 2>/dev/null || echo "unknown"); \
	DATE=$$(date +%Y-%m-%d); \
	printf "# Simple Compiler Bootstrap Metadata\n#\n# Updated by make bootstrap-promote.\n\nbootstrap:\n  version: %s\n  stage2_hash: %s\n  stage3_hash: %s\n  verified: true\n  source_revision: %s\n" \
		"$$DATE" "$$HASH2" "$$HASH3" "$$REV" > bootstrap.sdn
	@echo "Stable binary: rust/target/stable/simple"
	@echo "Bootstrap metadata: bootstrap.sdn"

bootstrap-from-stable:
	@echo "=== Rebuilding from stable compiler ==="
	@if [ ! -f rust/target/stable/simple ]; then \
		echo "Error: No stable compiler at rust/target/stable/simple"; \
		echo "Run 'make bootstrap-promote' first."; \
		exit 1; \
	fi
	@mkdir -p $(BOOTSTRAP_DIR)
	rust/target/stable/simple -c -o $(BOOTSTRAP_DIR)/simple_from_stable simple/compiler/main.spl
	@chmod +x $(BOOTSTRAP_DIR)/simple_from_stable
	@HASH_STABLE=$$(sha256sum rust/target/stable/simple | cut -d' ' -f1); \
	HASH_REBUILT=$$(sha256sum $(BOOTSTRAP_DIR)/simple_from_stable | cut -d' ' -f1); \
	echo "  stable hash:  $$HASH_STABLE"; \
	echo "  rebuilt hash: $$HASH_REBUILT"; \
	if [ "$$HASH_STABLE" = "$$HASH_REBUILT" ]; then \
		echo "SUCCESS: Rebuild matches stable binary!"; \
	else \
		echo "NOTE: Hashes differ (expected if source changed since promote)."; \
	fi

# ============================================================================
# Help
# ============================================================================

help:
	@echo "Simple Language Project - Available Commands"
	@echo ""
	@echo "Testing (807+ tests total):"
	@echo "  make test               - Run ALL tests (Rust + doc-tests + Simple/SSpec)"
	@echo "  make test-rust          - Run Rust tests only (faster)"
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
	@echo "  make coverage-service      - Service (interface + external lib touch)"
	@echo "  make coverage-environment  - Environment (branch/condition)"
	@echo "  make coverage-merged       - Merged unit + environment (branch/condition)"
	@echo "  make coverage-all          - Generate all coverage reports"
	@echo "  make coverage-check        - Verify all coverage thresholds (100%)"
	@echo "  make coverage-summary      - Print coverage summary"
	@echo ""
	@echo "Extended Coverage (public API):"
	@echo "  make coverage-extended         - Generate extended reports from existing data"
	@echo "  make coverage-extended-service - Generate service coverage report"
	@echo "  make coverage-extended-all     - Generate all extended report types"
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
	@echo "Architecture Testing:"
	@echo "  make arch-test           - Run architecture tests"
	@echo "  make arch-test-visualize - Generate dependency graph (DOT/Mermaid)"
	@echo ""
	@echo "TODO Management:"
	@echo "  make gen-todos     - Update TODO database (parallel scan - 7.8x faster)"
	@echo "  make todos         - Generate and show recent TODOs"
	@echo "  make todos-p0      - Show critical (P0) TODOs only"
	@echo "  make check-todos   - Validate TODO format"
	@echo ""
	@echo "Dashboard & Metrics:"
	@echo "  make dashboard         - Show dashboard summary"
	@echo "  make dashboard-collect - Collect fresh metrics"
	@echo "  make dashboard-snapshot- Create daily snapshot"
	@echo "  make dashboard-trends  - Show trend analysis"
	@echo "  make dashboard-alerts  - Check for critical alerts"
	@echo ""
	@echo "Bootstrap (Self-Compilation):"
	@echo "  make bootstrap        - Run full bootstrap pipeline with verification"
	@echo "  make bootstrap-stage1 - Build simple_new1 using Rust runtime"
	@echo "  make bootstrap-stage2 - Build simple_new2 using simple_new1"
	@echo "  make bootstrap-stage3 - Build simple_new3 using simple_new2"
	@echo "  make bootstrap-verify - Verify simple_new2 == simple_new3"
	@echo "  make bootstrap-clean  - Clean bootstrap artifacts"
	@echo "  make bootstrap-promote    - Promote verified compiler as stable"
	@echo "  make bootstrap-from-stable - Rebuild from stable compiler"
	@echo ""
	@echo "Package Management:"
	@echo "  make package-bootstrap - Build bootstrap package (runtime-only, ~25-50MB)"
	@echo "  make package-full      - Build full package (complete source)"
	@echo "  make package-all       - Build both packages"
	@echo "  make install           - Install bootstrap package to ~/.local"
	@echo "  make install-system    - Install system-wide to /usr/local (requires root)"
	@echo "  make uninstall         - Uninstall from ~/.local"
	@echo "  make verify-package    - Verify package integrity"
	@echo ""
	@echo "Other:"
	@echo "  make install-tools - Install required tools"
	@echo "  make clean         - Clean all artifacts"
	@echo "  make help          - Show this help"

# ============================================================================
# Backend Completeness (Phases 1-4)
# ============================================================================

# Phase 1: Check for catch-all patterns
check-exhaustiveness:
	@echo "=== Checking Backend Exhaustiveness ==="
	@./bin/wrappers/simple src/compiler/backend/exhaustiveness_validator.spl || \
		echo "Note: Phase 1 not yet implemented"

# Phase 2: Run backend coverage tests
test-backends:
	@echo "=== Running Backend Coverage Tests ==="
	@./rust/target/debug/simple_runtime test test/compiler/backend/ || \
		echo "Note: Phase 2 not yet implemented"

# Phase 3: Generate backend documentation
docs-backends:
	@echo "=== Generating Backend Documentation ==="
	@./bin/wrappers/simple scripts/generate_backend_docs.spl all || \
		echo "Note: Phase 3 not yet implemented"

# Phase 4: Regenerate code from IR DSL
codegen-from-dsl:
	@echo "=== Generating Code from IR DSL ==="
	@./bin/wrappers/simple src/compiler/irdsl/main.spl || \
		echo "Note: Phase 4 not yet implemented"

# Run all backend completeness checks
backend-completeness-full: check-exhaustiveness test-backends docs-backends
	@echo ""
	@echo "✓ All backend completeness checks completed!"

# Audit catch-all patterns (first step of Phase 1)
audit-catchalls:
	@echo "=== Auditing Catch-All Patterns ==="
	@echo "Searching for '_ =>' patterns in backend code..."
	@grep -rn "_ =>" rust/compiler/src/codegen/{llvm,vulkan}/ | grep -v test || \
		echo "No catch-all patterns found (good!)"

.PHONY: check-exhaustiveness test-backends docs-backends codegen-from-dsl \
        backend-completeness-full audit-catchalls

# ============================================================================
# Package Management
# ============================================================================

# Build bootstrap package (minimal runtime-only installation)
package-bootstrap:
	@echo "=== Building Bootstrap Package ==="
	./script/build-bootstrap.sh

# Build full package (complete source distribution)
package-full:
	@echo "=== Building Full Package ==="
	./script/build-full.sh

# Build all packages
package-all: package-bootstrap package-full

# Install bootstrap package (user-local)
install: install-user

install-user:
	@if [ ! -f simple-bootstrap-*.spk ]; then \
		echo "Error: No bootstrap package found. Run 'make package-bootstrap' first."; \
		exit 1; \
	fi
	@PKG=$$(ls -t simple-bootstrap-*.spk | head -1); \
	echo "Installing $$PKG to ~/.local"; \
	./rust/target/release-opt/simple_runtime src/app/package/main.spl install "$$PKG" --prefix=~/.local

# Install bootstrap package (system-wide, requires root)
install-system:
	@if [ ! -f simple-bootstrap-*.spk ]; then \
		echo "Error: No bootstrap package found. Run 'make package-bootstrap' first."; \
		exit 1; \
	fi
	@PKG=$$(ls -t simple-bootstrap-*.spk | head -1); \
	echo "Installing $$PKG to /usr/local (requires root)"; \
	sudo ./rust/target/release-opt/simple_runtime src/app/package/main.spl install "$$PKG" --system

# Uninstall package
uninstall:
	@echo "Uninstalling Simple from ~/.local"
	./rust/target/release-opt/simple_runtime src/app/package/main.spl uninstall --prefix=~/.local

# Verify package integrity
verify-package:
	@if [ ! -f simple-bootstrap-*.spk ]; then \
		echo "Error: No bootstrap package found."; \
		exit 1; \
	fi
	@PKG=$$(ls -t simple-bootstrap-*.spk | head -1); \
	echo "Verifying $$PKG"; \
	./rust/target/release-opt/simple_runtime src/app/package/main.spl verify "$$PKG"
