# Makefile Cleanup Analysis - February 2026

## Overview

The Makefile has 87 targets, many of which are now redundant with the Simple build system.

**Status:** The Simple build system (`src/app/build/`) now handles most functionality.

---

## Makefile vs Simple Build System

### ✅ Migrated to Simple Build (Can Remove from Makefile)

| Makefile Target | Simple Equivalent | Status |
|-----------------|-------------------|---------|
| `test` | `simple build test` | ✅ Migrated |
| `test-unit` | `simple build test --level=unit` | ✅ Migrated |
| `test-integration` | `simple build test --level=integration` | ✅ Migrated |
| `test-system` | `simple build test --level=system` | ✅ Migrated |
| `coverage` | `simple build coverage` | ✅ Migrated |
| `coverage-html` | `simple build coverage` | ✅ Migrated |
| `coverage-lcov` | `simple build coverage --format=lcov` | ✅ Migrated |
| `lint` | `simple build lint` | ✅ Migrated |
| `lint-fix` | `simple build lint --fix` | ✅ Migrated |
| `fmt` | `simple build fmt` | ✅ Migrated |
| `fmt-check` | `simple build fmt --check` | ✅ Migrated |
| `check` | `simple build check` | ✅ Migrated |
| `clean` | `simple build clean` | ✅ Migrated |
| `watch` | `simple build watch` | ✅ Migrated |

### ⏸️ Keep (Not Yet in Simple Build)

| Makefile Target | Reason | Keep? |
|-----------------|---------|-------|
| `test-rust` | Rust-specific tests | ✅ Yes |
| `duplication` | Code duplication check | ✅ Yes (PMD) |
| `coverage-json` | Raw JSON output | ⚠️ Maybe |
| `bootstrap` | Bootstrap build | ✅ In Simple |

### ❌ Obsolete (Can Remove)

| Target | Reason |
|--------|--------|
| `test-full-*` variants | Duplicates of `simple build test` |
| `coverage-extended-*` | Now in `simple coverage` tool |
| Multiple coverage check variants | Consolidated in Simple build |

---

## Recommended Action

### Phase 1: Add Deprecation Warnings
Add warnings to obsolete Makefile targets directing users to Simple build:

```makefile
test:
	@echo "WARNING: 'make test' is deprecated. Use 'simple build test' instead."
	@simple build test

lint:
	@echo "WARNING: 'make lint' is deprecated. Use 'simple build lint' instead."
	@simple build lint
```

### Phase 2: Update Documentation
Update all documentation to reference Simple build system instead of Make.

### Phase 3: Remove Obsolete Targets
After deprecation period, remove targets and keep only:
- Rust-specific operations
- CI/CD shortcuts
- Bootstrap helpers

---

## Minimal Makefile (Target)

```makefile
# Simple Language - Minimal Makefile
# Most functionality is in the Simple build system: simple build <command>

.PHONY: help
help:
	@echo "Simple Language Build"
	@echo ""
	@echo "Use 'simple build <command>' for most operations."
	@echo "See: simple build --help"
	@echo ""
	@echo "Makefile shortcuts:"
	@echo "  make bootstrap    Build minimal runtime"
	@echo "  make test-rust    Run Rust-only tests"
	@echo ""

.PHONY: bootstrap
bootstrap:
	@simple build --bootstrap

.PHONY: test-rust
test-rust:
	cd rust && cargo test --workspace

.DEFAULT_GOAL := help
```

This reduces from 87 targets to ~3, delegating everything else to Simple build system.
