# Directory Restructure Migration Plan

**Date:** 2026-01-21
**Status:** Planning
**Goal:** Reorganize project to Simple-language-oriented directory structure

## Overview

This migration plan restructures the project to be **Simple-language-oriented** while maintaining full build and test capability at every step.

### Target Structure

```
simple/
├── bin/
│   ├── rust/           # Compiled binaries
│   └── simple/         # Symlinks to rust binaries
├── src/
│   ├── rust/           # Rust compiler source
│   ├── app/            # Applications (formatter, linter, etc.)
│   └── lib/            # Libraries
│       └── std/        # Standard library
├── test/
│   ├── unit/           # Simple language unit tests
│   ├── integration/    # Simple language integration tests
│   ├── system/         # Simple language system tests
│   ├── environment/    # Test orchestration
│   ├── rust/           # Rust compiler tests
│   ├── app/            # Application tests
│   ├── lib/            # Library tests
│   │   ├── std/        # Std library tests
│   │   └── _cross_lib/ # Cross-library tests
│   ├── fixtures/       # Shared test data
│   └── mock/           # Mock infrastructure
├── bench/              # Benchmarks
├── fuzz/               # Fuzzing
├── src/i18n/               # Internationalization (KEEP AT ROOT)
└── scripts/            # Build scripts
```

## Key Principles

1. **Every step is buildable** - `cargo build --workspace` must succeed
2. **Every step passes all tests** - `make test` must pass
3. **Commit after each step** - Easy rollback if needed
4. **Copy before move** - Keep old paths working temporarily
5. **Incremental** - Small, verifiable changes

---

## Phase 1: Preparation (Non-Breaking)

### Step 1.1: Create New Directory Structure

**Duration:** 5 minutes

```bash
# Create directories
mkdir -p bin/{rust,simple}
mkdir -p scripts
mkdir -p src/lib/std
mkdir -p test/{unit,integration,system,environment,rust,app,lib,fixtures,mock}
mkdir -p test/lib/{std,_cross_lib}
mkdir -p test/lib/std/{unit,integration,system,fixtures}
mkdir -p test/lib/_cross_lib/{integration,system}
mkdir -p test/app/{formatter,linter,vscode_extension}
mkdir -p bench fuzz
```

**Verify:**
```bash
make check       # Should pass - no changes to source yet
```

**Commit:** `feat: create new directory structure for migration`

---

### Step 1.2: Create Link Scripts

**Duration:** 15 minutes

Create three files:
- `scripts/link-bins.sh`
- `scripts/link-bins.ps1`
- `scripts/link-bins.bat`

See `doc/guide/directory_structure.md` for full script content.

```bash
chmod +x scripts/*.sh
```

**Update Makefile:**
```makefile
.PHONY: link-bins

link-bins:
ifeq ($(OS),Windows_NT)
	@powershell -ExecutionPolicy Bypass -File scripts/link-bins.ps1
else
	@bash scripts/link-bins.sh
endif
```

**Verify:**
```bash
make check
make link-bins   # Should create symlinks
```

**Commit:** `feat: add binary linking scripts for cross-platform support`

---

## Phase 2: Move Tests (Test Directory Reorganization)

### Step 2.1: Move Rust Unit Tests

**Duration:** 10 minutes

```bash
cp -r tests/unit test/rust/
cp tests/Cargo.toml test/rust/
```

**Update:** `test/rust/Cargo.toml` - ensure paths are correct

**Update:** Root `Cargo.toml`
```toml
[workspace]
members = [
    # ... existing ...
    "test/rust",
]
```

**Update:** `Makefile`
```makefile
test-unit:
	cargo test -p simple-tests --test unit
```

**Verify:**
```bash
cargo build --workspace
make test-unit
```

**Commit:** `refactor: move rust unit tests to test/rust/unit/`

---

### Step 2.2: Move Rust Integration Tests

**Duration:** 10 minutes

```bash
cp -r tests/integration test/rust/
```

**Update:** `test/rust/Cargo.toml`
```toml
[[test]]
name = "integration"
path = "integration/main.rs"
harness = false
```

**Update:** `Makefile`
```makefile
test-integration:
	cargo test -p simple-tests --test integration
```

**Verify:**
```bash
cargo build --workspace
make test-integration
```

**Commit:** `refactor: move rust integration tests to test/rust/integration/`

---

### Step 2.3: Move Rust System Tests

**Duration:** 10 minutes

```bash
cp -r tests/system test/rust/
```

**Update:** `test/rust/Cargo.toml`
```toml
[[test]]
name = "system"
path = "system/main.rs"
harness = false
```

**Update:** `Makefile`
```makefile
test-system:
	cargo test -p simple-tests --test system
```

**Verify:**
```bash
cargo build --workspace
make test-system
```

**Commit:** `refactor: move rust system tests to test/rust/system/`

---

### Step 2.4: Move Rust Environment Tests

**Duration:** 10 minutes

```bash
cp -r tests/environment test/rust/
```

**Update:** `test/rust/Cargo.toml`
```toml
[[test]]
name = "environment"
path = "environment/main.rs"
harness = false
```

**Update:** `Makefile`
```makefile
test-environment:
	cargo test -p simple-tests --test environment
```

**Verify:**
```bash
cargo build --workspace
make test-environment
make test
```

**Commit:** `refactor: move rust environment tests to test/rust/environment/`

---

### Step 2.5: Remove Old tests/ Directory

**Duration:** 5 minutes

```bash
# Verify new location works
make test

# Remove old directory
rm -rf tests/
```

**Update:** Root `Cargo.toml` - remove "tests" from members if present

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: remove old tests/ directory`

---

### Step 2.6: Move Simple Language Tests

**Duration:** 15 minutes

```bash
cp -r simple/test/unit test/
cp -r simple/test/integration test/
cp -r simple/test/system test/
cp -r simple/test/environment test/
```

**Update:** Find and update test discovery in `build.rs`:
```rust
let test_dir = Path::new("test");  // Changed from "simple/test"
```

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: move simple language tests to test/`

---

### Step 2.7: Move Library Tests

**Duration:** 20 minutes

```bash
cp -r simple/std_lib/test/unit test/lib/std/
cp -r simple/std_lib/test/integration test/lib/std/
cp -r simple/std_lib/test/system test/lib/std/
cp -r simple/std_lib/test/fixtures test/lib/std/
```

**Update:** Discovery in `build.rs`
```rust
let stdlib_test_dir = Path::new("test/lib/std");
```

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: move stdlib tests to test/lib/std/`

---

### Step 2.8: Remove Old Simple test/ Directories

**Duration:** 5 minutes

```bash
# Verify all tests pass
make test

# Remove old directories
rm -rf simple/test
rm -rf simple/std_lib/test
```

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: remove old simple test directories`

---

## Phase 3: Move Source Code

### Step 3.1: Move Rust Source to src/rust/

**Duration:** 10 minutes per crate

```bash
mkdir -p src/rust

# Move one crate at a time
mv src/parser src/rust/
```

**Update:** Root `Cargo.toml`
```toml
[workspace]
members = [
    "src/rust/parser",
    # ... update all other crates ...
]
```

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: move parser to src/rust/parser`

**Repeat for:**
- compiler
- type
- driver
- runtime
- common
- loader
- diagnostics
- util

Each is a separate commit.

---

### Step 3.2: Move Applications

**Duration:** 15 minutes

```bash
cp -r simple/app src/
```

**Update:** Root `Cargo.toml` if apps are workspace members
```toml
[workspace]
members = [
    # ... existing ...
    "src/app/formatter",
    "src/app/linter",
]
```

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: move applications to src/app/`

---

### Step 3.3: Restructure Standard Library

**Duration:** 20 minutes

```bash
mkdir -p src/lib/std
cp -r simple/std_lib/* src/lib/std/
```

**Update:** Import paths and discovery logic

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: move standard library to src/lib/std/`

---

### Step 3.4: Remove Old simple/ Directories

**Duration:** 5 minutes

```bash
# Verify everything works
make check

# Remove old directories
rm -rf simple/app
rm -rf simple/std_lib
```

**Verify:**
```bash
cargo build --workspace
make test
```

**Commit:** `refactor: remove old simple/ source directories`

---

## Phase 4: Add New Features

### Step 4.1: Add Contract Tests

**Duration:** 30 minutes

```bash
mkdir -p test/rust/contract
```

Create `test/rust/contract/main.rs`

Move existing contract tests from:
- `src/parser/tests/contract_tests.rs`
- `src/compiler/src/mir/lower/tests/contract_tests.rs`

To `test/rust/contract/`

**Update:** `test/rust/Cargo.toml`

**Verify:**
```bash
cargo test -p simple-tests --test contract
make test
```

**Commit:** `feat: add consolidated contract tests`

---

### Step 4.2: Add Deployment Tests

**Duration:** 30 minutes

Create:
- `test/rust/deployment/main.rs`
- `test/rust/deployment/smoke_tests.rs`
- `test/rust/deployment/linkage_tests.rs`

**Verify:**
```bash
cargo test -p simple-tests --test deployment
make test
```

**Commit:** `feat: add deployment verification tests`

---

### Step 4.3: Add Mock Library for Simple

**Duration:** 1 hour

Create:
- `test/mock/simple/lib.spl`
- `test/mock/simple/stub.spl`
- `test/mock/simple/mock.spl`
- `test/mock/simple/verify.spl`

**Verify:**
```bash
make test
```

**Commit:** `feat: add mock library for Simple language`

---

### Step 4.4: Add Mock Prevention for Simple

**Duration:** 30 minutes

Update `test/system/__init__.spl`:
```simple
fn enforce_no_mocks():
    # Check for mock imports
    # Fail if any mock library is imported
    pass

enforce_no_mocks()
```

**Verify:**
```bash
make test
```

**Commit:** `feat: add mock prevention framework for Simple system tests`

---

### Step 4.5: Add Benchmarks

**Duration:** 1 hour

Create:
- `bench/Cargo.toml`
- `bench/parser_bench.rs`
- `bench/compiler_bench.rs`
- `bench/runtime_bench.rs`

**Update:** Root `Cargo.toml`
**Update:** `Makefile` - add `bench` target

**Verify:**
```bash
cargo build --workspace
make bench
```

**Commit:** `feat: add benchmark suite`

---

### Step 4.6: Add Shared Fixtures

**Duration:** 30 minutes

```bash
mkdir -p test/fixtures/{rust,simple,smf,data}
cp -r test/lib/std/fixtures/* test/fixtures/simple/
```

Update test files to reference new fixture locations.

**Verify:**
```bash
make test
```

**Commit:** `feat: add shared test fixtures directory`

---

## Phase 5: Final Cleanup

### Step 5.1: Update All Documentation

**Duration:** 1 hour

Update:
- `README.md`
- `doc/guide/test.md`
- `CLAUDE.md`
- `.gitignore`

**Verify:**
```bash
make check
```

**Commit:** `docs: update documentation for new directory structure`

---

### Step 5.2: Update CI/CD

**Duration:** 30 minutes

Update:
- `.github/workflows/*.yml`
- CI scripts

**Verify:**
```bash
make check-full
```

**Commit:** `ci: update CI/CD for new directory structure`

---

### Step 5.3: Final Verification

**Duration:** 15 minutes

```bash
# Clean build
cargo clean
rm -rf target

# Full rebuild
cargo build --workspace

# All tests
make test

# Full check
make check-full

# Benchmarks
make bench

# Link binaries
make link-bins

# Test binaries
bin/simple/simple --version
```

**Commit:** `refactor: complete migration to new directory structure`

---

## Rollback Plan

If any step fails:

```bash
# Rollback using git
git reset --hard HEAD~1

# Or manually undo the specific step
```

---

## Summary

### Timeline Estimate

| Phase | Duration | Steps |
|-------|----------|-------|
| Phase 1: Preparation | 20 min | 2 |
| Phase 2: Move Tests | 2 hours | 8 |
| Phase 3: Move Source | 2 hours | 4 (multiple commits per step) |
| Phase 4: Add Features | 4 hours | 6 |
| Phase 5: Cleanup | 2 hours | 3 |
| **Total** | **~10 hours** | **23 main steps** |

### Verification Checklist

After completion, verify:

- [ ] `cargo build --workspace` - succeeds
- [ ] `make test` - all tests pass
- [ ] `make check` - fmt + lint + test pass
- [ ] `make check-full` - full verification passes
- [ ] `make bench` - benchmarks run
- [ ] `make link-bins` - creates symlinks
- [ ] `bin/simple/simple --version` - binary works
- [ ] CI/CD passes
- [ ] Documentation updated

---

## Next Steps After Migration

1. Write comprehensive testing guide (`doc/guide/testing.md`)
2. Create directory structure quick reference (`doc/guide/directory_structure.md`)
3. Implement missing features:
   - Mock library for Simple
   - Mock prevention enforcement
   - Coverage for Simple source files
   - Property-based testing
   - Snapshot testing
   - Mutation testing

---

**Status:** Ready to begin
**Start Date:** TBD
**Completion Date:** TBD
