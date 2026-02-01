# Makefile → Simple Build Migration Guide

**Date:** 2026-02-01
**Status:** In Progress (Phase 7)

## Overview

The Simple project is migrating from Makefile-based build orchestration to a native Simple build system. This guide helps you transition from `make` commands to `simple build` commands.

## Why Migrate?

- **Self-hosting**: Build system written in Simple itself
- **Cross-platform**: No reliance on Make (works on Windows without WSL)
- **Type-safe**: Build configuration in Simple with compile-time checks
- **Faster**: Parallel builds by default
- **Better errors**: Clear error messages and suggestions
- **Unified**: One tool for building, testing, and packaging

## Quick Reference

### Common Commands

| Makefile | Simple Build | Notes |
|----------|--------------|-------|
| `make test` | `simple build test` | Run all tests |
| `make test-rust` | `simple build test --rust-only` | Rust tests only |
| `make coverage` | `simple build coverage` | Generate coverage |
| `make coverage-html` | `simple build coverage --format=html` | HTML coverage |
| `make lint` | `simple build lint` | Run clippy |
| `make lint-fix` | `simple build lint --fix` | Auto-fix warnings |
| `make fmt` | `simple build fmt` | Format code |
| `make fmt-check` | `simple build fmt --check` | Check formatting |
| `make check` | `simple build check` | All checks |
| `make check-full` | `simple build check --full` | Full checks + coverage |
| `make build` | `simple build` | Debug build |
| `make build-release` | `simple build --release` | Release build |
| `make clean` | `simple build clean` | Clean artifacts |

### Test Commands

| Makefile | Simple Build | Notes |
|----------|--------------|-------|
| `make test-unit` | `simple build test --level=unit` | Unit tests |
| `make test-integration` | `simple build test --level=integration` | Integration tests |
| `make test-system` | `simple build test --level=system` | System tests |
| `make test-verbose` | `simple build test --verbose` | Verbose output |

### Coverage Commands

| Makefile | Simple Build | Notes |
|----------|--------------|-------|
| `make coverage-unit` | `simple build coverage --level=unit` | Unit coverage |
| `make coverage-integration` | `simple build coverage --level=integration` | Integration coverage |
| `make coverage-system` | `simple build coverage --level=system` | System coverage |
| `make coverage-all` | `simple build coverage --level=all` | All coverage |
| `make coverage-lcov` | `simple build coverage --format=lcov` | LCOV format |
| `make coverage-json` | `simple build coverage --format=json` | JSON format |

### Bootstrap Commands

| Makefile | Simple Build | Notes |
|----------|--------------|-------|
| `make bootstrap` | `simple build bootstrap` | Full 3-stage bootstrap |
| `make bootstrap-stage1` | `simple build bootstrap --stage=1` | Stage 1 only |
| `make bootstrap-verify` | `simple build bootstrap --verify` | With verification |

### Package Commands

| Makefile | Simple Build | Notes |
|----------|--------------|-------|
| `make package-bootstrap` | `simple build package-bootstrap` | Bootstrap package |
| `make package-full` | `simple build package-full` | Full source package |
| `make package-all` | `simple build package` | All packages |

## Build Profiles

Simple build uses typed build profiles instead of Makefile variables:

```bash
# Debug build (default)
simple build

# Release build (optimized)
simple build --release

# Bootstrap build (minimal size, for distribution)
simple build --bootstrap

# Or use explicit profile flag
simple build --profile=debug
simple build --profile=release
simple build --profile=bootstrap
```

## Feature Flags

```bash
# Makefile (environment variable)
FEATURES="feature1,feature2" make build

# Simple build (command-line flag)
simple build --features=feature1,feature2
```

## Configuration Files

### Makefile Variables

```makefile
# Makefile
COVERAGE_DIR := rust/target/coverage
SIMPLE_COV_THRESHOLD ?= 80
```

### Simple Build Configuration

```sdn
# simple.sdn
build:
  profile: debug
  coverage:
    threshold: 80
    output_dir: rust/target/coverage
  test:
    parallel: true
    timeout: 60
```

## Migration Steps

### 1. Install Simple Build System

```bash
# Build the Simple runtime (if not already built)
cd rust && cargo build
```

### 2. Test Simple Build Commands

Try the Simple build commands alongside Makefile commands to verify they work:

```bash
# Old way
make test

# New way (should produce same result)
simple build test
```

### 3. Update CI/CD

Update your CI/CD configuration to use Simple build:

```yaml
# .github/workflows/ci.yml
# Before:
- run: make test
- run: make coverage

# After:
- run: simple build test
- run: simple build coverage
```

### 4. Update Documentation

Update any documentation that references Makefile commands:

```markdown
# Before:
Run `make test` to run tests.

# After:
Run `simple build test` to run tests.
```

### 5. Team Communication

Notify your team about the migration and share this guide.

## Deprecation Timeline

- **Phase 1 (Current)**: Makefile shows deprecation warnings, both work
- **Phase 2 (TBD)**: CI/CD uses Simple build exclusively
- **Phase 3 (TBD)**: Makefile moved to `legacy/Makefile.deprecated`
- **Phase 4 (TBD)**: Makefile removed (Simple build only)

## Features Unique to Simple Build

### Parallel Execution

```bash
# Tests run in parallel by default
simple build test

# Explicit control
simple build test --parallel
simple build test --no-parallel
```

### Watch Mode (Future)

```bash
# Auto-rebuild on file changes
simple build watch
```

### Incremental Builds (Future)

```bash
# Only rebuild changed components
simple build --incremental
```

### Build Metrics

```bash
# Show build time breakdown
simple build --metrics

# Save metrics to file
simple build --metrics --output=metrics.json
```

## Troubleshooting

### Simple Build Command Not Found

```bash
# Ensure Simple runtime is built
cd rust && cargo build

# Ensure bin/wrappers/simple is executable
chmod +x bin/wrappers/simple

# Add to PATH (optional)
export PATH="$PWD/bin/wrappers:$PATH"
```

### Build Fails with Simple Build

```bash
# Try with verbose output
simple build --verbose

# Compare with Makefile output
make build 2>&1 | tee make.log
simple build --verbose 2>&1 | tee simple.log
diff make.log simple.log
```

### Different Behavior

If Simple build behaves differently from Makefile:

1. File a bug report with both commands and outputs
2. Continue using Makefile until fixed
3. Reference: `doc/bug/bug_report.md`

## Getting Help

- **Documentation**: `doc/build/`
- **Examples**: `doc/build/getting_started.md`
- **Issues**: File at project issue tracker
- **Ask**: Team communication channels

## FAQ

### Q: Can I still use Makefile?

**A:** Yes, during the migration period both work. Makefile shows deprecation warnings but remains functional.

### Q: What if I have custom Makefile targets?

**A:** Custom targets can be migrated to Simple build by creating custom commands in `src/app/build/`. See `doc/build/extending.md`.

### Q: Is Simple build slower than Makefile?

**A:** No, Simple build should be similar or faster due to parallel execution and better caching.

### Q: Can I mix Makefile and Simple build?

**A:** Yes, but not recommended. Choose one to avoid confusion.

### Q: What about Windows?

**A:** Simple build works on Windows without WSL. Makefile requires WSL or other Unix-like environment.

## See Also

- **Overview**: `doc/build/overview.md`
- **Getting Started**: `doc/build/getting_started.md`
- **Reference**: `doc/build/reference.md`
- **Internals**: `doc/build/internals.md`

---

**Last Updated:** 2026-02-01
**Migration Status:** Phase 1 (Deprecation Warnings Added)
