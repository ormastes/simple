# Simple Build System - Getting Started Guide

**Quick Start:** Build, test, and package your Simple projects using `simple build`

## Prerequisites

- Rust toolchain (for building the Simple runtime)
- Simple runtime (see Installation)
- Optional: cargo-llvm-cov (for coverage)

## Installation

```bash
# 1. Clone the repository
git clone https://github.com/simple-lang/simple.git
cd simple

# 2. Build the Simple runtime (first-time setup)
cd rust && cargo build
# After initial build, use: simple build

# 3. Add bin/wrappers to PATH (optional)
export PATH="$PWD/bin/wrappers:$PATH"
```

## Basic Usage

### Build Your Project

```bash
# Debug build (default)
simple build

# Release build (optimized)
simple build --release

# Bootstrap build (minimal size, ~9 MB)
simple build --bootstrap
```

### Run Tests

```bash
# Run all tests (Rust + doc-tests + Simple/SSpec)
simple build test

# Run with parallel execution
simple build test --parallel

# Filter tests
simple build test --filter=pattern
```

### Generate Coverage

```bash
# HTML coverage report
simple build coverage

# Coverage by level
simple build coverage --level=unit
simple build coverage --level=integration
simple build coverage --level=system

# LCOV format
simple build coverage --format=lcov
```

### Quality Checks

```bash
# Run linter (clippy)
simple build lint

# Auto-fix lint warnings
simple build lint --fix

# Format code (rustfmt)
simple build fmt

# Check formatting without changes
simple build fmt --check

# Run all checks (lint + fmt + test)
simple build check
```

### Advanced Features

```bash
# Watch mode (auto-rebuild on file changes)
simple build watch

# Incremental build (use cache)
simple build incremental

# Show build metrics
simple build metrics

# Build with metrics tracking
simple build --metrics
```

### Bootstrap & Package

```bash
# Run 3-stage bootstrap pipeline
simple build bootstrap

# Create bootstrap package (~10 MB)
simple build package-bootstrap

# Create full source package (~50 MB)
simple build package-full
```

## Examples

### Development Workflow

```bash
# 1. Make changes to code
vim src/main.spl

# 2. Build and test
simple build
simple build test

# 3. Check quality
simple build lint
simple build fmt

# 4. Run all checks before commit
simple build check
```

### CI/CD Workflow

```bash
# Full validation pipeline
simple build check --full
simple build coverage --threshold=80
simple build bootstrap --verify
```

### Release Workflow

```bash
# 1. Run full checks
simple build check --full

# 2. Build release binary
simple build --release

# 3. Create packages
simple build package-bootstrap
simple build package-full

# 4. Verify packages
ls -lh simple-*.tar.gz
sha256sum simple-*.tar.gz
```

## Configuration

### Build Profiles

| Profile | Size | Optimization | Use Case |
|---------|------|--------------|----------|
| `debug` | 423 MB | None | Development (fast compile) |
| `release` | 40 MB | Full | Production (optimized) |
| `bootstrap` | 9.3 MB | Size | Distribution (minimal) |

### Test Levels

| Level | Tests | Coverage Type |
|-------|-------|---------------|
| `unit` | Workspace tests | Branch/condition |
| `integration` | Integration tests | Public function touch |
| `system` | System tests | Class/struct touch |
| `all` | All levels combined | Complete |

### Coverage Formats

| Format | Output | Use Case |
|--------|--------|----------|
| `html` | HTML report | Visual browsing |
| `lcov` | LCOV format | CI/CD integration |
| `json` | JSON data | Programmatic analysis |
| `text` | Terminal output | Quick checks |

## Common Tasks

### Before Committing

```bash
# Quick pre-commit check
simple build check

# Full pre-commit validation
simple build lint
simple build fmt
simple build test
```

### Continuous Integration

```yaml
# .github/workflows/ci.yml
- name: Build
  run: simple build --release

- name: Test
  run: simple build test

- name: Coverage
  run: simple build coverage --threshold=80

- name: Quality
  run: simple build check
```

### Local Development

```bash
# Terminal 1: Watch mode
simple build watch

# Terminal 2: Edit code
# Builds happen automatically on save
```

## Troubleshooting

### "simple_runtime not found"

**Problem:** The wrapper can't find the runtime binary

**Solution:**
```bash
simple build
# Or for first-time setup: cd rust && cargo build
```

### "cargo-llvm-cov not found"

**Problem:** Coverage tool not installed

**Solution:**
```bash
cargo install cargo-llvm-cov
```

### Build Fails

**Problem:** Compilation errors

**Solution:**
```bash
# Check error output
simple build --verbose

# Clean and rebuild
simple build clean
simple build
```

### Tests Fail

**Problem:** Some tests failing

**Solution:**
```bash
# Run specific test file
simple build test path/to/test.spl

# Run with verbose output
simple build test --verbose

# Run with fail-fast to stop on first failure
simple build test --fail-fast
```

## Migration from Makefile

If you're currently using `make`, see the [Migration Guide](../migration_guide.md).

**Quick reference:**

| Makefile | Simple Build |
|----------|--------------|
| `make test` | `simple build test` |
| `make coverage` | `simple build coverage` |
| `make lint` | `simple build lint` |
| `make fmt` | `simple build fmt` |
| `make check` | `simple build check` |
| `make build` | `simple build` |
| `make clean` | `simple build clean` |

## Next Steps

- **Read the Reference:** [Complete command reference](reference.md)
- **Understand Internals:** [Implementation details](internals.md)
- **See Examples:** [More examples](../examples/)
- **Get Help:** File issues on GitHub

## Tips & Best Practices

### Performance

- Use `--incremental` for faster rebuild times
- Use `--parallel` for faster test execution
- Use `watch` mode during development

### Quality

- Run `simple build check` before every commit
- Use `simple build lint --fix` to auto-fix warnings
- Maintain high coverage with `simple build coverage --threshold=80`

### CI/CD

- Use `simple build check --full` in CI pipelines
- Generate coverage reports for tracking trends
- Create packages automatically on releases

### Debugging

- Use `--verbose` flag for detailed output
- Check build metrics with `--metrics`
- Review logs in `rust/target/` directory

## Resources

- **Documentation:** `doc/build/`
- **Examples:** `doc/examples/`
- **Tests:** `test/build/`
- **Source:** `src/app/build/`

## Getting Help

- **Documentation Issues:** Check `doc/build/troubleshooting.md`
- **Bug Reports:** File on GitHub with reproduction steps
- **Feature Requests:** Discuss on GitHub Discussions
- **Questions:** Ask on community forums

---

**Last Updated:** 2026-02-01
**Version:** 1.0.0 (Complete - All 8 phases)
