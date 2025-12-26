# Feature: Code Quality Tools (Coverage & Duplication)

**Infrastructure Feature**
- **Importance**: 4/5
- **Difficulty**: 1/5
- **Status**: COMPLETED

## Goal

Set up tooling for:
- Test coverage measurement
- Code duplication detection
- Linting and formatting

## Tools Configured

### Coverage: `cargo-llvm-cov`
- Generates accurate coverage reports
- Supports HTML, LCOV, JSON output
- Install: `cargo install cargo-llvm-cov`

### Duplication: `jscpd`
- Detects copy-paste code patterns
- Configurable thresholds (5 lines / 50 tokens default)
- Fallback to grep-based detection if not installed
- Install: `npm install -g jscpd`

### Linting: `cargo clippy`
- Built-in, no extra install needed

## Files Created

| File | Purpose |
|------|---------|
| `Makefile` | Build automation with targets for all tools |
| `.jscpd.json` | Configuration for duplication detection |
| `architecture.md` | Updated with Code Quality Tools section |

## Makefile Targets

```bash
# Testing
make test              # Run all tests
make test-verbose      # Run tests with output

# Coverage
make coverage          # HTML report in target/coverage/html/
make coverage-summary  # Console summary
make coverage-lcov     # LCOV format for CI

# Duplication
make duplication       # Full jscpd report
make duplication-simple # Grep-based fallback

# Linting
make lint              # Clippy with warnings as errors
make lint-fix          # Auto-fix
make fmt               # Format code
make fmt-check         # Check formatting

# Combined
make check             # fmt + lint + test
make check-full        # All checks + coverage + duplication

# Setup
make install-tools     # Install all required tools
```

## Initial Duplication Analysis

Found potential areas for refactoring:
- `push_struct` function duplicated
- Several large functions (>50 lines) that could be broken down
- Struct definitions appearing in multiple test files

## Usage

```bash
# Quick check before commit
make check

# Full analysis for code review
make check-full

# Install all tools first time
make install-tools
```
