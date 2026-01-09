# SSpec Test Writing Skill

SSpec is Simple's BDD testing framework that generates documentation from tests.

## Quick Start

```simple
import std.spec

describe "Calculator":
    context "addition":
        it "adds two numbers":
            expect 2 + 2 == 4
```

Run: `simple test` or `cargo test -p simple-driver simple_stdlib`

## Test File Structure

### Location
```
simple/std_lib/test/
  unit/           # Fast, isolated (branch/condition coverage)
  integration/    # Public function touch (100%)
  system/         # Public type touch (100%)
```

### Naming
- Files: `*_spec.spl` or `*_test.spl`
- Describe: `describe "ClassName":`
- Context: `context "when condition":`
- Test: `it "does something":`

## BDD Syntax

### Groups & Tests

```simple
describe "Feature":
    """Optional docstring for generated docs."""

    context "when empty":
        it "returns zero":
            expect [].len() == 0

    context "when populated":
        it "has items":
            expect [1, 2, 3].len() == 3
```

### Hooks

| Hook | Scope | Order |
|------|-------|-------|
| `before_each:` | per test | outer -> inner |
| `after_each:` | per test | inner -> outer |
| `before_all:` | per group | once |
| `after_all:` | per group | once |

```simple
context "with setup":
    before_each:
        setup()
    after_each:
        cleanup()
    it "test":
        expect true
```

### Fixtures

```simple
# Lazy (memoized per test)
given_lazy :user, \:
    { name: "Alice" }

# Eager setup
given:
    setup_db()

# Named eager
given :db_connect, \:
    database.connect()
```

### Shared Contexts

```simple
context_def :as_admin:
    given_lazy :user, \:
        create(:user, :admin)

describe "Dashboard":
    context :as_admin:
        it "shows admin panel":
            expect user.admin?
```

## Matchers Reference

### Equality
```simple
expect value to eq expected
expect value to be expected
expect value to be_nil
```

### Comparison
```simple
expect 10 to gt 5       # greater than
expect 5 to lt 10       # less than
expect 10 to gte 10     # >=
expect 5 to lte 10      # <=
```

### Collections
```simple
expect [1, 2, 3] to include 2
expect [1, 2, 3] to have_length 3
expect [] to be_empty
```

### Strings
```simple
expect "hello world" to include_string "world"
expect "hello" to start_with "hel"
expect "hello" to end_with "lo"
expect "" to be_blank
```

### Errors
```simple
expect_raises ValueError:
    raise ValueError("bad")

expect_raises:
    risky_operation()
```

### Negation
```simple
expect value not_to eq other
expect [1] not_to be_empty
```

## Gherkin-Style (System Tests)

```simple
examples addition:
    a    b    result
    1    2    3
    10   20   30

feature Calculator:
    scenario outline Adding:
        given fresh calculator:
        when add <a>:
        when add <b>:
        then value is <result>:
        examples addition:
```

## Documentation Generation

SSpec uses triple-quoted strings (`"""`) as **full markdown docstrings** that get extracted into generated documentation.

### Docstring Format

```simple
"""
# Feature Name Specification

**Status:** Stable
**Feature IDs:** #10-19
**Keywords:** syntax, parsing
**Topics:** core-language

## Overview

Full markdown content supported here including:
- Bullet lists
- **Bold** and *italic*
- Code blocks with ```simple ... ```
- Tables

## Related Specifications

- [Types](types.md) - Type annotations
- [Functions](functions.md) - Function syntax
- See also: [External Doc](https://example.com)

## Key Concepts

| Concept | Description |
|---------|-------------|
| Tokens  | Lexical units |
| AST     | Syntax tree  |
"""
```

### Making Links

Standard markdown link syntax works inside docstrings:

```simple
"""
## Links in Documentation

### Internal Links (relative)
- [Types Specification](types.md)
- [Functions](functions.md#pattern-matching)
- [See Overview](#overview)

### External Links
- [Rust Documentation](https://doc.rust-lang.org)
- [GitHub Issue](https://github.com/org/repo/issues/123)

### Anchor Links
Use `{#anchor-name}` for custom anchors:

## Section Name {#custom-anchor}

Then link: [Go to section](#custom-anchor)
"""
```

### Doc Structure in Specs

```simple
"""
# Feature Name

**Status:** Stable
**Feature IDs:** #10-19

## Overview
High-level description.

## Related Specifications
- [Types](types.md) - Type system
- [Memory](memory.md) - Ownership rules
"""

## Test: Basic Usage

"""
### Scenario: Simple case
Validates basic behavior.

See [Types spec](types.md) for type details.
"""
test "basic test":
    assert true
```

### Generate Docs

```bash
# Using gen-sspec-docs binary
cargo run --bin gen-sspec-docs -- tests/specs/*_spec.spl

# Output to specific directory
cargo run --bin gen-sspec-docs -- tests/specs/*.spl --output doc/spec/generated/

# Using spec_gen.py script
python scripts/spec_gen.py --input tests/specs/syntax_spec.spl
```

### Generated Output Location

```
doc/spec/generated/
  README.md           # Index with links to all specs
  syntax.md           # Generated from syntax_spec.spl
  types.md            # Generated from types_spec.spl
  ...
```

### Generated README Structure

The generator creates an index with:
- Quick navigation by category
- Links to each spec: `[Syntax Specification](syntax.md)`
- Status badges, test counts, feature IDs
- Symbol references with anchor links

## Running Tests

```bash
# All stdlib tests
cargo test -p simple-driver simple_stdlib

# By layer
cargo test -p simple-driver simple_stdlib_unit
cargo test -p simple-driver simple_stdlib_system

# Specific test
cargo test -p simple-driver simple_stdlib_unit_core_string_spec

# Direct interpreter
./target/debug/simple simple/std_lib/test/unit/core/arithmetic_spec.spl

# With options
simple test --tag slow
simple test --fail-fast
simple test --match "Stack when empty"
```

## Coverage Measurement

### Quick Commands

```bash
make coverage              # HTML report -> target/coverage/html/
make coverage-summary      # Console summary
make coverage-all          # All report types
```

### By Test Level

```bash
# Unit: branch/condition (100% target)
make coverage-unit

# Integration: public function touch (100% target)
make coverage-integration

# System: class/struct method touch (100% target)
make coverage-system

# Merged: unit + environment
make coverage-merged
```

### Full Test Mode

```bash
# Run tests + generate all reports
make test-full

# Quick (no extended reports)
make test-full-quick

# With threshold check
make test-full-check
SIMPLE_COV_THRESHOLD=80 make test-full-check
```

### Coverage Thresholds

```bash
make coverage-check        # Verify all thresholds (100%)
make coverage-check-unit   # Unit only
make coverage-check-system # System only
```

### Reports Location

```
target/coverage/
  html/index.html          # Visual HTML report
  coverage.json            # Machine-readable
  unit/                    # Unit coverage
  integration/             # Integration coverage
  system/                  # System coverage
  extended/                # Extended analysis
```

## Code Duplication Detection

### Quick Check

```bash
make duplication           # Full report -> target/duplication/
```

### Configuration

Uses `.jscpd.json`:
- Threshold: 2%
- Min lines: 5
- Min tokens: 50

### Manual Run

```bash
# Rust source
jscpd src/ --reporters html,console --output target/duplication \
    --min-lines 5 --min-tokens 50 --format rust

# Simple source
jscpd simple/ --reporters html,console --output target/duplication \
    --min-lines 5 --min-tokens 50 --format simple
```

### Fallback (No jscpd)

```bash
make duplication-simple    # Basic pattern detection
```

## Pre-Commit Check

```bash
make check                 # fmt + lint + test
make check-full            # + coverage + duplication
```

## Install Tools

```bash
make install-tools         # cargo-llvm-cov, cargo-audit, cargo-outdated
npm install -g jscpd       # Duplication detection
```

## Critical Rules

- NEVER add `#[ignore]` without user approval
- NEVER skip failing tests as a "fix"
- ALWAYS fix root cause or ask user
- One assertion concept per test
- Clear test names: `it "adds two positive numbers":` not `it "works":`

## Lean Verification Integration

SSpec tests can reference formal verification in docstrings:

```simple
"""
### Lean Verification

This feature is verified in:
- `verification/TypeInference.lean` - Soundness proof
- `verification/MixinSubstitution.lean` - Type safety

**Properties Verified:**
1. Type substitution preserves well-typedness
2. Mixin application is associative

See [architecture skill](/architecture) for verification workflow.
"""
```

Generate Lean from verified code:
```bash
simple gen-lean compare           # Check alignment
simple gen-lean write --force     # Regenerate Lean files
```

## See Also

- `doc/spec/testing/testing_bdd_framework.md` - Full BDD spec
- `doc/sspec_format.md` - SSpec format details
- `doc/test.md` - Test policy
- `doc/spec/testing/sdoctest.md` - Documentation testing
- `doc/formal_verification.md` - Lean verification docs
- `/architecture` skill - Lean codegen, dependency analysis
