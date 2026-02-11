# Testing Core Simple Modules

**Date:** 2026-02-11
**Purpose:** Guide for testing and improving coverage of core Simple library (`src/core/*.spl`)

---

## Overview

The **core Simple library** (`src/core/`) contains the foundational compiler components written in Simple:
- **Lexer** (`lexer.spl`, `lexer_types.spl`, `lexer_struct.spl`) - Tokenization
- **Parser** (`parser.spl`) - AST construction
- **AST** (`ast.spl`, `ast_types.spl`) - Abstract syntax tree
- **Types** (`types.spl`) - Type system
- **MIR** (`mir.spl`, `mir_types.spl`) - Mid-level IR
- **Interpreter** (`interpreter/*.spl`) - Runtime execution
- **Compiler** (`compiler/*.spl`) - Code generation

These modules are tested using **full Simple** test framework (SSpec).

---

## Test Structure

### Test Location
```
test/unit/core/
├── lexer_spec.spl           # Lexer unit tests
├── parser_spec.spl          # Parser unit tests
├── ast_spec.spl             # AST tests
├── types_spec.spl           # Type system tests
├── mir_spec.spl             # MIR tests
├── interpreter/             # Interpreter tests
│   ├── env_spec.spl
│   ├── eval_spec.spl
│   ├── ops_spec.spl
│   ├── value_spec.spl
│   └── jit_spec.spl
├── branch_coverage_1_spec.spl through branch_coverage_25_spec.spl
├── auto_coverage_1_spec.spl through auto_coverage_12_spec.spl
└── *_coverage_spec.spl      # Various coverage tests
```

### Running Tests

```bash
# Run all core tests
bin/simple test test/unit/core/

# Run specific test file
bin/simple test test/unit/core/lexer_spec.spl

# Run with coverage tracking
bin/simple test test/unit/core/ --coverage

# Run only slow tests
bin/simple test test/unit/core/ --only-slow

# List all tests
bin/simple test test/unit/core/ --list
```

---

## Coverage Tracking

### Coverage Types

Simple supports multiple coverage levels:

1. **Decision/Branch Coverage** - Each if/match branch taken both ways
2. **Condition Coverage** - Each boolean condition evaluates to true AND false
3. **MC/DC Coverage** - Each condition independently affects decision (safety-critical)

### Enabling Coverage

Coverage is enabled by:
1. Running tests with `--coverage` flag
2. Setting `SIMPLE_COVERAGE=1` environment variable
3. Coverage data written to `.coverage/` directory

### Coverage Reports

After running with `--coverage`:

```
.coverage/
├── coverage.sdn         # Raw coverage data (SDN format)
├── summary.md          # Per-file coverage summary
└── uncovered.md        # Files with coverage gaps
```

### Coverage Summary Format

```markdown
| Metric | Covered | Total | Percentage |
|--------|---------|-------|------------|
| Decisions | 245 | 300 | 82% |
| Conditions | 180 | 220 | 82% |
```

### Per-File Coverage

Shows which modules need more test coverage:
```markdown
| File | Dec Covered | Dec Total | Dec % | Cond Covered | Cond Total | Cond % |
|------|-------------|-----------|-------|--------------|------------|--------|
| src/core/lexer.spl | 45 | 50 | 90% | 60 | 65 | 92% |
```

---

## Writing Coverage Tests

### Basic Structure

```simple
"""
# Branch Coverage Test Suite

**Feature IDs:** #BRANCH
**Category:** Testing
**Status:** Implemented

## Overview

Tests covering all conditional branches in [module name].
"""

use std.spec.{check}

describe "Module Name - Branch Coverage":
    it "tests branch A - true path":
        val result = some_function_that_returns_true()
        check(result == true)

    it "tests branch A - false path":
        val result = some_function_that_returns_false()
        check(result == false)
```

### Coverage Test Categories

1. **Conditional Branches** - `if/elif/else` all paths
2. **Match Statements** - All pattern cases including default
3. **Loop Branches** - Loop body executed/skipped, `break`/`continue`
4. **Boolean Expressions** - All combinations of `and`/`or`/`not`
5. **Comparison Operators** - True/false for `==`, `!=`, `<`, `>`, `<=`, `>=`
6. **Option Types** - `Some` and `nil` paths
7. **Collection Operations** - Empty/non-empty arrays, valid/invalid indices
8. **Error Paths** - Edge cases and error conditions

### Example: Testing Lexer Branches

```simple
describe "Lexer - String Tokenization":
    it "handles regular string":
        val tokens = lex("\"hello\"")
        check(tokens[0].kind == TOKEN_STRING)

    it "handles empty string":
        val tokens = lex("\"\"")
        check(tokens[0].kind == TOKEN_STRING)
        check(tokens[0].value == "")

    it "handles string with escape sequences":
        val tokens = lex("\"hello\\nworld\"")
        check(tokens[0].value.contains("\\n"))

    it "handles unterminated string - error path":
        val tokens = lex("\"hello")
        check(tokens[0].kind == TOKEN_ERROR)
```

---

## Current Coverage Status

### Seed Compiler Coverage (C++)

The bootstrap seed compiler (`seed/seed.cpp`) coverage:
- **seed.cpp:** 87.21% branch coverage (2086/2392 branches)
- **runtime.c:** 99.26% branch coverage (405/408 branches)
- **c_runtime.c:** 100% branch coverage (234/234 branches)

Run seed coverage:
```bash
bash seed/run_coverage.sh
# Report: seed/.build-coverage/report/index.html
```

### Simple Core Coverage

Currently investigating why Simple code coverage shows 0 decisions tracked.
Possible causes:
- Coverage instrumentation only works for compiled mode, not interpreter
- Runtime coverage tracking (`rt_coverage_*`) needs compiler support
- Coverage tracking may require AOT compilation with instrumentation

---

## Improving Coverage

### Strategy

1. **Identify gaps** - Check `.coverage/uncovered.md` after test run
2. **Analyze branches** - Find untested code paths in source
3. **Write tests** - Create `branch_coverage_N_spec.spl` files
4. **Verify** - Re-run with `--coverage` and check improvement
5. **Document** - Update test descriptions with feature IDs

### Target Areas for New Tests

Based on seed.cpp coverage gaps (~13% uncovered):

1. **Error Handling** - Parser/lexer error recovery paths
2. **Edge Cases** - Empty input, max limits, boundary conditions
3. **Complex Expressions** - Deeply nested operators, precedence
4. **Type System** - Generic instantiation, constraint checking
5. **Match Patterns** - Complex destructuring, guards
6. **String Interpolation** - Edge cases in `{expr}` handling
7. **Control Flow** - `break`/`continue` in nested loops

### Example: Adding New Branch Coverage Test

Create `test/unit/core/branch_coverage_26_spec.spl`:

```simple
"""
# Branch Coverage Test Suite - Parser Edge Cases

**Feature IDs:** #BRANCH #PARSER
**Category:** Testing
**Status:** Implemented

## Overview

Tests uncovered branches in parser for edge cases.
"""

use std.spec.{check}

describe "Parser - Nested Expression Branches":
    it "deeply nested parentheses":
        val expr = parse_expr("(((1 + 2)))")
        check(expr.kind == EXPR_BINARY)

    it "mixed precedence without parens":
        val expr = parse_expr("1 + 2 * 3")
        # Should parse as: 1 + (2 * 3)
        check(expr.left.kind == EXPR_NUMBER)
        check(expr.right.kind == EXPR_BINARY)
```

---

## Common Pitfalls

### Runtime Limitations

The interpreter has several limitations (see `MEMORY.md`):
- **NO generics at runtime** - `<>` syntax fails in interpreter
- **NO try/catch/throw** - use Option pattern
- **Closure capture broken** - can read outer vars, cannot modify
- **Chained methods broken** - use intermediate `var`

### Test Guidelines

1. **Use built-in matchers only:**
   - `to_equal`, `to_be`, `to_be_nil`, `to_contain`
   - `to_start_with`, `to_end_with`
   - `to_be_greater_than`, `to_be_less_than`

2. **Use `check(bool)` not `to_be_true()`**
   ```simple
   check(value == true)   # ✓ Correct
   expect(value).to_be_true()  # ✗ No such matcher
   ```

3. **Test both paths for every branch**
   ```simple
   it "condition true": check(func(5) == expected)
   it "condition false": check(func(0) != expected)
   ```

---

## References

- **Coverage Design:** `doc/MCDC_COVERAGE_DESIGN.md`
- **Unified Coverage Plan:** `doc/research/unified_coverage_plan.md`
- **Test Runner Design:** `doc/TEST_RUNNER_TAG_DESIGN.md`
- **SSpec Framework:** `.claude/skills/sspec.md`
- **Testing Guide:** `doc/guide/testing.md`
