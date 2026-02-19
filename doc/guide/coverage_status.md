# Coverage System Status & Action Plan

**Date:** 2026-02-11
**Status:** Coverage infrastructure exists but instrumentation is not implemented

---

## Current Situation

### What Works ✅

1. **Runtime Coverage Functions** - Available and functional
   - `rt_coverage_enabled()` - Returns true when `SIMPLE_COVERAGE=1`
   - `rt_coverage_decision_probe()` - Records decision branches
   - `rt_coverage_condition_probe()` - Records conditions
   - `rt_coverage_dump_sdn()` - Exports coverage data
   - `rt_coverage_clear()` - Resets coverage state

2. **Test Runner Integration** - Fully implemented
   - `--coverage` flag enables coverage mode
   - Sets `SIMPLE_COVERAGE=1` environment variable
   - Collects and merges coverage data across test files
   - Generates reports in `.coverage/` directory

3. **Coverage Reporting** - Complete
   - SDN format data storage (`.coverage/coverage.sdn`)
   - Per-file summary (`.coverage/summary.md`)
   - Uncovered branches report (`.coverage/uncovered.md`)
   - Decision and condition coverage metrics
   - Baseline tracking for regression detection

4. **Seed Compiler Coverage** - Working
   - C/C++ seed compiler has 87.21% branch coverage
   - Uses LLVM source-based coverage
   - Report: `seed/.build-coverage/report/index.html`
   - Run: `bash seed/run_coverage.sh`

### What Doesn't Work ❌

**Coverage Instrumentation is Missing**

When Simple code is compiled or interpreted, the compiler/interpreter does NOT insert calls to `rt_coverage_*` functions. This means:

- ❌ **Interpreter mode:** No coverage tracking (interpreter doesn't call probes)
- ❌ **SMF mode:** No coverage tracking (compiler doesn't insert probes)
- ❌ **Native mode:** No coverage tracking (compiler doesn't insert probes)
- ❌ **All test runs show:** 0% coverage, 0 decisions, 0 conditions tracked

### Test Results

```bash
$ bin/simple test test/unit/compiler_core/ --coverage

Decision coverage: 0% (0/0 decisions)
Condition coverage: 0% (0/0 conditions)
Files tracked: 0
```

Even a test with explicit `if` statements shows 0% coverage:
```simple
it "simple if branch":
    val x = 10
    if x > 5:  # NOT tracked
        check(true)
    else:
        check(false)
```

---

## Root Cause Analysis

### Missing Component: Compiler Instrumentation

The compiler needs to insert coverage probe calls during code generation. Example:

**Source Code:**
```simple
if condition:
    then_branch()
else:
    else_branch()
```

**Should Generate (pseudo-code):**
```c
bool decision_result = evaluate(condition);
rt_coverage_decision_probe("file.spl", 42, 1, decision_result);
if (decision_result) {
    then_branch();
} else {
    else_branch();
}
```

**Currently Generates:**
```c
// No coverage probe call!
if (evaluate(condition)) {
    then_branch();
} else {
    else_branch();
}
```

### Why Interpreter Mode Doesn't Work

The interpreter (`src/compiler_core/interpreter/eval.spl`) evaluates AST nodes but doesn't call coverage functions:

**Current `eval_if_expr` function:**
```simple
fn eval_if_expr(eid: i64) -> i64:
    val cond_val = eval_expr(cond_id)
    if val_is_truthy(cond_val):  # Branch taken but NOT recorded
        return eval_expr(then_id)
    if else_id >= 0:
        return eval_expr(else_id)
    val_make_nil()
```

**Should be:**
```simple
fn eval_if_expr(eid: i64) -> i64:
    val cond_val = eval_expr(cond_id)
    val taken = val_is_truthy(cond_val)

    # Record coverage
    if rt_coverage_enabled():
        rt_coverage_decision_probe(file, line, decision_id, taken)

    if taken:
        return eval_expr(then_id)
    if else_id >= 0:
        return eval_expr(else_id)
    val_make_nil()
```

---

## Workaround: Seed Compiler Coverage

While Simple code coverage doesn't work, we CAN measure how well tests exercise the **seed compiler** (C++):

### Seed Coverage: 87.21% (Target: >95%)

```bash
# Run seed coverage
bash seed/run_coverage.sh

# View report
open seed/.build-coverage/report/index.html
```

### Strategy

Writing diverse Simple tests improves seed compiler coverage by exercising different:
- Parser paths (edge cases, error recovery)
- Code generation branches (rare constructs)
- Type checking logic (complex types)
- Expression evaluation (operator precedence)

**Current Gaps (~13% uncovered):**
- Error handling paths
- Edge cases (empty input, max limits)
- Complex expressions (deeply nested operators)
- String interpolation edge cases
- Less common language features

---

## Action Plan

### Phase 1: Quick Wins (Seed Coverage)

**Goal:** Improve seed.cpp coverage from 87.21% → 95%+

1. **Analyze uncovered branches**
   ```bash
   bash seed/run_coverage.sh
   # Review HTML report for red/yellow lines
   ```

2. **Write targeted tests**
   - Create `test/unit/compiler_core/branch_coverage_26_spec.spl` and beyond
   - Focus on error cases, edge inputs, rare constructs
   - Test parser edge cases (deeply nested, malformed input)
   - Test expression evaluation corner cases

3. **Verify improvement**
   ```bash
   bash seed/run_coverage.sh
   # Check if coverage % increased
   ```

### Phase 2: Implement Coverage Instrumentation (Major Feature)

**Goal:** Enable Simple code coverage tracking

#### 2.1 Compiler Instrumentation

**File:** `src/compiler/codegen/*.spl` (or equivalent)

Add instrumentation pass that:
1. Tracks file/line info during compilation
2. Assigns unique IDs to each decision point
3. Inserts `rt_coverage_decision_probe()` calls before `if`/`match`
4. Inserts `rt_coverage_condition_probe()` for boolean conditions
5. Only inserts probes when `rt_coverage_enabled()` returns true

**Example transformation:**
```simple
# Input AST:
if x > 5:
    foo()

# Generated code (with instrumentation):
temp_cond = x > 5
if rt_coverage_enabled():
    rt_coverage_decision_probe("file.spl", 10, 42, temp_cond)
if temp_cond:
    foo()
```

#### 2.2 Interpreter Instrumentation

**File:** `src/compiler_core/interpreter/eval.spl`

Modify evaluation functions:
- `eval_if_expr` - Record which branch taken
- `eval_match_expr` - Record which case matched
- `eval_while_expr` - Record loop entry/skip
- `eval_for_expr` - Record loop iterations

Add extern declarations:
```simple
extern fn rt_coverage_enabled() -> bool
extern fn rt_coverage_decision_probe(file: text, line: i64, id: i64, taken: bool)
```

Modify `eval_if_expr`:
```simple
fn eval_if_expr(eid: i64) -> i64:
    val e_node = expr_get(eid)
    val cond_val = eval_expr(e_node.left)
    val taken = val_is_truthy(cond_val)

    # Coverage instrumentation
    if rt_coverage_enabled():
        val loc = get_expr_location(eid)
        rt_coverage_decision_probe(loc.file, loc.line, eid, taken)

    if taken:
        return eval_expr(e_node.right)
    if e_node.extra >= 0:
        return eval_expr(e_node.extra)
    val_make_nil()
```

#### 2.3 Location Tracking

Need to track source locations for AST nodes:
- Add `file: text` and `line: i64` fields to `Expr`/`Stmt` structs
- Preserve location info during parsing
- Pass locations to coverage probes

### Phase 3: Testing & Validation

1. **Test interpreter coverage**
   ```bash
   bin/simple test test/unit/compiler_core/ --coverage
   # Should show >0% coverage
   ```

2. **Test compiled coverage**
   ```bash
   bin/simple test test/unit/compiler_core/ --mode smf --coverage
   # Should show coverage for test code
   ```

3. **Validate reports**
   - Check `.coverage/summary.md` shows files
   - Check `.coverage/uncovered.md` identifies gaps
   - Verify coverage data is accurate

### Phase 4: MC/DC Support (Advanced)

Once basic coverage works, add MC/DC:
- Instrument individual conditions in compound expressions
- Track independence pairs
- Generate MC/DC reports

---

## Immediate Actions (Today)

### 1. Create Seed Coverage Tests ✅

Focus on improving seed.cpp coverage by writing tests for uncovered paths:

```bash
# Create new branch coverage test
cat > test/unit/compiler_core/branch_coverage_26_spec.spl <<'EOF'
"""
# Branch Coverage - Parser Edge Cases

**Feature IDs:** #BRANCH #PARSER
**Status:** Implemented
"""

use std.spec.{check}

describe "Parser Edge Cases":
    it "empty source file":
        val result = parse_source("")
        check(result.?)

    it "only whitespace":
        val result = parse_source("   \n\n  \t  ")
        check(result.?)

    it "deeply nested parentheses":
        val result = parse_expr("((((((1))))))")
        check(result.?)
EOF

# Run coverage
bash seed/run_coverage.sh
```

### 2. Document Current State ✅

Created:
- `doc/guide/testing_core_simple.md` - How to test core Simple
- `doc/guide/coverage_status.md` - This document

### 3. File Bug Report

Create issue: "Coverage instrumentation not implemented - shows 0% for all Simple code"

---

## Summary

**Status:** Coverage **reporting** works, coverage **instrumentation** doesn't exist.

**Workaround:** Improve seed compiler (C++) coverage by writing diverse Simple tests.

**Long-term:** Implement compiler and interpreter instrumentation to enable Simple code coverage tracking.

**Next Step:** Write more `branch_coverage_*.spl` tests to improve seed.cpp coverage from 87.21% to 95%+.
