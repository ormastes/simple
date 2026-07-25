# Failed Test Status Report

**Updated:** 2026-01-24 (after single-line function implementation)
**Location:** `test/lib/std/unit/tooling/`

---

## Summary

| Status | Count | Change |
|--------|-------|--------|
| Total Tooling Tests | 51 | - |
| Passed | 44 | +5 from fixes |
| Failed | 7 | -5 from fixes |

---

## Current Failed Tests (7)

| # | File | Error Type | Line |
|---|------|------------|------|
| 1 | color_utils_spec.spl | Inline if requires else | 131 |
| 2 | math_utils_spec.spl | Inline if requires else | 18 |
| 3 | path_utils_spec.spl | Inline if requires else | 35 |
| 4 | json_utils_spec.spl | Expected expression, found Eof | - |
| 5 | url_utils_spec.spl | Expected expression, found Newline | - |
| 6 | parse_utils_spec.spl | Undefined identifier: parse_int | - |
| 7 | html_utils_spec.spl | Missing argument for 'content' | - |

---

## Error Details by Category

### Category 1: Inline If Without Else Clause (3 tests)

**Error:**
```
parse error: Syntax error at X:Y: Inline if expression requires an else clause
```

**Files:** color_utils, math_utils, path_utils

**Problem:** Code uses inline if without else:
```simple
if condition: value
else if other: value2    # Parser sees this as separate statement!
```

**Fix:** Use block syntax:
```simple
if condition:
    value
else if other:
    value2
```

---

### Category 2: Expression Expected (2 tests)

**Errors:**
- `expected expression, found Eof` (json_utils)
- `expected expression, found Newline` (url_utils)

**Problem:** Incomplete expression or unexpected line ending.

**Fix:** Review files for syntax errors or incomplete statements.

---

### Category 3: Missing Module (1 test)

**Error:**
```
semantic: Undefined("undefined identifier: parse_int")
```

**File:** parse_utils_spec.spl

**Problem:** Imports `tooling.parse_utils.*` which doesn't exist.

**Fix:** Create module or define functions locally.

---

### Category 4: Missing Argument (1 test)

**Error:**
```
semantic: function expects argument for parameter 'content', but none was provided
```

**File:** html_utils_spec.spl

**Problem:** Function call missing required `content` argument.

**Fix:** Find and fix the function call.

---

## Tests Fixed by Single-Line Function Feature

The following tests now pass after implementing single-line function definitions (`fn name(): expr`):

| # | File | Previous Error |
|---|------|----------------|
| 1 | markdown_utils_spec.spl | expected Newline, found FString |
| 2 | compile_commands_spec.spl | expected Newline, found Identifier |
| 3 | coverage_spec.spl | parse error |
| 4 | misc_commands_spec.spl | parse error |
| 5 | regex_utils_spec.spl | parse error |
| 6 | web_commands_spec.spl | expected identifier, found Unwrap |

**Note:** web_commands also required adding `Unwrap` to allowed method names for `.unwrap()` calls.

---

## Comparison: Before vs After

| Metric | Before | After | Change |
|--------|--------|-------|--------|
| Tooling Tests Passed | 39 | 44 | +5 |
| Tooling Tests Failed | 12 | 7 | -5 |
| Pass Rate | 76.5% | 86.3% | +9.8% |

---

## Valid If Syntax Reference

```simple
# VALID: Inline if WITH else (same line)
val x = if cond: a else: b

# VALID: Block if (can omit else)
if cond:
    do_something()

# VALID: Block if-else-if
if cond:
    a
else if other:
    b
else:
    c

# INVALID: Inline if WITHOUT else
val x = if cond: a   # ERROR!

# INVALID: Inline if, else on next line
if cond: a
else: b   # ERROR - else is separate!
```

---

## Recommendations

1. **High Priority:** Fix 3 inline-if tests (color, math, path) - simple syntax change
2. **Medium Priority:** Fix html_utils missing argument
3. **Low Priority:** Create parse_utils module or update test
4. **Investigate:** json_utils and url_utils for incomplete expressions
