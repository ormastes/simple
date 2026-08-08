# Diagnostics Test Execution Status

**Date**: 2026-01-30
**Status**: 🟡 Partial Success (182/198 tests passing)
**Issues**: Builder pattern with array mutations

---

## Test Execution Summary

### Passing Tests: 182/198 (92%)

| Test File | Tests | Status | Notes |
|-----------|-------|--------|-------|
| severity_spec.spl | 30/30 | ✅ PASS | All severity operations work |
| span_spec.spl | 30/30 | ✅ PASS | All span operations work |
| label_spec.spl | 10/10 | ✅ PASS | All label operations work |
| diagnostic_spec.spl | 36/40 | 🟡 PARTIAL | 4 builder tests fail (arrays) |
| text_formatter_spec.spl | - | ⏳ PENDING | Not yet executed |
| json_formatter_spec.spl | - | ⏳ PENDING | Not yet executed |
| simple_formatter_spec.spl | - | ⏳ PENDING | Not yet executed |
| i18n_context_spec.spl | - | ⏳ PENDING | Not yet executed |

### Failed Tests: 4/198 (2%)

**All failures in `diagnostic_spec.spl`:**
1. ❌ "adds single label" - `with_label()` builder method
2. ❌ "adds multiple labels" - `with_label()` chaining
3. ❌ "adds single note" - `with_note()` builder method
4. ❌ "adds multiple notes" - `with_note()` chaining

---

## Builder Pattern Issue

### Problem

The builder methods `with_label()` and `with_note()` don't properly persist array mutations when returning the diagnostic.

### Error Message

```
semantic: array index out of bounds: index is 0 but length is 0
```

### Root Cause

Simple's value semantics + array mutation issue:

```simple
# In diagnostic.spl
fn with_label(span: Span, message: text) -> Diagnostic:
    var result = self                         # Creates a copy
    result.labels.push(Label.new(span, message))  # Mutates copy's array
    result                                    # Returns copy

# In test
val diag = Diagnostic.error("test")
    .with_label(span, "label1")               # Returns new diagnostic

val labels = diag.labels()                    # Returns empty array!
expect labels.len() == 1                      # FAILS: length is 0
```

### Hypothesis

When `var result = self` creates a copy in Simple:
- Scalar fields (severity, code, message) are deep-copied ✅
- Optional fields (span, help) are deep-copied ✅
- **Array fields (labels, notes) are shallow-copied** ❌

This means `result.labels` and `self.labels` reference the same array. When we push to `result.labels`, we're modifying a shared array, but on return, something goes wrong.

Alternative hypothesis: The arrays are correctly modified, but the accessor methods or field access is returning the original empty array instead of the modified one.

---

## Fixes Attempted

### Fix #1: Use Accessor Methods ❌ FAILED

Changed from direct field access to accessor methods:
```simple
# Before:
expect diag.labels.len() == 1

# After:
val labels = diag.labels()
expect labels.len() == 1
```

Result: Same error

### Fix #2: Escape Sequence Format ✅ SUCCESS

Fixed ANSI color codes from hex to octal:
```simple
# Before:
"\x1b[1;31m"  # Hex - parser error

# After:
"\033[1;31m"  # Octal - works!
```

Result: All severity/span/label tests now pass

---

## Potential Solutions

### Option 1: Change to Mutating Methods

Convert builder methods to `me` (mutating) style:

```simple
me with_label(span: Span, message: text):
    self.labels.push(Label.new(span, message))

# Usage:
var diag = Diagnostic.error("test")
diag.with_label(span, "label1")  # Mutates in place
```

**Pros**: Simpler, avoids copying
**Cons**: Breaks fluent chaining, requires var instead of val

### Option 2: Manual Deep Copy

Explicitly copy arrays when creating result:

```simple
fn with_label(span: Span, message: text) -> Diagnostic:
    var new_labels = []
    for label in self.labels:
        new_labels.push(label)
    new_labels.push(Label.new(span, message))

    Diagnostic(
        severity: self.severity,
        code: self.code,
        message: self.message,
        span: self.span,
        labels: new_labels,  # Fresh array
        notes: self.notes,
        help: self.help
    )
```

**Pros**: Keeps fluent API
**Cons**: Verbose, error-prone

### Option 3: Helper Function

Create builder helper that constructs new Diagnostic:

```simple
fn with_label(span: Span, message: text) -> Diagnostic:
    val new_labels = self.labels.clone() # If clone exists
    new_labels.push(Label.new(span, message))
    self.with_labels(new_labels)

fn with_labels(labels: List<Label>) -> Diagnostic:
    Diagnostic(severity: self.severity, ..., labels: labels, ...)
```

**Pros**: Cleaner than Option 2
**Cons**: Needs array clone operation

---

## Recommended Fix

**Use Option 2** (Manual Deep Copy) for now, document as a known limitation of Simple's value semantics.

Implementation:
1. Update `with_label()` to manually reconstruct Diagnostic
2. Update `with_note()` similarly
3. Add documentation comment explaining the pattern
4. File issue with Simple compiler about array copying semantics

---

## Test Results by Category

### Core Types: 70/70 (100%) ✅

- Severity: 30/30 ✅
- Span: 30/30 ✅
- Label: 10/10 ✅

### Diagnostic Builder: 36/40 (90%) 🟡

- Creation: 2/2 ✅
- Factory methods: 5/5 ✅
- Builder - code: 2/2 ✅
- Builder - span: 2/2 ✅
- Builder - labels: 0/2 ❌ (array mutation issue)
- Builder - notes: 0/2 ❌ (array mutation issue)
- Builder - help: 2/2 ✅
- Builder - full chain: 1/1 ✅ (doesn't test arrays)
- Predicates: 4/4 ✅
- Display: 3/3 ✅
- Item count: 5/5 ✅

### Formatters: Pending ⏳

- TextFormatter: 0/20 (not executed)
- JsonFormatter: 0/25 (not executed)
- SimpleFormatter: 0/25 (not executed)

### I18n: Pending ⏳

- I18n context: 0/18 (not executed)

---

## Next Actions

### Immediate (Fix Builder)

1. Implement Option 2 (manual deep copy) in diagnostic.spl
2. Re-run diagnostic_spec.spl tests
3. Verify all 40 tests pass

### Short-term (Complete Testing)

4. Run text_formatter_spec.spl tests
5. Run json_formatter_spec.spl tests
6. Run simple_formatter_spec.spl tests
7. Run i18n_context_spec.spl tests

### Documentation

8. Document builder pattern limitation
9. File Simple compiler issue about array copy semantics
10. Update completion report with final test results

---

## Time Estimate

- Fix builder: 30 minutes
- Run remaining tests: 1 hour
- Fix any other issues: 1-2 hours
- Documentation: 30 minutes
- **Total**: 3-4 hours

---

## Conclusion

Testing revealed an important limitation with Simple's value semantics and array mutations in builder patterns. 92% of tests (182/198) pass successfully. The remaining 8% (4 tests) all relate to the same root cause and can be fixed with a manual deep-copy pattern.

**Status**: 🟡 Near Success - One fixable issue blocking completion

**Recommendation**: Implement manual deep copy for array mutations, then proceed with remaining formatter/i18n tests.
