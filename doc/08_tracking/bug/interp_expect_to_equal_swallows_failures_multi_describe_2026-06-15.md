# Bug: expect().to_equal() swallows failures in multi-describe-block specs

**ID:** interp_expect_to_equal_swallows_failures_multi_describe_2026-06-15
**Severity:** P1
**Status:** source-resolved; regression pinned, execution pending
**Discovered:** 2026-06-15

## Symptom

In a spec file with multiple `describe` blocks, `expect(var).to_equal(wrong_value)` reports
the test as PASSED even when `var` holds a different value. The assertion is silently swallowed.

## Reproduction

Minimal: spec file with ≥2 `describe` blocks; inside any `it` body after the first block:

```spl
val cv1 = some_struct.method(arg)   # returns 0
expect(cv1).to_equal(999)            # PASSES when it should FAIL
```

The print output confirms the actual value is 0 (`DBG cv1=0`), but the test is marked green.

## Key Evidence

- **Single-describe-block files:** `expect().to_equal()` correctly fires (negative control confirmed).
- **The diag test** (single `it` in its own `describe` block at top of file) also fires correctly.
- **Multi-describe after the first block:** fails silently.
- `assert_equal(cv1, 999)` in the same position correctly reports FAILED (22 passed, 1 failed).

## Workaround

Use `assert_equal(actual, expected)` and `assert_true(expr)` instead of `expect().to_equal(true/false)`
in any spec file that has more than one `describe` block.

## Affected Files

- `test/01_unit/lib/common/compress/typed/types_spec.spl` — migrated to `assert_equal`/`assert_true`

## Root Cause (Hypothesis)

The `expect()` factory or `.to_equal()` matcher accumulates state into a describe-scoped
register that is not properly reset between `describe` blocks. After the first block's
state is consumed, subsequent matcher calls read stale/zero state and always compare
equal to whatever is there.

## Related Bugs

- `interp_run_enum_single_field_payload_corrupt_2026-06-15.md` — single-field enum payload
  corruption in `bin/simple run` (separate issue; absent in seed test runner)

## Resolution (2026-07-16)

Current `std.spec` resets `current_test_error` only when an `it` starts and
passing matchers never clear it. The child runner also sums every describe
summary instead of trusting the last one. The shared red sibling fixture now
runs a passing expectation after its failure; the existing system contract
still requires two examples and one failure, covering both failure retention
inside one `it` and aggregation across sibling describes. Execution is pending
a permitted pure-Simple test binary.
