# Bug: expect().to_equal() swallows failures in multi-describe-block specs

## Closed 2026-09-13 — does not reproduce: failures in later describe blocks are reported
- **measured** — probe spec with 3 `describe` blocks (1 passing, 2 deliberately wrong
  `to_equal`) run via the Rust seed `bin/simple` v1.0.0-rc.1 on Windows:
  `spec failure: 2 of 3 example(s) failed (exit 1)`, `declared>=3 executed=3 passed=1 failed=2`
  — both wrong assertions surfaced (`expected 5 to equal 9`, `expected abc to equal xyz`).
- **inferred** — filed against the Linux seed interpreter; the Windows seed is the same
  Rust seed lane, so this is strong but not self-hosted-binary evidence.

**ID:** interp_expect_to_equal_swallows_failures_multi_describe_2026-06-15
**Severity:** P1
**Status:** CLOSED 2026-09-13 (triage shard 03) — see the Closed section below
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

## Verification 2026-11-25 (P1 ledger sweep, Windows worktree) — CLOSED stands

Re-ran the closure scenario on the pinned tracked binary (`bin/simple.exe`,
38,403,072 B, Rust seed v1.0.0-rc.1): a probe spec with 3 `describe` blocks
(1 passing example, then one deliberately wrong `to_equal` in each later
block) under `SIMPLE_TEST_RUNNER_RUST=1 bin/simple.exe test` reported
`Passed: 1, Failed: 2` — both later-describe failures surfaced; nothing was
swallowed. (The default pure-Simple runner path is blocked at HEAD by the
pinned seed rejecting `@representation_boundary`; the Rust runner exercises
the same seed spec harness this bug was filed against.) The 2026-09-13
closure stands.
