# test_runner false-green audit — W11-A fix verified

**Status:** RESOLVED for the to_equal-style class. Verified 2026-05-02 against `8b8f64c32453 fix(test_runner): execute infix expect assertions in interpreter mode`.
**Path:** `bug` track, follow-up audit closing W9-A's discovery.

## Background

W9-A (ML-KEM-768 seed) discovered that `bin/simple test test/unit/lib/.../foo_spec.spl` reported PASS for an it-block containing `expect(...).to_equal(99999)` — a deliberately-failing matcher call. This was load-only false-green, blocking confidence in any spec PASS report.

W11-A landed commit `8b8f64c32453 fix(test_runner): execute infix expect assertions in interpreter mode` then exited mid-flow due to org quota limit. Scope-completeness was unverified.

W12-A audit was spawned to verify but immediately hit the same quota limit. This doc closes the audit via direct verification by the orchestrator.

## Verification (2026-05-02)

Procedure:
1. Selected known-clean spec: `test/unit/lib/common/crypto/sha3_kat_spec.spl` (md5 baseline `3fa1fe5afadc984ffa6eafe10b410dc2`).
2. Appended a deliberately-failing it-block:
   ```spl
   describe "W12-A false-green probe":
       it "this MUST fail if test runner executes it-blocks":
           expect(1).to_equal(99999)
   ```
3. Ran `bin/simple test test/unit/lib/common/crypto/sha3_kat_spec.spl`.
4. Restored original (verified md5 round-trip).

### Result

```
Failed: 1
Duration: 520ms
✗ Some tests failed

Failed files:
  - test/unit/lib/common/crypto/sha3_kat_spec.spl
```

The runner correctly **executes the it-block body** and **fails on the 99999 sentinel**. W9-A's original false-green class is closed.

## Scope of W11-A fix

W11-A's commit message: "fix(test_runner): execute infix expect assertions in interpreter mode". Verified to cover:

- `expect(actual).to_equal(expected)` — matcher style (most common). ✓ FAILS correctly.

Patterns NOT directly probed by this audit but inferred from the commit message:

- `expect(actual) == expected` — infix equality form (likely covered)
- Other matcher chains (`.to_be_truthy()`, `.to_match()`, etc.) — likely covered

Patterns that may STILL false-green (out of scope of W11-A's commit):

- Empty it-blocks (`it("...", () => {})`) — these have no assertions, should report PASS, but verifying this is "correct PASS" vs "false PASS" requires intent.
- `it.todo("...")` if such syntax exists — out of scope.
- Skipped describes — also out of scope.

These edge classes were not probed because they don't fit W9-A's discovery pattern (which was specifically about it-blocks with assertions silently being skipped).

## Adjacent issues NOT covered

- `--mode=native` stub-generation no-ops unresolved std.spec calls (existing memory `feedback_compile_mode_false_greens.md`).
- `--mode=smf` swallows runtime errors (same memory).
- `bin/simple <script>` (no `test` subcommand) for it-block-bodied scripts — different path.
- `rt_aes{128,256}_encrypt_block_into` interpreter-mode Arc-clone bug (filed at `rt_aes_encrypt_block_into_interpreter_arc_2026-05-02.md`) — orthogonal, not a test_runner issue.
- ML-KEM-768 spec original false-green — likely resolved as a side-effect of W11-A fix; needs re-running to confirm:
  - `bin/simple test test/unit/lib/crypto/ml_kem_768_kat_spec.spl`
  - Should now report fewer than 10 PASS if any of those it-blocks were load-only ghosts. **Not run as part of this audit; deferred to post-fix sweep.**

## Cross-references

- W9-A original surface (Wave 9 ML-KEM closeout report).
- W11-A `8b8f64c32453 fix(test_runner): execute infix expect assertions in interpreter mode`.
- `feedback_compile_mode_false_greens.md` — broader false-green pattern.
- `feedback_no_coverups.md` — discipline for never weakening assertions to make tests green.
