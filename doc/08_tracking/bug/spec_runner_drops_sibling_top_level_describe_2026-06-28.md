# Spec Runner Silently Runs Only the LAST Top-Level `describe` (hollow green)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage note 2026-09-13 — could not verify: the spec runner is broken on this host
- **measured** (Windows Rust seed v1.0.0-rc.1): `bin/simple test` is non-functional here — a 3-line 1-assertion spec returns in under a second with `WARNING: test daemon unavailable; running directly`, `error: test-runner: code -1 (process_run_bounded killed the child at its budget)` and a false `reason=outer-bound-timeout budget_ms=930000`. Seven real specs produced byte-identical verdicts.
- **inferred**: every runner-behaviour claim in this entry (example counts, PASS/FAIL bookkeeping, daemon timeouts) is therefore unverifiable here; a green or red from this host would be meaningless either way.
- **inferred**: left OPEN, not stale — the referenced spec files all still exist.

Date: 2026-06-28

Lane: `.spipe/simpleos-alpine-harden-musl-busybox`

## Summary

When a `*_spec.spl` file contains multiple SIBLING top-level `describe` blocks,
the interpreter test runner executes ONLY the last one and silently drops all
earlier sibling groups — reporting a PASS with a reduced example count and NO
error or warning. This manufactures hollow green results: most assertions never
run, yet the file is reported green.

## Evidence (this lane, commit 999581c)

| spec | top-level describes | authored it-blocks | examples actually run |
|---|---|---|---|
| `libc_stdlib_spec.spl` | 7 siblings | 38 | 8 (only the last, `libc_qsort`) |
| `simplebox_dispatch_spec.spl` | 5 siblings | 25 | 5 (only the last, `simplebox_applet_names`) |
| `simplebox_applets_core_spec.spl` | 3 siblings | 16 | 6 (only the last, `applet_chown_parse`) |
| `libc_string_ctype_spec.spl` | 1 (nested) | 14 | 14 (all — single top-level) |
| `libc_stdio_spec.spl` | 1 | 13 | 13 (all) |

The reported "Passed: N" exactly equals the it-count of the LAST describe in
every multi-sibling case. Single-top-level-describe specs run fully.

## Impact

Hollow greens. A reviewer comparing `reported examples` vs `authored it-blocks`
catches it; a reviewer trusting "PASS / 0 failed" does not. Affects both
`describe "X":` (block) and `describe("X"):` (call) styles.

## Workaround (applied in this lane)

Wrap all sibling describes under a SINGLE top-level `describe`, nesting the
former siblings one level deep. Then all it-blocks run.

## Acceptance for closure

- Multiple sibling top-level `describe` blocks all execute (sum of their
  it-blocks == reported examples), OR
- the runner emits a hard error/warning when it would drop a top-level describe,
  so a hollow green is impossible to ship silently.

