# Bug: famous-site corpus full system spec times out under focused verification

Status: CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

Date: 2026-06-01

## Summary

`test/03_system/wm_compare/famous_site_corpus_spec.spl` timed out after 120 seconds when run directly with:

```sh
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/03_system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --clean
```

The timeout happened while verifying structural layout report wiring. The narrower `structural_layout_report_spec` exercises the new wiring, but the full corpus spec remains too broad/slow for a focused regression gate.

## Impact

This blocks using the full famous-site corpus system spec as a routine focused gate. It also risks hiding regressions behind the runner timeout instead of reporting the failing scenario.

## Required Follow-Up

- Split long-running corpus scenarios into smaller specs or add runner filtering.
- Keep structural layout report wiring covered by `test/03_system/wm_compare/structural_layout_report_spec.spl`.
- Re-run the full corpus spec after the corpus test suite is split or optimized.

## Current Evidence

- `test/03_system/wm_compare/famous_site_corpus_spec.spl` typechecks.
- `test/03_system/wm_compare/structural_layout_report_spec.spl` covers the new structural report surface and focused corpus layout-report attachment.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no repro that ran conclusively within the triage budget; closed stale per the standing 'too old -> close' decision. Binary (unused, no run needed): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
