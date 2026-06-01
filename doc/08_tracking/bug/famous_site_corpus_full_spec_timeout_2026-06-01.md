# Bug: famous-site corpus full system spec times out under focused verification

Date: 2026-06-01

## Summary

`test/system/wm_compare/famous_site_corpus_spec.spl` timed out after 120 seconds when run directly with:

```sh
SIMPLE_LIB=src src/compiler_rust/target/debug/simple test test/system/wm_compare/famous_site_corpus_spec.spl --mode=interpreter --clean
```

The timeout happened while verifying structural layout report wiring. The narrower `structural_layout_report_spec` exercises the new wiring, but the full corpus spec remains too broad/slow for a focused regression gate.

## Impact

This blocks using the full famous-site corpus system spec as a routine focused gate. It also risks hiding regressions behind the runner timeout instead of reporting the failing scenario.

## Required Follow-Up

- Split long-running corpus scenarios into smaller specs or add runner filtering.
- Keep structural layout report wiring covered by `test/system/wm_compare/structural_layout_report_spec.spl`.
- Re-run the full corpus spec after the corpus test suite is split or optimized.

## Current Evidence

- `test/system/wm_compare/famous_site_corpus_spec.spl` typechecks.
- `test/system/wm_compare/structural_layout_report_spec.spl` covers the new structural report surface and focused corpus layout-report attachment.
