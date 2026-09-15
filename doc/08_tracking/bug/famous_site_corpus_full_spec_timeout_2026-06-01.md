# Bug: famous-site corpus full system spec times out under focused verification

## Closed 2026-09-13 — Stale: both referenced specs and their whole directory were deleted

- **measured** `ls test/03_system/wm_compare` -> `No such file or directory`; neither `famous_site_corpus_spec.spl` nor `structural_layout_report_spec.spl` exists anywhere under `test/`.
- **measured** The repro command names `src/compiler_rust/target/debug/simple`, a Linux debug seed not built on this host.
- **inferred** A timeout report about a spec file that no longer exists cannot be reproduced or fixed; the corpus lane was removed rather than split.


Status: closed (2026-09-13 triage) — see the "Closed 2026-09-13" section below

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
