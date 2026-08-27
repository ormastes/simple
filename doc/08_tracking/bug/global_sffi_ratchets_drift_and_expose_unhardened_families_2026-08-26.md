# Global SFFI ratchets drift and expose unhardened families

- **Status:** OPEN
- **Filed:** 2026-08-26
- **Area:** SFFI admission and unsafe-surface tooling
- **Severity:** critical — global safety gates are not green

## Evidence

`scripts/check/check-raw-sffi-unsafe-ratchet.shs` reports 11,356 `rt_`
declarations: 2,826 tagged, 8,281 untouched, and 0 signed-admitted. Its baseline
comparison fails with 540 new and 3,435 stale entries. Regenerating the baseline
would silently grandfather new unsafe declarations and is not an acceptable
fix.

`scripts/audit/sffi-null-signature-guard.shs` independently fails. Checked
dynload/symbol providers and typed boolean thunks have since removed those WFFI
findings, but stale TCP/UDP ABI expectations, runtime null contracts, and missing
checked crypto bindings remain.

## Unblock condition

Review the 540 new declarations by provider family: remove duplicates, add
minimal lexical unsafe contracts where raw access is required, or replace
fabricated-value APIs with checked status/out contracts. Remove only genuinely
stale baseline rows. Implement signed exact-artifact admission, then require
both commands to pass without broad exclusions or baseline regeneration.
