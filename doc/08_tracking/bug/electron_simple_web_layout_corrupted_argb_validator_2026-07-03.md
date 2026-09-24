# Electron Simple Web Layout Corrupted ARGB Validator
## Closed 2026-09-16 — status fixed; validator recomputes checksums, regression scenario verifies pass

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

- status: fixed
- date: 2026-07-03
- gate: `test/03_system/check/electron_simple_web_layout_proof_validator_spec.spl`

## Bug

A GUI/web proof can claim matching checksums while the captured Electron ARGB
artifact has a one-pixel corruption. If the validator trusts only proof rows, a
bad captured image can be reported as equal.

## Fix

The validator recomputes checksum and weighted checksum from the captured ARGB
artifact and rejects mismatches. The regression scenario corrupts one captured
pixel, verifies `captured-argb-checksum-mismatch`, then writes the fixed proof
and verifies `pass`.

