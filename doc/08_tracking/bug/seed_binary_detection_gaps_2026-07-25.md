# Bug: seed-binary detection is path-based and defeated by cosmetic misdetection
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Date:** 2026-07-25  
**Status:** RESOLVED 2026-11-25 — content-first detection landed; selftest 5/5 PASS (see verification section at bottom)

## Problem
The `is_rust_seed_simple()` classifier in `check-hosted-wm-capture-evidence.shs` uses path substring matching (`src/compiler_rust/*`) as its sole detection criterion. A seed binary copied to a self-hosted-looking deploy path is silently accepted by evidence gates.

Aggravating: the deployed stage4 self-hosted binary itself prints the seed WARNING line in some run lanes (known cosmetic misdetection, recorded in `doc/03_plan/compiler/bootstrap/stage4_macos_deploy_2026-07-25.md`) and embeds the warning string. This links seed driver components, causing string/warning probes to misclassify the self-hosted binary as seed.

**Result:** Identification is unreliable in both directions.

## Consequence
- Deployed self-hosted binaries may be rejected or incorrectly validated
- Seed binaries with relocated paths bypass detection
- Evidence matrix gates cannot reliably distinguish self-hosted from seed runs
- Blocks reproducible evidence collection

## Fix Direction
Implement a definitive self-ID channel (e.g., `--version` reporting: `build_lane=seed|stage4-selfhosted` + `source_sha=<hash>`). Consume this across all evidence-gate scripts. Fix the cosmetic warning misdetection at its root in the deployed binary.


## 2026-11-25 verification (p3-bav lane) — RESOLVED

The reported defect (path-substring-only seed detection, defeated by relocated
seeds and by the cosmetic warning misdetection) is fixed in current source:

- `scripts/check/check-hosted-wm-capture-evidence.shs` `is_rust_seed_simple()`
  (line 27) is now content-first: after the retained path check it greps the
  binary bytes for the seed-warning literal (`grep -a -q -F "$SEED_MARKER"`),
  which only the Rust driver (`src/compiler_rust/driver/src/seed_warning.rs`)
  embeds; the header comment records the 2026-08-17 measurement that a
  path-clean seed was previously admitted and that the self-hosted stage3
  binary does not contain the marker (so no false positive in the other
  direction).
- Empirical: `sh scripts/check/check-hosted-wm-capture-evidence.shs --selftest`
  on this host (2026-11-25) -> `PASS — 5 selftest fixture(s) checked, 0 failed`,
  covering deployed-seed-outside-compiler_rust, seed-by-path-without-marker,
  self-hosted-no-false-positive, symlink-to-seed, and absent-path cases —
  exactly the bypass shapes this bug reported.

Status: RESOLVED. The broader fix-direction item (a `--version`
`build_lane=`/`source_sha=` self-ID channel consumed by all evidence gates)
remains a possible enhancement but is not required to close the reported
detection gap.
