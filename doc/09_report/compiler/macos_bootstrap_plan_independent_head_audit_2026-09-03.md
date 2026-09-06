# macOS Bootstrap Plan Independent HEAD Audit

**Date:** 2026-09-03  
**Audited HEAD:** `9be09131322b4b0be4737d33e2aa8ee6f7ebb691`  
**Verdict:** incomplete; one portable M0 contract gap fixed by this audit

## Scope

This audit re-read the macOS harmonization plan and every current-tree document
linked by its documentation section. It compared their named deliverables and
acceptance gates with source and executable tests at the audited HEAD. Native
Apple signing, notarization, Intel execution, and unavailable producer artifacts
were excluded from portable implementation claims.

## Findings

1. `ReverseReferenceKeyV1`, immutable reverse-reference projection receipts,
   and the Phase2-to-Phase3 compatibility manifest named by M2/M3 were absent at
   this HEAD. They remain source gaps, not external-signing blockers.
2. The sidecar contract freeze names `MacosBootstrapReceiptV1`, but no typed
   source contract existed. Existing shell receipts do not provide one portable,
   fail-closed schema for native identity, timings, memory, cache counts, source
   reads, critical path, real `Results:` evidence, and seed-substitution policy.
3. The P0 status table is stale relative to the much larger bootstrap script,
   but its broad completion claim cannot be updated without canonical typed
   evidence and native runs.
4. M4/M5 native per-architecture, universal, signing, notarization, and
   promote-without-rebuild gates still require external runners/artifacts or
   credentials and were not claimed from source tests.

## Implemented Gap

`src/compiler/00.common/cache/macos_bootstrap_receipt.spl` now defines the
portable `MacosBootstrapReceiptV1` contract. Admission rejects malformed hashes,
unsupported/cross-host architectures, target mismatches, inconsistent module
counts, impossible RSS evidence, missing native/focused/contract/results proof,
and Rust-seed artifact substitution. Canonical length-framed hashing binds every
field while excluding paths and timestamps from semantic identity.

`test/01_unit/compiler/cache/macos_bootstrap_receipt_v1_spec.spl` covers arm64
and x86_64 valid receipts plus architecture, target, digest, counter, RSS,
vacuous-success, substitution, and digest-mutation failures.

## Remaining Portable Work

- Connect the typed receipt to the bootstrap collector and validator.
- Implement `ReverseReferenceKeyV1` and registry-specific immutable projections.
- Implement and adversarially test the read-only Phase2-to-Phase3 compatibility
  manifest.
- Add the 20-warm-request retained-RSS monotonic-growth qualification harness.

No native M4/M5 evidence is inferred by this audit.

## Verification

- Focused interpreter SPipe test: **4/4 PASS** using the admitted pure-Simple
  macOS arm64 runtime.
- Stub scan: **PASS**.
- `doc/06_spec` executable-spec layout count: **0**.
- `git diff --check`: **PASS**.
- File-level `check` did not qualify: its lint and format subprocesses both
  returned exit `-1` without a source diagnostic. This is recorded rather than
  promoted to a passing compiler-wide check.
