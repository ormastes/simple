# Kernel Phase 7 Qualification

- Executable: `test/03_system/compiler/kernel_phase7_qualification_spec.spl`
- Requirements: `KPM-REQ-001`, `KPM-REQ-004`, `KPM-REQ-006`, `KPM-REQ-008`,
  `KPM-REQ-009`, `KPM-REQ-010`, `KPM-REQ-011`, `KPM-REQ-012`, `KPM-REQ-013`,
  `KPM-NFR-001`, `KPM-NFR-004`, `KPM-NFR-005`, `KPM-NFR-006`
- Evidence class: executable qualification definition; no runtime result is embedded.

## Scenarios

- binds LLVM plus Cranelift, ABI v1, simple.sdn, and atomic APK-only
- records the selected one-binary row as BLOCKED without runtime evidence
- refuses a BLOCKED summary as a deployment prerequisite
- keeps both selected build modes without restoring rejected policy alternatives
- rejects legacy coverage ABI and manifest policy inputs
- uses production bootstrap, parity, hash, and strict startup gates
  This includes generating the Phase 5 relocation audit on demand before the
  Phase 7 composition checker runs in a fresh isolated worktree.

## Selected Authority

- Backend composition: LLVM+Cranelift.
- ABI epoch: v1.
- Manifest ownership: `simple.sdn`.
- Coverage cutover: atomic APK-only.
- Residency: admitted per-architecture baseline; maximum steady RSS is 110% of
  baseline RSS and nonnegative growth across 20 warm requests is 10% of baseline RSS.

Dual coverage, deferred ABI, `plugin.sdn`, missing baselines, and stale or
cross-architecture receipts fail closed. The one-binary and dynload rows must
use produced self-hosted artifacts and retain provenance-safe evidence.

## Freshness

The requirement IDs and scenario titles mirror the executable source. Runtime,
APK-only coverage, one-binary, dynload, startup, and residency qualification
remain blocked until admitted self-hosted evidence exists. No runtime PASS is claimed.
