# Coverage probe plan attributes 0 lines/decisions to executed struct methods
## Open 2026-09-16 — needs owner triage
## Triage 2026-11-25 — still OPEN, Rust-seed-only, out of bounded-fix scope

2026-11-25 triage (work/p3-baq-20261125): re-confirmed the 2026-09-13 triage.
The coverage probe plan / runtime store attribution lives only in the Rust
seed (`src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs`); a
repo-wide search finds no probe-plan attribution code in pure-Simple
`src/compiler`/`src/lib`/`src/app`. A fix therefore requires a Rust seed
change plus a cargo build, which this lane is forbidden to run, and the repro
additionally needs a `--coverage` run against a real Vulkan struct-method
spec. Left OPEN; no doc content changed beyond this note.

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Triage 2026-09-13
OPEN, out of scope for this lane: this shard's file column names
`src/compiler_rust/compiler/src/mir/lower/lowering_coverage.rs` — Rust seed
MIR coverage-lowering, not pure-Simple `src/lib`/`src/app`/`src/compiler`
source. The repro also requires a `--coverage` run plus a real Vulkan
struct-method spec to confirm against, which is not a cheap, isolated repro
within this pass's budget either way. Left OPEN, no doc content changed
beyond this line.

**Date:** 2026-08-15
**Status:** OPEN
**Severity:** P3 — coverage measurement blind spot, not a runtime defect

## Symptom

`src/lib/nogc_sync_mut/gpu/engine2d/vulkan_presenter.spl` struct methods
(`VulkanEngine2dPresenterReceipt.is_valid`,
`VulkanEngine2dPresentDamageReceipt.is_direct_partial_present`) demonstrably
execute under `bin/simple test --coverage` (11 assertions on their results
pass in
test/01_unit/os/compositor/vulkan_present_damage_gate_branch_coverage_spec.spl),
yet the coverage report attributes **0/91 lines and 0/0 decisions** to the
module — any `@cover` threshold on it fails vacuously.

## Impact

Modules whose logic lives in struct methods (as opposed to free functions or
class methods) cannot be coverage-gated; per-layer coverage campaigns must
skip them, understating real coverage.

## Unblock

Extend the probe plan/runtime store attribution to struct-method bodies, or
document the scope limit in the coverage guide. Cross-check whether class
methods and free functions in the same file attribute correctly (they do in
sibling modules, e.g. vulkan_present_damage_gate.spl 9/9).

