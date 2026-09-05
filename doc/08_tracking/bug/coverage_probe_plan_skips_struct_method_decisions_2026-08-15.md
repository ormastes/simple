# Coverage probe plan attributes 0 lines/decisions to executed struct methods

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
