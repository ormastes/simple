# TargetHIR stale waiter accepts a retry's terminal result

Status: source repair; runtime verification unexecuted by explicit user waiver.
Source inspected: release revision `f998bc43600f8ae22bb7e7db75bc7edd69ecbcce`.

`RegionSlotTable.await_slot` checked the requested generation only while the
slot was Building. If generation 1 was canceled, generation 2 was claimed and
published Ready, a generation-1 waiter returned generation 2's payload as its
own result. The equivalent retry ending in Failed exposed the replacement's
failure rather than reporting that the original generation had expired.

The owner now preserves the empty-slot diagnostic first, then checks generation
before exposing Building, Ready or Failed state. Current-generation pending,
success and failure results retain their behavior. This does not add concurrent
synchronization or change the separate snapshot/pin representation.

Authored regression: `test/01_unit/compiler/hir/target_hir_region_slot_spec.spl`.
New scenarios cover canceled/reclaimed Ready and Failed states and missing-slot
diagnostic precedence. The existing stale Building and current-generation cases
remain. No compiler, test, bootstrap or native execution was performed; source
review does not qualify the runtime protocol.
