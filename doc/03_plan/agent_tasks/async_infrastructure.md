# Async infrastructure lanes and merge ownership

**2026-10-27 — design handoff; no implementation milestone completed here.**
Selected scope comes from the user and the merged SCV/resource plans. This
work extends existing owners after duplicate/API inspection; it does not
select a new runtime or remove generic semantic specialization.

| Lane | Owner / model | Scope and handoff |
|---|---|---|
| Architecture/design | `astra_async_arch` / Astra | Source audit; language/common-interface and hosted/embedded separation; detailed lifecycle and TDD inventory; documents only |
| Scalar map/ref implementation | `luna_lockless_impl` / Luna | Test-first bounded scalar map/ref; own code/tests, actual import/native receipts; no generic or scheduler completion claims |
| Algorithm/safety review | `astra_lockless_guide` / Astra | Define shared names, review publication/wakes/lifetime/target capability and exact test oracles; review implementation before acceptance |
| Existing cache/library fixes | Parent-assigned independent lane | Inspect/reuse existing utility helpers, regression-first fixes, no duplicate registry or scheduler |
| Bootstrap/Hello | Parent's existing compiler lanes | After required map/ref tests, exact producer phase3 lineage and Hello; preserve independent failures and admission gates |
| Merge owner and final reviewer | Parent `/root`, with Astra review for concurrency design | Reconcile interfaces, exact-head review, document links/status and evidence; land reviewed session-owned PR |

Shared interface names, reserved files and dependency directions are in
[detail design](../../05_design/lib/runtime/async_infrastructure.md). Manual
step/setup/checker names and fail-fast rule are in the
[TDD plan](../sys_test/async_infrastructure.md). No lower-model sidecar may mark
source inspection, model output, or generated prose as native qualification.

No UI applies. Existing feature/layer route is the SimpleRing async-base
contract/capsule plus parallel-ownership and host-I/O library layers; no OS
kernel/driver ownership is changed. Existing requirements and selected plans
are reused. New architecture and details supplement, not overwrite, historical
design/evidence. Executable system specs and generated manuals remain pending
implementation; the design-only document gate is not full verify/release PASS.
