# C4 account/provider foundation integration

Source target: `release_phase3` commit `23e4331eec5e56c9123713f856b9333902696277`,
confirmed against the remote on 2026-10-25. This integrates a previously selected
foundation for FORMAL-PHYSICAL-ACCOUNTING / C4-HIR-CFG. It does not complete either
requirement. No limits, public API policy, runtime ABI or accepted semantics change.

## Selected authority and provenance

The retained immutable packet root, called B below, is
`/home/yoon/dev/robust-tdd-20261014/formal-c4-structured-loop-contract-20261021`.
Selected authority is [the shared interface](</home/yoon/dev/robust-tdd-20261014/formal-c4-structured-loop-contract-20261021/pathb-shared-interface-v1.json>)
and [Path B design revision 3](</home/yoon/dev/robust-tdd-20261014/formal-c4-structured-loop-contract-20261021/module-budget-component/producer-view-design/revision3/design.md>),
with B/provider-api-v4. The [bounded local reuse audit](</tmp/physical_provider_accounting_research_20261025.md>)
records the selected assignment ledger, duplicate search and actual allocation API
limitations. These host-local links identify the retained evidence, not portable
runtime qualification receipts.

Account revision 1 and provider revision 2 received scoped source/API review GO.
Their 36 original scenarios were UNRUN. The following original after-image hashes
are preserved here so integration changes remain distinguishable from those reviews.
Paths are relative to the repository; packet files occupy the same `after/` paths.

| Original file | SHA-256 |
|---|---|
| `src/compiler/50.mir/loop_resource_account_v1.spl` | `b9fbf6cc967f312c37e471ee65cb89c7cfa779ce12d46361fbda4ba760d69bcd` |
| `test/01_unit/compiler/mir/loop_resource_account_v1_spec.spl` | `b4b6c7b50c9741ed268597231989bdb2f321a73b8841b75c59a6f1f2bc7fa2c2` |
| `doc/06_spec/01_unit/compiler/mir/loop_resource_account_v1_spec.md` | `db9ca75da6558e65d271fa5bba1c2fe0080de1ccdfa76c9c1a85c6e5aa224f6d` |
| `src/compiler/50.mir/loop_module_shape_types_v1.spl` | `6cdd0fa8f381a1773f9540361e7e81ffa715e5a1672fbc82150c88fbc54e91a7` |
| `src/compiler/50.mir/loop_module_shape_owner_v1.spl` | `f7608a9636cf00dd84d64019386ac9dd8a7334d7b3155fdba6a4d112f66eb44b` |
| `src/compiler/50.mir/loop_module_shape_projection_v1.spl` | `c4267ee4f1cc5ec28c3325cd4a0ce170da4ba98b269f71d5f4880b60518f379f` |
| `test/01_unit/compiler/mir/loop_module_shape_owner_v1_spec.spl` | `dde500071c5cee044f046d93af5b57c1a46c5e3ea8b173beb80a27a70fd15342` |
| `test/01_unit/compiler/mir/loop_module_shape_projection_v1_spec.spl` | `b16aa45299212bee4b6390b95e2933cbe12faa45abd6ed623096b4055f994d11` |
| `doc/06_spec/01_unit/compiler/mir/loop_module_shape_owner_v1_spec.md` | `b2d417614aa3a3da2c1e51958a8dc75c70f46f04fb5071a0bf7a844a0e6c33a4` |
| `doc/06_spec/01_unit/compiler/mir/loop_module_shape_projection_v1_spec.md` | `b048e11ed127a567b0e9b033d5b8f9e211d4385c7f12293675e791338d22549a` |

## Ownership and state

The MIR layer owns `MirLoopResourceAccountV1` and the flat scalar shape arena.
One account lives for the invocation. Aliases share cumulative debits and terminal
close. Atomic multi-dimensional reservations compare remaining capacity before
addition; there are no refunds, per-function resets or retrospective charges.
Limits only narrow the frozen hard caps.

`MirLoopShapeOwnerV1` transitions from Constructing to Sealed or Failed. The first
construction failure remains sticky. Writer handles bind the actual owner and row
revision. Construction readers become invalid when their phase ends. Sealed
views retain the same owner/account and return scalar cursors, counts and values.
Closing an alias invalidates further views and projection permits. This is a
single-owner invocation scope; no locks, lock-level annotations, global caches or
cross-invocation reuse are introduced.

Type, operand, instruction, text and declaration-planner projections require
operation-specific one-use permits and reservation before materialization. The
planner receives declarations plus neutral function headers, never source bodies.
Its neutral metadata is not evidence that actual source metadata was admitted.
Compiler-enforced constructor privacy, native class aliasing/copy ABI and physical
allocation capacities are separate qualification gates.

## Current dependency reconciliation

The nine historical shared dependencies remain unchanged in this integration.
Four match the packet: `mir_instruction_support`, `mir_instruction_kinds`,
`hir_operators` and `decl_attrs`. The five differing dependencies were compared to
B/provider-component/revision2/dependencies:

| Current dependency difference | Foundation disposition |
|---|---|
| `mir_types`: source-symbol field replaced by three short-borrow fields on `MirLocal` | No rich local projection exists here. Preserve current layout; source capture must classify provenance separately. |
| `mir_instruction_graph`: `MirFunction` removes loop-site field, adds `nogc_strict` and `short_call_contracts`; body helpers and deterministic emission ordering also changed | Adapt only the new projection: reserve 36 rather than 35 function fields; explicitly supply neutral no-GC, short-call and enum metadata. Preserve all current helpers. |
| `hir_types`: representation and no-GC module metadata added | New leaves import `SymbolId`; no rich HIR module construction. Source admission remains a follow-on. |
| `hir_definitions`: assignment operator optional; historical loop invariants absent | No imported rich statement/block constructor. Do not restore historical fields or visitors. |
| `Span`: same-line merged-column correction | Raw explicit six-field span projection remains unchanged and retains original length. No merge operation is used. |

Only three of the ten imported files differ from their reviewed after-images:
projection implementation, projection SSpec and its authored manual. The new ninth
projection scenario independently inventories the current one-function Unit
signature reservation: 510 scalar slots for the permit path and 516 including
two text-export permits. A 509-slot allowance refuses the 290-slot function
skeleton reservation after retaining 220 earlier slots. The current layout adds
five logical slots relative to the historical one-function envelope. These
counts describe the frozen source copy model; they are not allocator bytes.

Static integration checks on 2026-10-25: both working and staged direct-env
runtime guards returned PASS; executable-spec layout count under `doc/06_spec`
was zero; staged whitespace validation found no errors; scoped source/spec scan
found no placeholder passes. Hash comparison confirmed seven exact imports and
the three documented adaptations. These checks establish only source/layout
hygiene. Astra reviewed the corrected 510/516/509 oracle and the 36-field
adaptation with source-scoped GO; no runtime evidence followed from that review.

## Evidence and remaining gates

Seven account, 21 owner and nine projection scenarios are authored against the
actual production APIs. All 37 remain UNRUN without an admitted compiled SSpec
producer. The three manual mirrors remain explicitly authored/UNRUN; docgen and
`sspec-maintain` have not executed. Source review, checksums and scenario counts
cannot establish behavioral PASS or 80% branch coverage.

The required compiler/library/MCP/LSP checks, core runtime and MCP native smokes,
performance/RSS measurements and full-route source execution remain TEST_BLOCKED
under the same runner qualification gate. Stage 2 diagnostic admission does not
authorize general SPipe/docgen or release evidence. No Rust seed fallback, new
test runner or full bootstrap is introduced by this foundation.

Follow-on scope and owner assignments are in
[the task packet](../../03_plan/agent_tasks/c4_account_provider_foundation_v1.md);
the [test plan](../../03_plan/sys_test/c4_account_provider_foundation_v1.md)
retains executable/manual mapping and admission requirements. Full physical
provider accounting remains OPEN.
