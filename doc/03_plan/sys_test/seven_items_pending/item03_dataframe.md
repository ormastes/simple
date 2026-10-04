# Item 3: typed DataFrame collections and query optimizer

Status: NOT_IMPLEMENTED acceptance scenarios. This status describes the new scenario bodies, not the implementation status of the product. Criteria were authored before their SSpec skeletons. No tests or compilers were run.

Executable skeleton: [item03_dataframe_spec.spl](../../../../test/03_system/seven_items_pending/item03_dataframe_spec.spl).

## Sources and existing coverage

Canonical umbrella: [seven-item host completion plan](../../seven_plans_host_completion_2026-09-29.md), item 3. References: [selected functional requirements](../../../02_requirements/feature/collection_planner.md), [balanced NFRs](../../../02_requirements/nfr/collection_planner.md), [collection plan research](../../../01_research/compiler/collection_planner/collection_plan_ir_2026-07-31.md), [detailed system plan](../collection_planner.md).

The detailed system plan lists narrower DataFrame merge/group_by/value_counts/scalar-broadcast specs and registry/extraction/selection unit specs. They do not prove production end-to-end lowering. Its declared `test/03_system/app/compiler/feature/collection_planner_spec.spl` is absent in the inspected authoritative DEV tree. These new umbrella scenarios connect prerequisite gates through emitted-plan execution and host/performance evidence; they do not replace existing narrower assertions. AC01 covers the research P0 gate, AC02–03 typed/index substrate, AC04–08 registry/extraction/lowering/adaptation, and AC09–11 explanation/performance/host completion.

The new scenarios are umbrella end-to-end campaigns. They preserve the existing detailed tests and requirements; they neither replace those catalogs nor certify completion. Windows first, then Linux/WSL is execution ordering, not removal of other supported hosts.

## Acceptance criteria

### S7-I03-AC01: semantic prerequisites gate optimized collection execution

- Requirements: REQ-002 NFR-001 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Same fixtures for array map/filter/flat_map/any/all, captured closures and colliding Dict insertion across interpreter, JIT, LLVM AOT, self-hosted native and bootstrap routes.
- Action: Run actual compiler/runtime entrypoints and inspect outputs, callback order, closure results and referenced runtime-symbol resolution before enabling rewrites.
- Observable result: All routes agree including empty any/all and early exits; referenced symbols resolve; a missing symbol or unproven closure/Dict path blocks optimized execution rather than silently falling back while claiming parity.

### S7-I03-AC02: typed DataFrame columns preserve boundary values

- Requirements: REQ-001 NFR-001 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Typed numeric and generic columns with NaN, signed zero, duplicate keys, missing optionals and dtype mismatch controls.
- Action: Round-trip through actual column operations and run filter/projection/grouping/aggregation against the reference path.
- Observable result: Element/key types persist; NaN does not match, signed zeros compare as contracted, stable duplicates and first/last/unique policies hold, missing values remain explicit and dtype mismatches produce matching errors.

### S7-I03-AC03: generic indexes preserve collection semantics under collisions

- Requirements: REQ-004 REQ-005 NFR-001 NFR-002 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Text, integer, enum, tuple and interned-symbol keys with forced collisions, resize/removal boundaries and unavailable hash/equality implementations.
- Action: Execute generic HashMap/HashSet operations and indexed unique/group_by through production code, comparing a reference implementation.
- Observable result: Lookup/insertion/removal remain correct after collisions and resize; first-seen group/unique order and duplicates survive; unsupported keys take explicit correct fallback or refusal, and operation counts expose quadratic behavior rather than hiding it behind timing.

### S7-I03-AC04: one typed registry drives diagnostics and backend resolution

- Requirements: REQ-003 REQ-006 NFR-006 NFR-007 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Versioned registry, equivalent functional chains and explicit loops, bounded intentional cases and duplicate/stale/backend-symbol mismatch rows.
- Action: Load through the production compiler, run typed COLL diagnostics and resolve code-generation symbols.
- Observable result: One registry binds receiver/key/effect/cardinality/cost/order facts; equivalent code receives equivalent explained complexity analysis, bounded work is justified, and duplicate/stale/mismatched bindings refuse rather than inventing facts.

### S7-I03-AC05: logical extraction proves legality before changing execution

- Requirements: REQ-007 REQ-008 NFR-001 NFR-006 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Equivalent typed chains/loops with known and unknown effects, source spans and a malformed/cyclic plan control.
- Action: Extract through the actual compilation pipeline, validate the semantic DAG and carry proof/blocker receipts into lowering.
- Observable result: Equivalent inputs expose equivalent semantics; extraction is linear in visited HIR, unknown facts cannot authorize rewrites, malformed plans reject and the original HIR execution remains available with recorded fallback.

### S7-I03-AC06: fused MIR preserves observable effects and ownership

- Requirements: REQ-008 NFR-001 NFR-004 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Eligible map/filter pipelines and controls with throw, mutation, aliasing, captured closure, short-circuit and suspension behavior.
- Action: Compile and execute selected fused and original paths while observing emitted MIR, callback events and allocation behavior.
- Observable result: Eligible work executes one actual MIR loop without intermediate collections/closure allocation; outputs, errors, ownership and callback count/order agree; unsafe fusion retains the original path instead of losing effects.

### S7-I03-AC07: physical joins execute selected implementations with output costs

- Requirements: REQ-005 REQ-009 NFR-001 NFR-004 NFR-007 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Semi/anti joins, first/all matches, frequency/distinct/intersection fixtures with sorted/unsorted keys, skew, duplicates and a configured memory cap.
- Action: Generate nested/hash/merge/direct-index candidates, select and lower through production compilation, then compare actual execution with reference results.
- Observable result: Receipts identify the implementation that ran and build/probe/output work; ordering and multiplicity remain correct, all-equal output cost is counted, illegal candidates explain refusal and over-cap memory plans reject before MIR lowering.

### S7-I03-AC08: profiles and semantic cache changes cannot legalize unsafe rewrites

- Requirements: REQ-010 NFR-001 NFR-006 NFR-007 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Valid and stale .sprof records pinned to function, callee summaries, registry version, target/backend, policy and epoch.
- Action: Compile with missing/valid profiles, vary each cache identity component and replay the same valid configuration.
- Observable result: Valid evidence may change guarded physical choice but not legality; stale/missing evidence preserves correct original behavior; affected plans invalidate and identical inputs reproduce the same plan without repeated hot-path full-tree work.

### S7-I03-AC09: explanations correspond to emitted plans and differential outcomes

- Requirements: REQ-006 REQ-011 NFR-001 NFR-007 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Actual eligible and rejected rewrites with source spans, retained reference execution and backend-specific plan receipts.
- Action: Request explain output, inspect selected MIR/plan identity, execute differential fixtures and connect results to generated manual traceability.
- Observable result: Original/selected complexity, alternatives, blockers, memory, profile and fallback reasons correspond to the emitted implementation; an advisory-only chooser or timing-only inference cannot qualify actual optimized execution.

### S7-I03-AC10: scaling runtime memory and compiler latency meet selected budgets

- Requirements: REQ-004 REQ-009 REQ-011 NFR-002 NFR-003 NFR-004 NFR-005 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Same-revision optimized/reference fixtures with 1k/2k/4k/8k bounded-output workloads and separate all-equal skew, fixed machine/target/backend/build flags and at least five warm runs.
- Action: Count equality/hash/comparison/build/probe/emitted work and measure runtime, peak RSS, compiler startup and analysis requests; retain cold startup too.
- Observable result: Endpoint log(count8000/count1000)/log(8) is at most 1.15 with all four counts retained; no case exceeds 10% median runtime, 20% median RSS or 5% warm compiler startup/request regression; cold startup is reported without inventing a gate and semantic parity precedes performance qualification.

### S7-I03-AC11: host and backend matrices retain explicit incomplete cells

- Requirements: REQ-002 REQ-011 NFR-001 NFR-007 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Supported host/architecture/backend matrix with immutable compiler/runtime/fixture identities; separate Windows native, WSL/Linux, native Linux, macOS, FreeBSD and claimed SimpleOS guest lanes.
- Action: Run prerequisite, typed-column, lowering and differential campaigns for every claimed cell and retain exact command/result/plan evidence.
- Observable result: Every claimed cell demonstrates actual lowered execution and semantic equivalence; missing runner/symbol/feature remains incomplete with a specific diagnostic, x86-64 does not certify ARM64, and source inspection or a narrow DataFrame unit pass cannot close the system matrix.
