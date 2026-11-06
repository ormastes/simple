# Node attributes: verification and system-test plan

Date: 2026-11-06. Status: planned tests; no executions claimed.
Requirements: [feature](../../02_requirements/feature/node_attributes.md) and
[NFR](../../02_requirements/nfr/node_attributes.md).

## Planned executable surfaces

- Unit contracts: `test/01_unit/common/structural/node_attribute_schema_spec.spl`
  and `node_attribute_lifecycle_spec.spl` in that directory.
- Compiler integration: `test/02_integration/compiler/node_attributes_spec.spl`.
- System scenario: `test/03_system/app/compiler/feature/node_attributes_spec.spl`.
- Generated manual: `doc/06_spec/03_system/app/compiler/feature/node_attributes_spec.md`.
- Native fixtures: admitted compiler/backend fixtures under `test/fixtures/compiler/node_attributes/`.

These names are planned, not existing/passing test claims. Author executable
scenarios alongside the corresponding implementation using real assertions. Do
not create empty bodies or passing TODOs for this documentation landing. Generated
manuals require admitted SPipe/docgen execution and human-readable review.

## Requirement-to-evidence matrix

| Requirement | Scenario and required oracle |
|---|---|
| REQ-001 | Equivalent SPL/SDN schemas produce equal normalized descriptors; conflicting nominal types/defaults/authority show both origins; unauthorized owner injection fails. |
| REQ-002 | Side-effecting receiver/RHS/index fixtures record order and single evaluation; nested/indexed writes change the intended owner; move/borrow/atomic negative cases reject. |
| REQ-003 | Missing/repeated initialization, default failure/retry, optional None, discard/cancel and unresolved scope exit; destructor/resource counts prove exactly-once cleanup. |
| REQ-004 | Wrong store/view/region, reset, removal/reuse and exhausted generations reject stale handles; ready valid access succeeds without a public tag. |
| REQ-005 | Ordered children and duplicates preserved; parent/cycle violations fail; group failure publishes no member and cannot leak pending dereferences. |
| REQ-006 | Direct/column/sparse representations return equal logical values; missing physical entries differ from stored None; unsupported physical mappings reject. |
| REQ-007 | Same source fixture/result/error/order across admitted native and interpreter lanes; both Pure-Simple evaluator paths exercised; Rust reference evidence labeled separately. |
| REQ-008 | Canonical get/set selectors with spacing/Boolean variations; exact successful-event counts; no helper/backing-store duplicates or success event on failure. |
| REQ-009 | Static off/prepared disabled/active modes; missing instrumentation/wrong map/provider fails; saturation/drop/recursion stays bounded and honest. |
| REQ-010 | Two simultaneous contexts remain isolated; schema/physical/profile changes invalidate the correct keys; stale receipts and incomplete reverse projections fail closed. |
| REQ-011 | Real Simple parse/resolve/lower workload traverses managed node owners; BuildRunner cannot bypass DAG/attempt/output validation via a setter. |
| REQ-012 | NA-OFF-01: ordinary disabled fixture baseline; NA-OFF-02: managed declaration disabled diagnostic; NA-OFF-03: no generated/observer dependencies; NA-OFF-04: no live safety toggle. |
| REQ-013 | PR sequence shows design before structural implementation before consumer adoption; full completion report accounts for all later gates. |
| REQ-014 | NA-TOOLS-01–03: LSP origin/type, generated target and physical/rejection explanation agree with the compiler's frozen plan. |
| REQ-015 | Migration failure preserves authoritative state; leases block incompatible conversion; callback migration is rejected; next-build/snapshot works without general shared migration. |

The source report's ATTR/AOP/LAY/COL/XR/MIG/RUN/CACHE inventory remains normative
for applicable paths. The matrix groups tests; it does not delete its edge cases.
Optional unsupported capabilities need refusal tests and truthful status, not a
claim that a different provider executed the requested operation.

## Manual flow and helpers

Canonical scenario step names: `Resolve one schema from source and configuration`,
`Build and finalize a typed node`, `Read and update ordinary fields`,
`Reject stale and unauthorized access`, `Observe one logical operation`,
`Compile Simple with managed nodes`, `Compare disabled and enabled builds`.

Planned shared helpers: `node_attribute_fixture`, `compile_node_attribute_fixture`,
`expect_node_attribute_diagnostic`, `expect_node_attribute_trace`, and
`assert_node_attribute_runtime_admitted`. Define typed results and actual command
receipts before implementation; do not land silent mock helpers. Use built-in
matchers (`to_equal`, `to_contain`, etc.) and real artifact/protocol/exec evidence.
No TUI/GUI is proposed; CLI/LSP diagnostics need text/protocol captures, not
invented screenshots.

## Qualification gates

Record runtime path/hash/stage/lineage, source revision, backend/target/provider,
commands, test counts and exits. Missing admitted runtime is TEST_BLOCKED, never
a seed fallback or authored-spec PASS. Run each unchanged green criterion once;
at most six evidence-changing fix/verify cycles, per repository policy.

For compiler/lib changes, include compiler/lib/MCP/LSP checks, the MCP stdio
integration scenario, core runtime and MCP native smoke. Package smoke applies
only if package/publication paths change. Run both direct-env guards, verify no
`*_spec.spl` exists below `doc/06_spec`, generate/review manuals and run
`sspec-maintain scan` on changed pairs. Report coverage and NFR evidence explicitly.
Do not infer production readiness from a documentation-only check.
