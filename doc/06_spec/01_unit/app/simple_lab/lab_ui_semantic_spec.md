# lab_ui_semantic_spec

> Simple Lab UI semantic-state spec (Stream L, task L2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# lab_ui_semantic_spec

Simple Lab UI semantic-state spec (Stream L, task L2).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Simple Lab UI semantic-state spec (Stream L, task L2).

S1/S2-level per the repo's semantic UI contract convention
(`src/lib/common/ui/semantic_contract.spl`, mirrored by
`test/01_unit/app/ui/semantic_contract_spec.spl` and
`test/01_unit/app/ui/semantic_backend_helpers_spec.spl`): drive the app
through `SemanticUiCommand` + `semantic_ui_command_to_event`, read state back
through `semantic_ui_snapshot_from_state_with_capabilities`'s element/prop
list — never by poking the widget tree directly.

Covers: cell add, cell source edit, cell run (through the in-process
`KernelSessionManager`, K1, backed by the shared `LocalExec`/`LocalExecFactory`
real executor in `std.notebook.local_exec` — K2's shared implementation,
retired the earlier Lab-only `lab_executor.spl` stand-in), and output
read-after-write.

Design: doc/05_design/app/tools/notebook_lanes_architecture.md §7.1
Plan:   doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md (Stream L, L2)

## Scenarios

### Simple Lab UI (semantic state, S1)

#### starts with one empty cell

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- starts with one empty cell
   - Expected: _lab_prop(snapshot, "cell_0_editor", "value") equals ``
   - Expected: _lab_prop(snapshot, "cell_0_output", "content") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("starts with one empty cell")
val app = SimpleLabApp.create()
val snapshot = _lab_snapshot(app)
assert_true(_lab_element_exists(snapshot, "cell_0"))
assert_false(_lab_element_exists(snapshot, "cell_1"))
expect(_lab_prop(snapshot, "cell_0_editor", "value")).to_equal("")
expect(_lab_prop(snapshot, "cell_0_output", "content")).to_equal("")
```

</details>

#### adds a cell through the shared command vocabulary (read-after-write)

- adds a cell through the shared command vocabulary (read-after-write)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("adds a cell through the shared command vocabulary (read-after-write)")
val app = SimpleLabApp.create()
_lab_dispatch_action(app, "lab_add_cell")
val snapshot = _lab_snapshot(app)
assert_true(_lab_element_exists(snapshot, "cell_0"))
assert_true(_lab_element_exists(snapshot, "cell_1"))
```

</details>

#### edits a cell's source through InputChange (read-after-write)

- edits a cell's source through InputChange (read-after-write)
   - Expected: _lab_prop(snapshot, "cell_0_editor", "value") equals `print("42 from Simple Lab")`
   - Expected: _lab_prop(snapshot, "cell_0_output", "content") equals ``
   - Expected: _lab_prop(snapshot, "cell_0_lane_badge", "content") equals `not run`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("edits a cell's source through InputChange (read-after-write)")
val app = SimpleLabApp.create()
_lab_dispatch_type(app, "cell_0_editor", "print(\"42 from Simple Lab\")")
val snapshot = _lab_snapshot(app)
expect(_lab_prop(snapshot, "cell_0_editor", "value")).to_equal("print(\"42 from Simple Lab\")")
expect(_lab_prop(snapshot, "cell_0_output", "content")).to_equal("")
expect(_lab_prop(snapshot, "cell_0_lane_badge", "content")).to_equal("not run")
```

</details>

#### runs a cell through KernelSessionManager and reads the captured output back

- runs a cell through KernelSessionManager and reads the captured output back
   - Expected: _lab_prop(snapshot, "cell_0_lane_badge", "content") equals `available`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("runs a cell through KernelSessionManager and reads the captured output back")
val app = SimpleLabApp.create()
_lab_dispatch_type(app, "cell_0_editor", "print(\"42 from Simple Lab\")")
_lab_dispatch_action(app, "cell_run_0")
val snapshot = _lab_snapshot(app)
expect(_lab_prop(snapshot, "cell_0_output", "content")).to_contain("42 from Simple Lab")
expect(_lab_prop(snapshot, "cell_0_lane_badge", "content")).to_equal("available")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9bf2e00acb537da46a97fb63fdaba889038f0836c65e235d8fb4a1654b58bd75`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9bf2e00acb537da46a97fb63fdaba889038f0836c65e235d8fb4a1654b58bd75`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9bf2e00acb537da46a97fb63fdaba889038f0836c65e235d8fb4a1654b58bd75`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl
mirror: doc/06_spec/01_unit/app/simple_lab/lab_ui_semantic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/simple_lab/lab_ui_semantic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_lab/lab_ui_semantic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'starts with one empty cell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'adds a cell through the shared command vocabulary (read-after-write)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_lab/lab_ui_semantic_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'edits a cell's source through InputChange (read-after-write)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
