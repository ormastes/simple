# gui_vs_tauri_spec

> test/perf/tauri_equiv/gui_vs_tauri_spec.spl

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gui_vs_tauri_spec

test/perf/tauri_equiv/gui_vs_tauri_spec.spl

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-9 — Tauri-equivalent benchmark: |
| Category | Performance \| GUI \| Tauri |
| Status | Pending implementation (Phase 5) |
| Source | `test/perf/tauri_equiv/gui_vs_tauri_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

test/perf/tauri_equiv/gui_vs_tauri_spec.spl

  startup, windows, scroll, IPC, memory; reports vs baseline.
Verifies that the Tauri-equivalent benchmark:
  - Runs startup, new_window, close, resize, scroll, route_change, ipc, event_broadcast, idle_memory
  - Reports Tauri renderer identity and Simple backend identity
  - Fails the Tauri-equivalent performance claim when NFR ratios are missed
  - Reference kind is "rust-tauri"

@cover test/perf/tauri_equiv/workflow_driver.spl
@cover test/perf/tauri_equiv/report_spec.spl
@cover test/perf/tauri_equiv/simple_app.spl

Purpose and audience: AC-9 Tauri-equivalence benchmark schema and NFR
ratio gate evidence for GUI performance engineers; scope is the report
model, 9-workflow coverage, per-workflow pass/fail math, and memory rows.

@req REQ-PERF-TAURI-EQUIV
research: doc/01_research/platform/simple_tauri.md ; research: doc/01_research/ui/render_path/electron_tauri_vulkan_enablement_2026-06-16.md

## Scenarios

### gui_vs_tauri — AC-9: Tauri-equivalent benchmark

### report schema

#### AC-9: reference_kind is rust-tauri

- operator verifies: AC-9: reference_kind is rust-tauri
   - Expected: b.reference_kind equals `REF_KIND_TAURI`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: reference_kind is rust-tauri")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.reference_kind).to_equal(REF_KIND_TAURI)
```

</details>

#### AC-9: tauri_renderer field is non-empty

- operator verifies: AC-9: tauri_renderer field is non-empty
   - Expected: b.tauri_renderer equals `wry/webkit`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: tauri_renderer field is non-empty")
val b: TauriBenchReport = make_tauri_bench_ok()
# oracle: wry/webkit is the fixed renderer identity the report must carry.
expect(b.tauri_renderer).to_equal("wry/webkit")
```

</details>

#### AC-9: simple_backend field is non-empty

- operator verifies: AC-9: simple_backend field is non-empty
   - Expected: b.simple_backend equals `simple_cpu_scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: simple_backend field is non-empty")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.simple_backend).to_equal("simple_cpu_scalar")
```

</details>

#### AC-9: sample_count is greater than zero

- operator verifies: AC-9: sample_count is greater than zero
   - Expected: b.sample_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: sample_count is greater than zero")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.sample_count > 0).to_equal(true)
```

</details>

#### AC-9: warmup_count is greater than zero

- operator verifies: AC-9: warmup_count is greater than zero
   - Expected: b.warmup_count > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: warmup_count is greater than zero")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.warmup_count > 0).to_equal(true)
```

</details>

### workflow coverage (9 workflows)

#### AC-9: nine workflows are recorded

- operator verifies: AC-9: nine workflows are recorded
   - Expected: b.workflows.len() equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: nine workflows are recorded")
val b: TauriBenchReport = make_tauri_bench_ok()
# oracle: 9 = the fixed AC-9 workflow set recorded in make_tauri_bench_ok.
expect(b.workflows.len()).to_equal(9)
```

</details>

#### AC-9: first workflow is startup

- operator verifies: AC-9: first workflow is startup
   - Expected: b.workflows[0].workflow equals `WORKFLOW_STARTUP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: first workflow is startup")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[0].workflow).to_equal(WORKFLOW_STARTUP)
```

</details>

#### AC-9: new_window workflow is present

- operator verifies: AC-9: new_window workflow is present
   - Expected: b.workflows[1].workflow equals `WORKFLOW_NEW_WINDOW`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: new_window workflow is present")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[1].workflow).to_equal(WORKFLOW_NEW_WINDOW)
```

</details>

#### AC-9: ipc workflow is present

- operator verifies: AC-9: ipc workflow is present
   - Expected: b.workflows[6].workflow equals `WORKFLOW_IPC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: ipc workflow is present")
val b: TauriBenchReport = make_tauri_bench_ok()
# oracle: index 6 is the ipc row of the fixed 9-row layout.
expect(b.workflows[6].workflow).to_equal(WORKFLOW_IPC)
```

</details>

#### AC-9: idle_memory workflow is last

- operator verifies: AC-9: idle_memory workflow is last
   - Expected: b.workflows[8].workflow equals `WORKFLOW_IDLE_MEMORY`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: idle_memory workflow is last")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[8].workflow).to_equal(WORKFLOW_IDLE_MEMORY)
```

</details>

### pass/fail per workflow

#### AC-9: startup workflow passes when ratio <= NFR_TAURI_RATIO_THRESHOLD

- operator verifies: AC-9: startup workflow passes when ratio <= NFR_TAURI_RATIO_THRESHOLD
   - Expected: wf.pass is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: startup workflow passes when ratio <= NFR_TAURI_RATIO_THRESHOLD")
val wf: TauriWorkflowResult = make_workflow(WORKFLOW_STARTUP, 1200000, 1000000, 45000)
expect(wf.pass).to_equal(true)
```

</details>

#### AC-9: scroll workflow passes when simple_us is close to tauri_us

- operator verifies: AC-9: scroll workflow passes when simple_us is close to tauri_us
   - Expected: wf.pass is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: scroll workflow passes when simple_us is close to tauri_us")
val wf: TauriWorkflowResult = make_workflow(WORKFLOW_SCROLL, 5000, 4000, 200)
expect(wf.pass).to_equal(true)
```

</details>

#### AC-9: workflow fails when simple is more than 1.5x Tauri

- operator verifies: AC-9: workflow fails when simple is more than 1.5x Tauri
   - Expected: wf.pass is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: workflow fails when simple is more than 1.5x Tauri")
val wf: TauriWorkflowResult = make_workflow(WORKFLOW_STARTUP, 2000000, 1000000, 45000)
expect(wf.pass).to_equal(false)
```

</details>

#### AC-9: simple_us is greater than zero for non-idle workflows

- operator verifies: AC-9: simple_us is greater than zero for non-idle workflows
   - Expected: b.workflows[0].simple_us > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: simple_us is greater than zero for non-idle workflows")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[0].simple_us > 0).to_equal(true)
```

</details>

#### AC-9: tauri_us is greater than zero for non-idle workflows

- operator verifies: AC-9: tauri_us is greater than zero for non-idle workflows
   - Expected: b.workflows[0].tauri_us > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: tauri_us is greater than zero for non-idle workflows")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[0].tauri_us > 0).to_equal(true)
```

</details>

### memory reporting

#### AC-9: idle_memory rss_kb is greater than zero

- operator verifies: AC-9: idle_memory rss_kb is greater than zero
   - Expected: b.workflows[8].rss_kb > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: idle_memory rss_kb is greater than zero")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[8].rss_kb > 0).to_equal(true)
```

</details>

#### AC-9: startup rss_kb is greater than zero

- operator verifies: AC-9: startup rss_kb is greater than zero
   - Expected: b.workflows[0].rss_kb > 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-PERF-TAURI-EQUIV
step("operator verifies: AC-9: startup rss_kb is greater than zero")
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[0].rss_kb > 0).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-PERF-TAURI-EQUIV`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `727cd3c29f45a541b2cabe805a780ee2749dcc4c2dff5d119950bb1b90218925`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `727cd3c29f45a541b2cabe805a780ee2749dcc4c2dff5d119950bb1b90218925`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `727cd3c29f45a541b2cabe805a780ee2749dcc4c2dff5d119950bb1b90218925`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/perf/tauri_equiv/gui_vs_tauri_spec.spl
mirror: doc/06_spec/perf/tauri_equiv/gui_vs_tauri_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/perf/tauri_equiv/gui_vs_tauri_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/perf/tauri_equiv/gui_vs_tauri_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/perf/tauri_equiv/gui_vs_tauri_spec.spl:1:1: advice SSDOC-MNT-007 [maintainability] (-10): research, plan, architecture, or design metadata links are incomplete
  why: Reviewers need selected lifecycle evidence, not inferred project state.
  improve: Link the selected lifecycle artifacts or configure a reasoned scope suppression.
test/perf/tauri_equiv/gui_vs_tauri_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/perf/tauri_equiv/gui_vs_tauri_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-9: reference_kind is rust-tauri' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/tauri_equiv/gui_vs_tauri_spec.spl:98:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-9: tauri_renderer field is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/perf/tauri_equiv/gui_vs_tauri_spec.spl:105:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AC-9: simple_backend field is non-empty' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
