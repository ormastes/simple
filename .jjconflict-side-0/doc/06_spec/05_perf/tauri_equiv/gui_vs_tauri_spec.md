# gui_vs_tauri_spec

> test/perf/tauri_equiv/gui_vs_tauri_spec.spl

<!-- sdn-diagram:id=gui_vs_tauri_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_vs_tauri_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_vs_tauri_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_vs_tauri_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Source | `test/05_perf/tauri_equiv/gui_vs_tauri_spec.spl` |
| Updated | 2026-06-01 |
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

## Scenarios

### gui_vs_tauri — AC-9: Tauri-equivalent benchmark

### report schema

#### AC-9: reference_kind is rust-tauri

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.reference_kind).to_equal(REF_KIND_TAURI)
```

</details>

#### AC-9: tauri_renderer field is non-empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.tauri_renderer).to_equal("wry/webkit")
```

</details>

#### AC-9: simple_backend field is non-empty

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.simple_backend).to_equal("simple_cpu_scalar")
```

</details>

#### AC-9: sample_count is greater than zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.sample_count > 0).to_equal(true)
```

</details>

#### AC-9: warmup_count is greater than zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.warmup_count > 0).to_equal(true)
```

</details>

### workflow coverage (9 workflows)

#### AC-9: nine workflows are recorded

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows.len()).to_equal(9)
```

</details>

#### AC-9: first workflow is startup

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[0].workflow).to_equal(WORKFLOW_STARTUP)
```

</details>

#### AC-9: new_window workflow is present

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[1].workflow).to_equal(WORKFLOW_NEW_WINDOW)
```

</details>

#### AC-9: ipc workflow is present

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[6].workflow).to_equal(WORKFLOW_IPC)
```

</details>

#### AC-9: idle_memory workflow is last

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[8].workflow).to_equal(WORKFLOW_IDLE_MEMORY)
```

</details>

### pass/fail per workflow

#### AC-9: startup workflow passes when ratio <= NFR_TAURI_RATIO_THRESHOLD

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wf: TauriWorkflowResult = make_workflow(WORKFLOW_STARTUP, 1200000, 1000000, 45000)
expect(wf.pass).to_equal(true)
```

</details>

#### AC-9: scroll workflow passes when simple_us is close to tauri_us

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wf: TauriWorkflowResult = make_workflow(WORKFLOW_SCROLL, 5000, 4000, 200)
expect(wf.pass).to_equal(true)
```

</details>

#### AC-9: workflow fails when simple is more than 1.5x Tauri

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val wf: TauriWorkflowResult = make_workflow(WORKFLOW_STARTUP, 2000000, 1000000, 45000)
expect(wf.pass).to_equal(false)
```

</details>

#### AC-9: simple_us is greater than zero for non-idle workflows

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[0].simple_us > 0).to_equal(true)
```

</details>

#### AC-9: tauri_us is greater than zero for non-idle workflows

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[0].tauri_us > 0).to_equal(true)
```

</details>

### memory reporting

#### AC-9: idle_memory rss_kb is greater than zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val b: TauriBenchReport = make_tauri_bench_ok()
expect(b.workflows[8].rss_kb > 0).to_equal(true)
```

</details>

#### AC-9: startup rss_kb is greater than zero

<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
