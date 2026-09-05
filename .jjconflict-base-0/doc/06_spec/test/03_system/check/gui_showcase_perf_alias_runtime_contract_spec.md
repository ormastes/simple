# GUI Showcase Perf Alias Runtime Contract

> Validates that retained 4K and 8K GUI showcase performance evidence cannot pass when the native alias path reports raw `rt_*` usage. This keeps the 200 FPS GUI showcase lane on the pure Simple retained renderer path instead of accepting a runtime shortcut as performance evidence.

<!-- sdn-diagram:id=gui_showcase_perf_alias_runtime_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_showcase_perf_alias_runtime_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_showcase_perf_alias_runtime_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_showcase_perf_alias_runtime_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Alias Runtime Contract

Validates that retained 4K and 8K GUI showcase performance evidence cannot pass when the native alias path reports raw `rt_*` usage. This keeps the 200 FPS GUI showcase lane on the pure Simple retained renderer path instead of accepting a runtime shortcut as performance evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_alias_runtime_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that retained 4K and 8K GUI showcase performance evidence cannot pass
when the native alias path reports raw `rt_*` usage. This keeps the 200 FPS GUI
showcase lane on the pure Simple retained renderer path instead of accepting a
runtime shortcut as performance evidence.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- A retained 4K row with `alias_raw_rt_count=1` is normalized to `fail`.
- A retained 8K row with `alias_raw_rt_count=1` is normalized to `fail`.
- The failure reasons are `raw-rt-in-4k-alias:1` and `raw-rt-in-8k-alias:1`.
- The aggregate forwards the raw runtime alias count into final evidence.
- All surrounding backend, timing, RSS, checksum, source, native, and fallback
  fields remain valid so the raw-runtime gate is the first failing condition.

## Scenarios

### GUI showcase perf alias runtime contract

#### rejects retained 4K and 8K rows that use raw runtime aliases

- Create and aggregate a retained 4K row with raw runtime alias usage
   - Expected: code_4k equals `0`
- Create and aggregate a retained 8K row with raw runtime alias usage
   - Expected: code_8k equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create and aggregate a retained 4K row with raw runtime alias usage")
val command_4k = retained_4k_raw_rt_command("build/test-gui-showcase-perf-alias-runtime-contract-4k")
val (_stdout_4k, _stderr_4k, code_4k) = process_run("/bin/sh", ["-c", command_4k])
expect(code_4k).to_equal(0)
val evidence_4k = file_read("build/test-gui-showcase-perf-alias-runtime-contract-4k/out/evidence.env")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_reason=raw-rt-in-4k-alias:1")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_alias_raw_rt_count=1")

step("Create and aggregate a retained 8K row with raw runtime alias usage")
val command_8k = retained_8k_raw_rt_command("build/test-gui-showcase-perf-alias-runtime-contract-8k")
val (_stdout_8k, _stderr_8k, code_8k) = process_run("/bin/sh", ["-c", command_8k])
expect(code_8k).to_equal(0)
val evidence_8k = file_read("build/test-gui-showcase-perf-alias-runtime-contract-8k/out/evidence.env")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_reason=raw-rt-in-8k-alias:1")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_alias_raw_rt_count=1")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md](doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
