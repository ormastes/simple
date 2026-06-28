# GUI Showcase Perf Backend Contract

> Validates that retained 4K and 8K GUI showcase performance evidence must come from the canonical retained widget showcase backend. A producer cannot satisfy completion by reporting a generic or unrelated backend label.

<!-- sdn-diagram:id=gui_showcase_perf_backend_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_showcase_perf_backend_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_showcase_perf_backend_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_showcase_perf_backend_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Showcase Perf Backend Contract

Validates that retained 4K and 8K GUI showcase performance evidence must come from the canonical retained widget showcase backend. A producer cannot satisfy completion by reporting a generic or unrelated backend label.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/gui_showcase_perf_backend_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that retained 4K and 8K GUI showcase performance evidence must come
from the canonical retained widget showcase backend. A producer cannot satisfy
completion by reporting a generic or unrelated backend label.

**Plan:** doc/03_plan/agent_tasks/vulkan_backed_web_gui_renderdoc_parallel_plan.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- A retained 4K row with `backend=wrong-backend` is normalized to `fail`.
- A retained 8K row with `backend=wrong-backend` is normalized to `fail`.
- The failure reasons are `invalid-4k-backend:wrong-backend` and
  `invalid-8k-backend:wrong-backend`.
- All surrounding timing, RSS, checksum, retained-mode, source, native, and
  fallback fields remain valid so the backend classifier is the first failing
  gate.

## Scenarios

### GUI showcase perf backend contract

#### rejects retained 4K and 8K rows with non-canonical backend labels

- Create and aggregate a retained 4K row with a wrong backend
   - Expected: code_4k equals `0`
- Create and aggregate a retained 8K row with a wrong backend
   - Expected: code_8k equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Create and aggregate a retained 4K row with a wrong backend")
val command_4k = retained_4k_backend_command("build/test-gui-showcase-perf-backend-contract-4k")
val (_stdout_4k, _stderr_4k, code_4k) = process_run("/bin/sh", ["-c", command_4k])
expect(code_4k).to_equal(0)
val evidence_4k = file_read("build/test-gui-showcase-perf-backend-contract-4k/out/evidence.env")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_status=fail")
expect(evidence_4k).to_contain("gui_showcase_4k_200fps_reason=invalid-4k-backend:wrong-backend")

step("Create and aggregate a retained 8K row with a wrong backend")
val command_8k = retained_8k_backend_command("build/test-gui-showcase-perf-backend-contract-8k")
val (_stdout_8k, _stderr_8k, code_8k) = process_run("/bin/sh", ["-c", command_8k])
expect(code_8k).to_equal(0)
val evidence_8k = file_read("build/test-gui-showcase-perf-backend-contract-8k/out/evidence.env")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_status=fail")
expect(evidence_8k).to_contain("gui_showcase_8k_perf_reason=invalid-8k-backend:wrong-backend")
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
