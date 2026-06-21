# CPU SIMD Engine2D Diagram Evidence Spec

> This scenario is the release gate for CPU SIMD drawing evidence in the GUI hardening lane.

<!-- sdn-diagram:id=cpu_simd_engine2d_diagram_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=cpu_simd_engine2d_diagram_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

cpu_simd_engine2d_diagram_evidence_spec -> std
cpu_simd_engine2d_diagram_evidence_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=cpu_simd_engine2d_diagram_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU SIMD Engine2D Diagram Evidence Spec

This scenario is the release gate for CPU SIMD drawing evidence in the GUI hardening lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | .spipe/gui-hardening-full/state.md |
| Plan | doc/03_plan/agent_tasks/gui_backend_perf.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/cpu_simd_engine2d_diagram_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario is the release gate for CPU SIMD drawing evidence in the GUI
hardening lane.

## Examples

Run the scenario to confirm the evidence wrapper reports zero diagram
mismatches and records the exact-bitmap no-blur policy.

**Requirements:** .spipe/gui-hardening-full/state.md
**Plan:** doc/03_plan/agent_tasks/gui_backend_perf.md
**Design:** N/A
**Research:** N/A

## Scenarios

### CPU SIMD Engine2D diagram evidence

#### renders the SIMD-backed diagram exactly like the scalar reference _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 0:
    print "cpu simd engine2d evidence stdout: " + stdout
    print "cpu simd engine2d evidence stderr: " + stderr
expect(code).to_equal(0)
expect(stdout).to_contain("cpu_simd_evidence_status=pass")
expect(stdout).to_contain("cpu_simd_evidence_reason=runtime-evidence-verified")
expect(stdout).to_contain("cpu_simd_evidence_policy=exact-bitmap-no-blur-no-tolerance")
expect(stdout).to_contain("cpu_simd_evidence_blur_or_tolerance_used=false")
expect(stdout).to_contain("cpu_simd_evidence_diagram_pixel_count=192")
expect(stdout).to_contain("cpu_simd_evidence_diagram_mismatch_count=0")
expect(stdout).to_contain("cpu_simd_evidence_fill_mismatch_count=0")
expect(stdout).to_contain("cpu_simd_evidence_copy_mismatch_count=0")
expect(stdout).to_contain("cpu_simd_evidence_alpha_mismatch_count=0")
expect(stdout).to_contain("cpu_simd_evidence_scroll_mismatch_count=0")
expect(stdout).to_contain("cpu_simd_evidence_diagram_fill_hits=9")
expect(stdout).to_contain("cpu_simd_evidence_diagram_copy_hits=7")
expect(stdout).to_contain("cpu_simd_evidence_diagram_alpha_hits=9")
expect(stdout).to_contain("cpu_simd_evidence_diagram_blit_hits=1")
expect(stdout).to_contain("cpu_simd_evidence_diagram_scroll_hits=7")
expect(stdout).to_contain("cpu_simd_evidence_general_status=Initialized")
expect(stdout).to_contain("cpu_simd_evidence_log_bytes=")
expect(stdout).to_contain("cpu_simd_evidence_log_cksum=")

val report = file_read_text(_report_path(run_id))
expect(report).to_contain("# CPU SIMD Engine2D Evidence")
expect(report).to_contain("- status: pass")
expect(report).to_contain("- diagram pixel count: 192")
expect(report).to_contain("- diagram mismatch count: 0")
expect(report).to_contain("- policy: exact bitmap, no blur, no tolerance")
expect(report).to_contain("- evidence_log_bytes: ")
expect(report).to_contain("- evidence_log_cksum: ")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [.spipe/gui-hardening-full/state.md](.spipe/gui-hardening-full/state.md)
- **Plan:** [doc/03_plan/agent_tasks/gui_backend_perf.md](doc/03_plan/agent_tasks/gui_backend_perf.md)


</details>
