# Production GUI/web backend readback source contract

> Validates that production GUI/web renderer parity cannot pass on Metal-backed backend evidence unless the backend row explicitly reports same-frame `device_readback`. Matching checksums, a positive command queue handle, and a completed frame are not sufficient when the readback source is a CPU mirror or other non-device shortcut.

<!-- sdn-diagram:id=production_gui_web_backend_readback_source_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_backend_readback_source_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_backend_readback_source_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_backend_readback_source_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/web backend readback source contract

Validates that production GUI/web renderer parity cannot pass on Metal-backed backend evidence unless the backend row explicitly reports same-frame `device_readback`. Matching checksums, a positive command queue handle, and a completed frame are not sufficient when the readback source is a CPU mirror or other non-device shortcut.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/production_gui_web_backend_readback_source_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates that production GUI/web renderer parity cannot pass on Metal-backed
backend evidence unless the backend row explicitly reports same-frame
`device_readback`. Matching checksums, a positive command queue handle, and a
completed frame are not sufficient when the readback source is a CPU mirror or
other non-device shortcut.

**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- Backend evidence promotes `production_gui_web_renderer_parity_backend_readback_source`.
- A Metal-backed row with `backend_readback_source=cpu_mirror` fails top-level
  production parity.
- The failure reason remains `backend-executed-parity-failed`.
- Surrounding matrix, layout, surface, font, Metal readback, timing, checksum,
  frame-complete, and command-queue fields are otherwise passing.

## Scenarios

### Production GUI/web backend readback source contract

#### rejects Metal backend rows that use CPU mirror readback

- Run production parity with a Metal backend row that reports cpu_mirror readback
   - Expected: code equals `0`
- Inspect the promoted backend source and top-level failure


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Run production parity with a Metal backend row that reports cpu_mirror readback")
val root = "build/test-production-gui-web-backend-readback-source-contract"
val command = cpu_mirror_readback_command(root)
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

step("Inspect the promoted backend source and top-level failure")
val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_status=pass")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_metal_resolved=metal")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_metal_gpu_frame_complete=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_metal_command_queue_handle=42")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_checksum_match=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_same_frame_readback=true")
expect(evidence).to_contain("production_gui_web_renderer_parity_backend_readback_source=cpu_mirror")
expect(evidence).to_contain("production_gui_web_renderer_parity_status=fail")
expect(evidence).to_contain("production_gui_web_renderer_parity_reason=backend-executed-parity-failed")
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

- **Plan:** [doc/03_plan/sys_test/simple_web_browser_production_hardening.md](doc/03_plan/sys_test/simple_web_browser_production_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
