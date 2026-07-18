# Production GUI/Web host-GPU aggregate status contract

> Locks the aggregate evidence contract so verifiers do not treat the legacy `production_gui_web_host_gpu_queue_readback_status=pass` key as full platform readiness. The Linux GUI/web queue integration status and full host-GPU platform matrix status are separate evidence dimensions.

<!-- sdn-diagram:id=production_gui_web_host_gpu_aggregate_status_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_web_host_gpu_aggregate_status_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_web_host_gpu_aggregate_status_contract_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_web_host_gpu_aggregate_status_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI/Web host-GPU aggregate status contract

Locks the aggregate evidence contract so verifiers do not treat the legacy `production_gui_web_host_gpu_queue_readback_status=pass` key as full platform readiness. The Linux GUI/web queue integration status and full host-GPU platform matrix status are separate evidence dimensions.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/feature/host_gpu_lane.md |
| Plan | doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md |
| Design | doc/05_design/host_gpu_lane.md |
| Research | doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md |
| Source | `test/03_system/check/production_gui_web_host_gpu_aggregate_status_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Locks the aggregate evidence contract so verifiers do not treat the legacy
`production_gui_web_host_gpu_queue_readback_status=pass` key as full platform
readiness. The Linux GUI/web queue integration status and full host-GPU platform
matrix status are separate evidence dimensions.

**Plan:** doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md
**Requirements:** doc/02_requirements/feature/host_gpu_lane.md
**Research:** doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md
**Architecture:** doc/04_architecture/ui/simple_gui_stack.md
**Design:** doc/05_design/host_gpu_lane.md
**Report:** doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md

## Syntax

The aggregate may keep this compatibility key for existing consumers:

```text
production_gui_web_host_gpu_queue_readback_status=pass
```

Full platform readiness must be read from the separate matrix key:

```text
full_host_gpu_platform_matrix_status=partial
missing_device_readback_platforms=metal,rocm,directx,webgpu
```

## Examples

A Linux queue-integration pass with missing native host evidence is represented
as:

```text
linux_gui_web_queue_integration_status=pass
production_gui_web_host_gpu_queue_readback_status=pass
full_host_gpu_platform_matrix_status=partial
missing_device_readback_platforms=metal,rocm,directx,webgpu
```

A full platform pass would require:

```text
full_host_gpu_platform_matrix_status=complete
missing_device_readback_platforms=
```

## Acceptance

- The report exposes Linux queue integration status separately from full matrix
  status.
- The legacy compatibility status key remains visible but is not the platform
  completion gate.
- A partial matrix must name missing native device-readback platforms.
- Runtime queue probe evidence comes from a committed no-GC probe file rather
  than shell-generated Simple source.
- The canonical Draw IR runtime queue evidence gate runs the no-GC spec first,
  while the legacy GC bridge remains a separate compatibility gate.

## Scenarios

### Production GUI/Web host-GPU aggregate status contract

<details>
<summary>Advanced: keeps Linux queue pass separate from full platform matrix status</summary>

#### keeps Linux queue pass separate from full platform matrix status

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = rt_file_read_text("doc/09_report/production_gui_web_host_gpu_queue_readback_2026-06-16.md")
expect(report).to_contain("Date: 2026-06-16")
expect(report).to_contain("- linux GUI/web queue integration status: pass")
expect(report).to_contain("- full host-GPU platform matrix status: partial")
expect(report).to_contain("- missing device-readback platforms: metal,rocm,directx,webgpu")
```

</details>


</details>

#### keeps the aggregate script publishing distinct status keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs")
expect(script).to_contain("production_gui_web_host_gpu_queue_readback_status=\"$production_runtime_queue_integration_status\"")
expect(script).to_contain("linux_gui_web_queue_integration_status=\"$production_runtime_queue_integration_status\"")
expect(script).to_contain("full_host_gpu_platform_matrix_status=\"$platform_matrix_status\"")
expect(script).to_contain("append_env \"full_host_gpu_platform_matrix_status\" \"$full_host_gpu_platform_matrix_status\"")
expect(script).to_contain("append_env \"linux_gui_web_queue_integration_status\" \"$linux_gui_web_queue_integration_status\"")
expect(script).to_contain("append_env \"production_gui_web_host_gpu_queue_readback_status\" \"$production_gui_web_host_gpu_queue_readback_status\"")
```

</details>

#### uses a committed no-GC runtime queue probe instead of generated source

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs")
val probe = rt_file_read_text("test/01_unit/lib/nogc_async_mut/gpu/engine2d/runtime_queue_probe.spl")
expect(script).to_contain("queue_probe_source=\"test/01_unit/lib/nogc_async_mut/gpu/engine2d/runtime_queue_probe.spl\"")
expect(script.contains("write_queue_probe")).to_be(false)
expect(script.contains("cat >\"$BUILD_DIR/queue_probe.spl\"")).to_be(false)
expect(probe).to_contain("queue_zero_backend_packet_id=")
expect(probe).to_contain("queue_nonzero_backend_last_backend_handle=")
expect(probe).to_contain("queue_overflow_packet_id=")
expect(script).to_contain("SIMPLE_NO_STUB_FALLBACK=1")
expect(script).to_contain("\"$SIMPLE_BIN\" native-build")
expect(script).to_contain("queue_probe_native_runtime_path=\"${SIMPLE_RUNTIME_PATH:-$ROOT_DIR/src/compiler_rust/target/bootstrap}\"")
expect(script).to_contain("--runtime-bundle host-gpu --runtime-path \"$queue_probe_native_runtime_path\"")
expect(script).to_contain("--mode one-binary --output \"$queue_probe_native\"")
expect(script).to_contain("if [ \"$code\" = \"0\" ]")
expect(script).to_contain("cmp -s \"$BUILD_DIR/queue_probe.env\" \"$BUILD_DIR/queue_probe_native.env\"")
expect(script).to_contain("[ \"$(status_of queue_probe_native_status)\" = \"pass\" ]")
expect(script).to_contain("| runtime_queue_probe_native | ${report_queue_probe_native_status:-missing} | direct_no_stub_native_queue_dispatch |")
```

</details>

#### gates Draw IR runtime queue evidence through the no-GC owner and reports the GC bridge as compatibility only

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = rt_file_read_text("scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs")
expect(script).to_contain("test test/01_unit/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl")
expect(script).to_contain("test test/01_unit/lib/gc_async_mut/gpu/engine2d/draw_ir_runtime_queue_spec.spl")
expect(script).to_contain("append_env \"nogc_draw_ir_runtime_queue_status\" \"pass\"")
expect(script).to_contain("append_env \"gc_draw_ir_runtime_queue_status\" \"pass\"")
expect(script).to_contain("[ \"$(status_of nogc_draw_ir_runtime_queue_status)\" = \"pass\" ]")
expect(script.contains("[ \"$(status_of gc_draw_ir_runtime_queue_status)\" = \"pass\" ]")).to_be(false)
expect(script).to_contain("| gc_draw_ir_runtime_queue | ${report_gc_draw_ir_runtime_queue_status:-missing} | legacy_gc_queue_bridge |")
```

</details>

#### keeps BrowserBackend production queue and event flow imports on no-GC

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val backend = rt_file_read_text("src/app/ui.browser/backend.spl")
expect(backend).to_contain("nogc_async_mut.gpu.engine2d.draw_ir_runtime_queue")
expect(backend).to_contain("nogc_async_mut.gpu.engine2d.host_gpu_draw_ir_event_flow")
expect(backend).to_contain("engine2d_draw_ir_payload_summary")
expect(backend).to_contain("engine2d_host_gpu_draw_ir_event_flow")
expect(backend).to_contain("last_artifact_queue_dispatch_status")
expect(backend).to_contain("last_artifact_queue_backend_handle")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/feature/host_gpu_lane.md](doc/02_requirements/feature/host_gpu_lane.md)
- **Plan:** [doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md](doc/03_plan/sys_test/production_gui_web_host_gpu_queue_readback.md)
- **Design:** [doc/05_design/host_gpu_lane.md](doc/05_design/host_gpu_lane.md)
- **Research:** [doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md](doc/01_research/language/host_gpu_lane/later_gpu_host_grammar.md)


</details>
