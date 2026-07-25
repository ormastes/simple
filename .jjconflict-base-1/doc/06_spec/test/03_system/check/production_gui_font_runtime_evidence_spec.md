# Production GUI font runtime evidence

> Validates the producer that converts real vector-font compute and generated 2D readback evidence into the `PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV` contract consumed by production GUI/web font-offload evidence.

<!-- sdn-diagram:id=production_gui_font_runtime_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=production_gui_font_runtime_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

production_gui_font_runtime_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=production_gui_font_runtime_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Production GUI font runtime evidence

Validates the producer that converts real vector-font compute and generated 2D readback evidence into the `PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV` contract consumed by production GUI/web font-offload evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/simple_web_browser_production_hardening.md |
| Design | doc/07_guide/tooling/renderdoc_capture_infra.md |
| Research | N/A |
| Source | `test/03_system/check/production_gui_font_runtime_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the producer that converts real vector-font compute and generated 2D
readback evidence into the `PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV` contract
consumed by production GUI/web font-offload evidence.

**Plan:** doc/03_plan/sys_test/simple_web_browser_production_hardening.md
**Requirements:** N/A
**Research:** N/A
**Design:** doc/07_guide/tooling/renderdoc_capture_infra.md

## Acceptance

- Passing source proofs emit `production_gui_font_runtime_status=pass`.
- The runtime env pins the selected backend in
  `production_gui_font_runtime_candidates_simple`.
- The production font wrapper consumes the runtime env and can reach
  `production_gui_font_offload_status=pass`.
- Missing generated 2D readback stays unavailable and does not mark runtime,
  vector, or bitmap readiness true.

## Scenarios

### Production GUI font runtime evidence

#### promotes passing vector and generated 2D readback proofs into font offload readiness

<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-production-gui-font-runtime-pass"
val (_setup_out, _setup_err, setup_code) = process_run("/bin/sh", ["-c", write_pass_fixtures(root)])
expect(setup_code).to_equal(0)

val (_runtime_out, _runtime_err, runtime_code) = process_run("/bin/sh", ["-c", runtime_command(root)])
expect(runtime_code).to_equal(0)
val runtime_env = file_read(root + "/runtime/evidence.env")
expect(runtime_env).to_contain("production_gui_font_runtime_status=pass")
expect(runtime_env).to_contain("production_gui_font_runtime_selected_backend=cuda")
expect(runtime_env).to_contain("production_gui_font_runtime_candidates_simple=[\"cuda\", \"opencl\", \"cpu_simd\", \"software\", \"cpu\"]")
expect(runtime_env).to_contain("production_gui_font_runtime_vector_gpu_returned_glyphs=2")
expect(runtime_env).to_contain("production_gui_font_runtime_bitmap_readback_available=true")

val font_command = "BUILD_DIR=" + root + "/font REPORT_PATH=" + root + "/font/report.md PRODUCTION_GUI_FONT_RUNTIME_EVIDENCE_ENV=" + root + "/runtime/evidence.env sh scripts/check/check-production-gui-font-offload-evidence.shs"
val (_font_out, _font_err, font_code) = process_run("/bin/sh", ["-c", font_command])
expect(font_code).to_equal(0)
val font_env = file_read(root + "/font/evidence.env")
expect(font_env).to_contain("production_gui_font_offload_status=pass")
expect(font_env).to_contain("production_gui_font_offload_runtime_evidence_status=pass")
expect(font_env).to_contain("production_gui_font_offload_vector_production_ready=true")
expect(font_env).to_contain("production_gui_font_offload_bitmap_production_ready=true")
```

</details>

#### fails closed when generated 2D readback is missing

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-production-gui-font-runtime-missing-readback"
val (_setup_out, _setup_err, setup_code) = process_run("/bin/sh", ["-c", write_missing_readback_fixtures(root)])
expect(setup_code).to_equal(0)

val (_runtime_out, _runtime_err, runtime_code) = process_run("/bin/sh", ["-c", runtime_command(root) + " || true"])
expect(runtime_code).to_equal(0)
val runtime_env = file_read(root + "/runtime/evidence.env")
expect(runtime_env).to_contain("production_gui_font_runtime_status=unavailable")
expect(runtime_env).to_contain("production_gui_font_runtime_reason=generated-2d-readback-not-pass")
expect(runtime_env).to_contain("production_gui_font_runtime_vector_runtime_ready=false")
expect(runtime_env).to_contain("production_gui_font_runtime_bitmap_readback_available=false")
```

</details>

#### selects Metal when vector glyph pixels and Metal generated readback both pass

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-production-gui-font-runtime-metal-pass"
val (_setup_out, _setup_err, setup_code) = process_run("/bin/sh", ["-c", write_metal_pass_fixtures(root)])
expect(setup_code).to_equal(0)

val (_runtime_out, _runtime_err, runtime_code) = process_run("/bin/sh", ["-c", runtime_command(root)])
expect(runtime_code).to_equal(0)
val runtime_env = file_read(root + "/runtime/evidence.env")
expect(runtime_env).to_contain("production_gui_font_runtime_status=pass")
expect(runtime_env).to_contain("production_gui_font_runtime_selected_backend=metal")
expect(runtime_env).to_contain("production_gui_font_runtime_candidates_simple=[\"metal\", \"cuda\", \"opencl\", \"cpu_simd\", \"software\", \"cpu\"]")
expect(runtime_env).to_contain("production_gui_font_runtime_metal_status=pass")
expect(runtime_env).to_contain("production_gui_font_runtime_metal_readback_available=true")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/simple_web_browser_production_hardening.md](doc/03_plan/sys_test/simple_web_browser_production_hardening.md)
- **Design:** [doc/07_guide/tooling/renderdoc_capture_infra.md](doc/07_guide/tooling/renderdoc_capture_infra.md)


</details>
