# Tauri/Chrome Surface Manifest Gate Spec

> This scenario verifies that the production surface-manifest wrapper fails closed when live browser-shell capture evidence is unavailable. The renderer parity lane requires real Electron, Tauri/WebKitGTK, and Chrome/Chromium captures; an unavailable Tauri or Chrome row must not promote the aggregate manifest to pass.

<!-- sdn-diagram:id=tauri_chrome_surface_manifest_gate_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=tauri_chrome_surface_manifest_gate_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

tauri_chrome_surface_manifest_gate_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=tauri_chrome_surface_manifest_gate_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tauri/Chrome Surface Manifest Gate Spec

This scenario verifies that the production surface-manifest wrapper fails closed when live browser-shell capture evidence is unavailable. The renderer parity lane requires real Electron, Tauri/WebKitGTK, and Chrome/Chromium captures; an unavailable Tauri or Chrome row must not promote the aggregate manifest to pass.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md |
| Plan | doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md |
| Design | doc/07_guide/app/ui/ui_render.md |
| Research | N/A |
| Source | `test/03_system/gui/tauri_chrome_surface_manifest_gate_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario verifies that the production surface-manifest wrapper fails
closed when live browser-shell capture evidence is unavailable. The renderer
parity lane requires real Electron, Tauri/WebKitGTK, and Chrome/Chromium
captures; an unavailable Tauri or Chrome row must not promote the aggregate
manifest to pass.

## Acceptance Criteria

- The Tauri/Chrome manifest wrapper exits nonzero when a manifest row cannot
  produce live capture proof.
- The wrapper emits `tauri_chrome_simple_web_layout_manifest_status=fail`.
- The wrapper still records per-lane live-capture status fields so the missing
  shell proof is visible in the evidence report.

## Examples

```bash
SIMPLE_LIB=src src/compiler_rust/target/release/simple test \
  test/03_system/gui/tauri_chrome_surface_manifest_gate_spec.spl \
  --mode=interpreter --clean --format json
```

**Requirements:** doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md
**Plan:** doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md
**Design:** doc/07_guide/app/ui/ui_render.md
**Research:** N/A

## Scenarios

### Tauri/Chrome surface manifest gate

#### fails closed when live shell captures are unavailable

1. rt process run timeout

2. "case missing shell capture electron simple web layout html path=" +  build dir

3. "case missing shell capture electron simple web layout expected argb path=" +  build dir

4. )) to equal
   - Expected: code equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val layout_env = _layout_env_path(run_id)
rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p " + _build_dir(run_id)], 5000)
expect(rt_file_write_text(layout_env,
    "electron_simple_web_layout_manifest_status=pass\n" +
    "electron_simple_web_layout_manifest_reason=pass\n" +
    "electron_simple_web_layout_manifest_case=missing_shell_capture\n" +
    "electron_simple_web_layout_manifest_case_count=1\n" +
    "electron_simple_web_layout_manifest_pass_count=1\n" +
    "electron_simple_web_layout_manifest_fail_count=0\n" +
    "case_missing_shell_capture_electron_simple_web_layout_html_path=" + _build_dir(run_id) + "/missing.html\n" +
    "case_missing_shell_capture_electron_simple_web_layout_expected_argb_path=" + _build_dir(run_id) + "/missing-argb.json\n" +
    "case_missing_shell_capture_electron_simple_web_layout_width=96\n" +
    "case_missing_shell_capture_electron_simple_web_layout_height=64\n"
)).to_equal(true)
val result = _run_manifest(run_id)
val stdout = result[0]
val code = result[2]
expect(code).to_equal(1)
expect(stdout).to_contain("tauri_chrome_simple_web_layout_manifest_status=fail")
expect(stdout).to_contain("live-surface-capture-required")
expect(stdout).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_capture_status=unavailable")
expect(stdout).to_contain("tauri_chrome_simple_web_layout_manifest_tauri_live_capture=false")
expect(stdout).to_contain("tauri_chrome_simple_web_layout_manifest_no_fake_capture=true")
expect(stdout).to_contain("tauri_chrome_simple_web_layout_manifest_blur_or_tolerance_used=false")
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

- **Requirements:** [doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md](doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md)
- **Plan:** [doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md](doc/03_plan/agent_tasks/shared_ui_gpu_backend_rollout_2026_06_04.md)
- **Design:** [doc/07_guide/app/ui/ui_render.md](doc/07_guide/app/ui/ui_render.md)


</details>
