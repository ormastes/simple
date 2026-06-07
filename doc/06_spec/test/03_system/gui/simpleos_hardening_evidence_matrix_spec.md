# SimpleOS Hardening Evidence Matrix Spec

> This scenario audits the current SimpleOS hardening goal as a requirement matrix. It does not replace the deeper live gates; it verifies that the current workspace has authoritative evidence for every explicit clause in the user request.

<!-- sdn-diagram:id=simpleos_hardening_evidence_matrix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_hardening_evidence_matrix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_hardening_evidence_matrix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_hardening_evidence_matrix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS Hardening Evidence Matrix Spec

This scenario audits the current SimpleOS hardening goal as a requirement matrix. It does not replace the deeper live gates; it verifies that the current workspace has authoritative evidence for every explicit clause in the user request.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | .spipe/gui_hardening_current_plan/state.md |
| Plan | .spipe/gui_hardening_current_plan/state.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This scenario audits the current SimpleOS hardening goal as a requirement
matrix. It does not replace the deeper live gates; it verifies that the current
workspace has authoritative evidence for every explicit clause in the user
request.

The matrix checks SSH transcript evidence, shared WM lifecycle evidence, CPU
SIMD Engine2D diagram evidence, layered WebRenderer/Engine2D bitmap evidence,
Simple GUI through WebRenderer bitmap evidence, host/QEMU WM counterpart
bitmap evidence, and the latest live QEMU Simple GUI/MDI framebuffer artifact.

## Acceptance Criteria

- Executable launch from the SimpleOS filesystem is proven by the SSH transcript
  for `/usr/bin/simple`.
- SSH server and shell launch both `/usr/bin/simple.smf` and `/usr/bin/simple`.
- Hosted WM source and SimpleOS WM lifecycle behavior are covered by the shared
  WM renderer unification evidence report.
- CPU SIMD Engine2D diagram rendering has exact-bitmap mismatch count zero and
  no blur/tolerance policy.
- WebRenderer backed by Engine2D passes exact bitmap checks against Node and Bun
  counterparts, including the explicit `simple-web-engine2d-image-taskbar-command`
  sample page.
- Simple GUI backed by Simple WebRenderer passes exact Electron bitmap checks.
- Production GUI/WebRenderer parity passes the generated GUI matrix, Electron
  layout manifest, live Tauri/WebKitGTK and Chrome/Chromium surface manifest,
  and pure Simple Engine2D backend parity with zero mismatches and no
  blur/tolerance.
- QEMU WM capture and the host GTK GL scene counterpart both pass with zero
  mismatches and no blur/tolerance. Host GTK timing baselines are
  non-promoting, and guest-side Simple-vs-GTK performance is satisfied only by
  QEMU guest serial timing markers. If the guest-side performance gate is still
  blocked, the aggregate matrix is blocked and exits nonzero even when all
  artifact rows preserve their evidence fields.
- The live QEMU Simple GUI/MDI artifact has the expected 1024x768 PPM and raw
  pmemsave byte sizes, while the executable spec/manual require the canonical
  MDI serial markers and framebuffer anchor checks.
- The latest live QEMU Simple GUI/MDI PPM is parsed directly and must satisfy
  the same probe, header, body, top-lane, and taskbar pixel anchors as the live
  QMP capture spec.

## Examples

Run the matrix directly:

```bash
BUILD_DIR=build/simpleos_hardening_evidence_matrix_current \
REPORT_PATH=doc/09_report/simpleos_hardening_evidence_matrix_2026-06-05.md \
sh scripts/check/check-simpleos-hardening-evidence-matrix.shs
```

Run the SPipe gate:

```bash
SIMPLE_LIB=src src/compiler_rust/target/release/simple test \
  test/03_system/gui/simpleos_hardening_evidence_matrix_spec.spl \
  --mode=interpreter --clean --format json
```

## Failure Diagnostics

- A single failed row means the corresponding requirement lacks current
  evidence and should be rerun or repaired at its source gate.
- If `qemu_wm_simple_gui_mdi` fails only on artifact byte counts, rerun
  `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl`.
- If layered GUI rows fail, rerun
  `test/03_system/gui/layered_simple_gui_web_engine2d_bitmap_evidence_spec.spl`.
- If SSH rows fail, rerun `test/03_system/ssh_live_login_in_qemu_spec.spl`.

## Matrix Rows

The wrapper emits these rows:

- `simpleos_hardening_exec_launch_fs_status`
- `simpleos_hardening_ssh_smf_exec_status`
- `simpleos_hardening_shared_wm_status`
- `simpleos_hardening_cpu_simd_status`
- `simpleos_hardening_web_renderer_engine2d_status`
- `simpleos_hardening_simple_gui_webrenderer_status`
- `simpleos_hardening_qemu_host_counterpart_status`
- `simpleos_hardening_qemu_gui_smf_artifact_status`
- `simpleos_hardening_qemu_mdi_status`

The matrix passes only when all nine rows are `pass` and the required
guest-side QEMU performance release gate is `pass`.

## Evidence Sources

- SSH rows read `build/os/x64-ssh-live.session-smf.txt` and
  `build/os/x64-ssh-live.session-exec.txt`.
- Shared WM reads
  `doc/09_report/shared_wm_renderer_unification_evidence_2026-06-04.md`.
- CPU SIMD reads `doc/09_report/cpu_simd_engine2d_evidence_2026-06-03.md`.
- Layered WebRenderer and Simple GUI rows read
  `doc/09_report/layered_simple_gui_web_engine2d_bitmap_evidence_2026-06-05.md`.
- The explicit sample-page WebRenderer row also reads
  `doc/09_report/simple_web_engine2d_js_bitmap_evidence_2026-06-02.md` and
  `doc/09_report/bun_simple_web_engine2d_js_bitmap_evidence_2026-06-02.md`.
- Host/QEMU counterpart evidence reads
  `doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-05.md`.
- Production GUI/WebRenderer parity evidence reads
  `doc/09_report/production_gui_web_renderer_parity_evidence_2026-06-05.md`.
- QEMU MDI evidence reads the latest
  `build/tmp/gui_entry_engine2d_wm_simple_web_spec_*` capture directory plus
  `test/03_system/gui/gui_entry_engine2d_wm_simple_web_spec.spl` and its generated
  manual.

## Scope Notes

- This matrix is an audit gate, not a replacement for live QEMU or bitmap
  evidence generation.
- It intentionally requires exact bitmap/no blur/no tolerance report fields
  from the source gates.
- It intentionally distinguishes the explicit Simple Web sample-page evidence
  from the broader layered GUI scenes, because the hardening request names both
  a sample page and the full GUI/WebRenderer stack.
- It intentionally requires the latest MDI capture PPM and raw pmemsave byte
  sizes, because those prove a real 1024x768 framebuffer artifact exists.
- It samples the latest MDI PPM directly so a size-only artifact cannot satisfy
  the live QEMU row.
- The GUI SMF artifact contract is a counted matrix row. It cannot promote live
  QEMU capture or guest-side performance evidence, but a missing or failing
  SMF artifact contract keeps the matrix incomplete.
- QEMU guest perf can report `pass` only when the QEMU evidence report contains
  a harness pass, `sample_origin=qemu-guest`, and a serial marker line with
  `simple_frame_cycles` and `iterations` fields. The GTK timing is a host-side
  baseline field in the same report; it is not claimed as guest GTK evidence.
- If a report is stale or missing, the right fix is to rerun the source gate and
  refresh the report.
- If the matrix passes after a source gate was weakened, the source gate should
  be tightened; the matrix is only as strong as the row evidence it checks.
- Host GTK timing baselines are diagnostic by themselves and must never promote
  the `guest-simple-frame-plus-host-gtk-baseline` release gate without a real
  QEMU guest Simple frame marker.
- Production GUI/WebRenderer parity requires live Tauri and Chrome captures;
  `unavailable` browser-shell rows do not satisfy the Simple GUI/WebRenderer
  matrix row.
- Before release, run this matrix together with the individual source gates that
  changed in the current branch.

**Requirements:** .spipe/gui_hardening_current_plan/state.md
**Plan:** .spipe/gui_hardening_current_plan/state.md
**Design:** N/A
**Research:** N/A

## Scenarios

### SimpleOS hardening evidence matrix

#### passes when evidence rows and guest performance are wired

<details>
<summary>Executable SPipe</summary>

Runnable source: 36 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_matrix(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
expect(code).to_equal(0)
expect(stdout).to_contain("simpleos_hardening_matrix_status=pass")
expect(stdout).to_contain("simpleos_hardening_matrix_reason=pass")
expect(stdout).to_contain("simpleos_hardening_matrix_passed=9/9")
expect(stdout).to_contain("simpleos_hardening_exec_launch_fs_status=pass")
expect(stdout).to_contain("simpleos_hardening_ssh_smf_exec_status=pass")
expect(stdout).to_contain("simpleos_hardening_shared_wm_status=pass")
expect(stdout).to_contain("simpleos_hardening_cpu_simd_status=pass")
expect(stdout).to_contain("simpleos_hardening_web_renderer_engine2d_status=pass")
expect(stdout).to_contain("simpleos_hardening_simple_gui_webrenderer_status=pass")
expect(stdout).to_contain("simpleos_hardening_production_gui_web_renderer_parity_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_host_counterpart_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
expect(stdout).to_contain(" qemu_status=pass")
expect(stdout).to_contain(" macos_status=not-run")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate=guest-simple-frame-plus-host-gtk-baseline")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_blocker=none")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_reason=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_sample_origin=qemu-guest")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_required_sample_origin=qemu-guest")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_marker_line=[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=")
expect(stdout).to_contain("simpleos_hardening_qemu_host_perf_promotes_qemu_perf=false")
expect(stdout).to_contain("simpleos_hardening_qemu_mdi_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_mdi_ppm_anchor_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_mdi_ppm_nonblack=")
expect(stdout).to_contain("simpleos_hardening_gui_entry_capture_ppm_bytes=2359312")
expect(stdout).to_contain("simpleos_hardening_gui_entry_capture_raw_bytes=3145728")
```

</details>

#### fails closed when live QMP passes but GUI SMF artifact contract is not executed

1. rt process run timeout

2. )) to equal
   - Expected: code equals `1`


<details>
<summary>Executable SPipe</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val qemu_report = _qemu_report_path(run_id)
rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p " + _build_dir(run_id)], 5000)
expect(rt_file_write_text(qemu_report,
    "# QEMU GTK WM Capture Evidence\n\n" +
    "- status: pass\n" +
    "- auto QMP status: pass\n" +
    "- qemu live bitmap status: pass\n" +
    "- live capture sample mismatches: 0\n" +
    "- live capture full-scene mismatches: 0\n" +
    "- qemu-side perf status: unavailable\n" +
    "- qemu-side perf release gate: guest-simple-frame-plus-host-gtk-baseline\n" +
    "- qemu-side perf required for release: true\n" +
    "- qemu-side perf release blocker: qemu-side-simple-perf-harness-not-wired\n" +
    "- qemu-side perf harness status: unwired\n" +
    "- qemu-side perf harness reason: qemu-side-simple-perf-harness-not-wired\n" +
    "- qemu-side perf harness sample origin: none\n" +
    "- qemu-side perf harness required sample origin: qemu-guest\n" +
    "- qemu-side perf harness marker line:\n" +
    "- host GTK GL WM scene mismatch count: 0\n" +
    "- host GTK GL WM scene blur/tolerance used: false\n" +
    "- host perf baseline status: pass\n" +
    "- host perf baseline comparison available: true\n" +
    "- host perf baseline promotes QEMU perf: false\n" +
    "- GUI SMF artifact contract status: fail\n" +
    "- GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=fail artifact=build/gui/pure_gui_hot.smf sha256=abc size=1 smf_role=2 arch=1 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick qemu_status=not-run qemu_reason=live-qemu-not-executed macos_status=not-run macos_reason=requires-macos-arm64\n"
)).to_equal(true)
val result = _run_matrix_with_qemu_report(run_id, qemu_report)
val stdout = result[0]
val code = result[2]
expect(code).to_equal(1)
expect(stdout).to_contain("simpleos_hardening_matrix_status=fail")
expect(stdout).to_contain("simpleos_hardening_matrix_reason=matrix-incomplete")
expect(stdout).to_contain("simpleos_hardening_matrix_passed=8/9")
expect(stdout).to_contain("simpleos_hardening_qemu_host_counterpart_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_status=fail")
expect(stdout).to_contain("simpleos_hardening_production_gui_web_renderer_parity_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_status=fail")
expect(stdout).to_contain("qemu_status=not-run")
expect(stdout).to_contain("macos_status=not-run")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate_status=blocked-unwired")
```

</details>

#### passes the combined GUI SMF artifact row only when QEMU macOS and guest perf evidence all pass

1. rt process run timeout

2. )) to equal
   - Expected: code equals `0`


<details>
<summary>Executable SPipe</summary>

Runnable source: 50 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val qemu_report = _qemu_report_path(run_id)
rt_process_run_timeout("/bin/sh", ["-c", "mkdir -p " + _build_dir(run_id)], 5000)
expect(rt_file_write_text(qemu_report,
    "# QEMU GTK WM Capture Evidence\n\n" +
    "- status: pass\n" +
    "- auto QMP status: pass\n" +
    "- qemu live bitmap status: pass\n" +
    "- live capture sample mismatches: 0\n" +
    "- live capture full-scene mismatches: 0\n" +
    "- qemu-side perf status: pass\n" +
    "- qemu-side perf release gate: guest-simple-frame-plus-host-gtk-baseline\n" +
    "- qemu-side perf required for release: true\n" +
    "- qemu-side perf release blocker: none\n" +
    "- qemu-side perf harness status: pass\n" +
    "- qemu-side perf harness reason: pass\n" +
    "- qemu-side perf harness sample origin: qemu-guest\n" +
    "- qemu-side perf harness required sample origin: qemu-guest\n" +
    "- qemu-side perf simple frame cycles: 1000\n" +
    "- qemu-side perf host GTK frame us: 200\n" +
    "- qemu-side perf iterations: 30\n" +
    "- qemu-side perf timing unit: tsc\n" +
    "- qemu-side perf harness marker line: [desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=1000 iterations=30 timing_unit=tsc\n" +
    "- host GTK GL WM scene mismatch count: 0\n" +
    "- host GTK GL WM scene blur/tolerance used: false\n" +
    "- host perf baseline status: pass\n" +
    "- host perf baseline comparison available: true\n" +
    "- host perf baseline promotes QEMU perf: false\n" +
    "- GUI SMF artifact contract status: pass\n" +
    "- GUI SMF artifact contract row: GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf sha256=abc size=1 smf_role=2 arch=3 embedded_dynlib=true symbol=gui_dynlib_hot_probe_tick qemu_status=pass qemu_reason=live-qemu-artifact-verified macos_status=pass macos_reason=live-macos-window-artifact-verified\n"
)).to_equal(true)
val result = _run_matrix_with_qemu_report(run_id, qemu_report)
val stdout = result[0]
val code = result[2]
expect(code).to_equal(0)
expect(stdout).to_contain("simpleos_hardening_matrix_status=pass")
expect(stdout).to_contain("simpleos_hardening_matrix_reason=pass")
expect(stdout).to_contain("simpleos_hardening_matrix_passed=9/9")
expect(stdout).to_contain("simpleos_hardening_qemu_host_counterpart_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_status=pass")
expect(stdout).to_contain("simpleos_hardening_production_gui_web_renderer_parity_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_gui_smf_artifact_contract_row=GUI_SMF_ARTIFACT_CONTRACT status=pass artifact=build/gui/pure_gui_hot.smf")
expect(stdout).to_contain(" qemu_status=pass")
expect(stdout).to_contain(" macos_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_gate_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_release_blocker=none")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_status=pass")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_sample_origin=qemu-guest")
expect(stdout).to_contain("simpleos_hardening_qemu_guest_perf_harness_marker_line=[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=1000 iterations=30 timing_unit=tsc")
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

- **Requirements:** [.spipe/gui_hardening_current_plan/state.md](.spipe/gui_hardening_current_plan/state.md)
- **Plan:** [.spipe/gui_hardening_current_plan/state.md](.spipe/gui_hardening_current_plan/state.md)


</details>
