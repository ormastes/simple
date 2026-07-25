# WM Compare Guide

`wm_compare` is the screenshot capture and comparison harness for the Window
Manager render lanes.

It does not define the WM runtime. It captures and compares artifacts produced
by other runtimes.

---

## Source Modes

The harness currently understands three source labels:

| Source | Meaning |
|--------|---------|
| `A` | Electron reference capture |
| `B` | Live host Simple Web WM capture |
| `D` | QEMU Simple OS capture via QMP screendump |

Current source-B behavior is important:

- source B is a live capture of the running localhost Web WM page
- it is not an in-process placeholder renderer anymore
- the `scene` name controls output naming and report grouping, but does not
  change the served HTML fixture by itself

---

## Main Modes

`src/app/wm_compare/main.spl` currently supports these higher-level modes:

| Mode | Purpose |
|------|---------|
| default capture flow | capture one or more sources by label |
| `live_b` | capture and persist live source-B output |
| `bit-compare` | compare two explicit PPM inputs |
| `live_bd_compare` | capture live B and compare against D |

---

## Typical Commands

### Capture real SimpleOS QEMU and host GTK WM parity evidence

Use this wrapper when the task asks for a real GUI/WM lane instead of a fake
QMP capture. It runs from the repository root, launches the SimpleOS desktop
under QEMU when `QEMU_AUTO_LAUNCH_SIMPLEOS_DESKTOP=1`, captures the framebuffer
through QMP `screendump`, and also runs the host GTK/GL exact-scene baseline:

```bash
QEMU_AUTO_LAUNCH_SIMPLEOS_DESKTOP=1 \
  BUILD_DIR=build/qemu_gtk_wm_capture_evidence \
  REPORT_PATH=doc/09_report/qemu_gtk_wm_capture_evidence_$(date -u +%F).md \
  timeout 180 sh scripts/check/check-qemu-gtk-wm-capture-evidence.shs
```

The wrapper chains the host scene baseline through:

```bash
sh scripts/check/check-gtk-gl-wm-scene-bitmap-evidence.shs
```

Current live QMP evidence:
`doc/09_report/qemu_gtk_wm_capture_evidence_2026-06-05.md` and
`doc/09_report/rv64_display_smoke_qmp_evidence_current_2026-07-02.md`.

The fake-QMP screendump contract is harness-only fallback evidence. Use it only
to validate the command/JSON/PPM parsing path without booting QEMU:

```bash
REPORT_DATE=2026-07-02 \
  BUILD_DIR=build/qemu_capture_fake_qmp_evidence-current \
  REPORT_PATH=doc/09_report/qemu_capture_fake_qmp_evidence_current_2026-07-02.md \
  sh scripts/check/check-qemu-capture-fake-qmp-evidence.shs
```

Current fake-QMP harness evidence:
`doc/09_report/qemu_capture_fake_qmp_evidence_current_2026-07-02.md`.

Current passing evidence requires:

- `auto QMP status: pass`
- `qemu live bitmap status: pass`
- `qemu live bitmap reason: live-qmp-screendump-pass`
- `live capture full-scene mismatches: 0`
- RV64 evidence contract `2`, one positive correlated present revision, and at
  least four canonical desktop palette witnesses
- `host GTK GL WM scene status: pass`
- `host GTK GL WM scene mismatch count: 0`
- `host GTK GL WM scene blur/tolerance used: false`

The host GTK baseline does not by itself promote guest-side performance. A
release-grade pass requires both a host GTK baseline and a QEMU guest Simple
paint marker shaped like:

```text
[desktop-e2e] qemu-perf sample_origin=qemu-guest simple_frame_cycles=<positive> iterations=<positive> timing_unit=tsc
```

### Capture live source B

```bash
src/compiler_rust/target/bootstrap/simple run src/app/wm_compare/main.spl -- \
  --source=B \
  --scene=four_windows \
  --mode=live_b
```

### Compare two explicit captures

```bash
src/compiler_rust/target/bootstrap/simple run src/app/wm_compare/main.spl -- \
  --mode=bit-compare \
  --source-a=test/09_baselines/wm_compare/four_windows/B_live.ppm \
  --source-b=test/09_baselines/wm_compare/engine2d_in_qemu/D.ppm \
  --out-dir=test/09_baselines/wm_compare/phase5
```

---

## Current Truth About Parity

The harness works, but not every comparison is meaningful.

Important current limitation:

- B and D are not yet a true parity pair for the same runtime scene
- B is the live obsidian-themed Web WM
- D is still tied to a different guest capture path

So a B-vs-D mismatch is often reporting a real structural difference, not a
harness bug.

Use `wm_compare` today for:

- live capture persistence
- source drift detection
- artifact generation
- bounded comparison reports

Do not over-interpret B-vs-D as proof of WM equivalence unless both sides are
known to render the same scene through comparable pipelines.

For the SimpleOS desktop/GTK lane, prefer
`scripts/check/check-qemu-gtk-wm-capture-evidence.shs` over ad hoc `wm_compare`
captures. That wrapper now owns the canonical real-QEMU QMP screendump plus
host GTK/GL exact-scene evidence and writes the release-auditable report under
`doc/09_report/`.
When that wrapper already has a live QMP socket, it calls
`check-wm-launch-capture-evidence.shs` with
`RUN_WM_CONTRACT_AND_SPECS=0` so the live screendump probe is not delayed by
unrelated host WM contract/spec checks.

For the QEMU RV64 Vulkan/RenderDoc lane, start from
`src/os/simpleos_config_matrix.spl`. The `qemu-riscv64-desktop` profile defines
the service/GPU launch contract. `simpleos_qemu_service_required_evidence_keys()`
defines the live QEMU rows that must pass before WM comparison can be treated
as guest evidence: serial console, SSH banner/probe, HTTP status/probe, QEMU
GPU readback, and QEMU WM marker.

`simpleos_wm_renderdoc_required_evidence_keys()` then defines the minimum
structured rows for a QEMU SimpleOS WM versus host WM comparison:

- SimpleOS `.rdc` magic must be `RDOC`;
- Simple runtime backend must be Vulkan with `vulkan-engine2d`;
- Simple2D and QEMU GPU readback must pass;
- QEMU WM and host WM evidence must both pass;
- the structured QEMU-vs-host WM comparison must pass.

`simpleos_renderdoc_artifact_required_evidence_keys()` is the artifact-level
RenderDoc gate below that comparison. The capture mode must be
`capture-simple`, the SimpleOS `.rdc` path must be present, magic must be
`RDOC`, payload size must be larger than the header, the capture log must pass,
runtime backend must be Vulkan with `vulkan-engine2d`, the helper must pass,
and both QEMU and host WM RenderDoc log paths must be present.
Windows evidence wrappers emit both `simpleos_renderdoc_rdc_magic_status` and
the compatibility row `simpleos_renderdoc_rdc_status`; both represent the same
RDOC-magic readiness check and must remain fail-closed when the file is missing
or malformed. For aggregate raw-row ingestion, `simpleos_renderdoc_rdc_magic=RDOC`
without `simpleos_renderdoc_rdc_magic_status=pass` remains blocked.
On Windows, `scripts\check\check-simpleos-rdoc-raw-row-gate.ps1` is the focused
contract smoke for that behavior. It writes isolated synthetic aggregate
evidence under `build/simpleos_multiconfig_live_evidence/rdoc-raw-row-gate/`
and confirms that raw `RDOC` alone blocks while raw `RDOC` plus
`simpleos_renderdoc_rdc_magic_status=pass` passes. This is not live RenderDoc
evidence.

`simpleos_wm_structured_compare_required_evidence_keys()` is the detailed
state contract for that last row. A wrapper must report matching QEMU/host
scene names, window counts, focus IDs, titlebar status, taskbar status,
RenderDoc log comparison status, ARGB diff status, and ARGB mismatch count.
The pass condition is fail-closed: mismatched scenes, missing RenderDoc log
comparison, missing ARGB diff, or nonzero ARGB mismatches are blocked results.

`simpleos_multiconfig_live_required_evidence_keys()` is the aggregate completion
gate. It must remain blocked until QEMU service evidence, FPGA serial evidence,
Engine2D Vulkan evidence, RenderDoc artifact evidence, structured WM comparison,
and WM RenderDoc evidence all report `pass`.
`scripts/check/check_simpleos_multiconfig_live_evidence.spl` is the matching
operator-facing status emitter. A no-artifact run should report
`simpleos_multiconfig_live_status=blocked:qemu-service:blocked:missing-qemu-serial-console`;
that blocked result is expected until QEMU/FPGA/Vulkan/RenderDoc/WM wrappers
publish real evidence rows.
The WM comparison wrapper should contribute
`simpleos_wm_structured_compare_evidence_status` and
`simpleos_wm_renderdoc_evidence_status` to the aggregate `key=value` evidence
file consumed by `--evidence <path>`.
It may also write the raw structured rows directly: scene names, window counts,
focus IDs, titlebar/taskbar statuses, RenderDoc log compare status, ARGB diff
status, and `simpleos_wm_argb_mismatch_count`. The aggregate checker derives
the WM status rows and keeps mismatches blocked.

On Windows, use the focused host/QEMU WM evidence wrapper after the QEMU
desktop wrapper has produced its raw rows:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\check\check-simpleos-wm-host-compare-evidence.ps1 -BaseEvidencePath build/simpleos_multiconfig_live_evidence/qemu-rv64-desktop.env
```

It writes `build/simpleos_multiconfig_live_evidence/wm-host-compare.env`,
preserving base QEMU rows while overriding the WM/readback rows it owns. The
default inputs are:

- QEMU QMP screendump: `build/os/systest/qemu-riscv64-desktop/qemu-screendump.ppm`;
- host WM capture: `build/os/systest/qemu-riscv64-desktop/host-wm.ppm`;
- QEMU RenderDoc/log: `build/os/systest/qemu-riscv64-desktop/qemu-wm-renderdoc.log`;
- host RenderDoc/log: `build/os/systest/qemu-riscv64-desktop/host-wm-renderdoc.log`;
- SimpleOS RenderDoc capture: `build/os/systest/qemu-riscv64-desktop/simpleos-wm.rdc`.

Add `-AttemptHostWmCapture` when the operator wants the wrapper to invoke
`src/os/compositor/hosted_wm_capture_evidence.spl` before validating
`host-wm.ppm`. The wrapper records `simpleos_host_wm_capture_attempted`,
`simpleos_host_wm_capture_mode`, `simpleos_host_wm_capture_status`,
`simpleos_host_wm_capture_exit_code`, and `simpleos_host_wm_capture_log_path`.
Use `-HostCaptureTimeoutSeconds <n>` to bound that child process. These rows
diagnose the host capture path only; a timeout, crash, fallback, missing PPM,
or mismatched capture remains blocked. On the current Windows debug runtime the
hosted file-output path is avoided: the entrypoint emits a marker-delimited
compact rectangle scene on stdout, the wrapper materializes that scene as a P6
`host-wm.ppm`, and
`simpleos_host_wm_capture_mode=hosted-wm-capture-stdout-ppm` records that path.

The wrapper validates QEMU and host captures as nonblank PPM files. QEMU QMP
captures are normally P6; the hosted stdout path may emit either legacy P3 or
the compact rectangle scene, which the wrapper normalizes/materializes to RGB
bytes before comparison. It compares normalized bytes exactly, emits
`simpleos_wm_argb_mismatch_count`, records
RenderDoc `.rdc` magic/size and log paths, and remains fail-closed while any
capture or log is absent. The stdout path can prove a host renderer artifact
exists and can now match the QEMU WM rectangle scene with zero ARGB mismatches,
but it is still not a completion claim unless RenderDoc log comparison also
passes. The WM scene and RenderDoc scene are separate:
`-WmSceneName` defaults to `simpleos-desktop-four-windows`, while
`-RenderdocSceneName` defaults to `vulkan-engine2d`. Do not use the Engine2D
scene name as the WM scene identity.

The wrapper also reports artifact classification rows:
`simpleos_wm_qemu_ppm_width`, `simpleos_wm_qemu_ppm_height`,
`simpleos_wm_qemu_capture_kind`, `simpleos_wm_host_ppm_width`,
`simpleos_wm_host_ppm_height`, `simpleos_wm_host_capture_kind`, and
`simpleos_wm_argb_diff_status`, `simpleos_wm_argb_diff_reason`, and
`simpleos_wm_argb_mismatch_count`. The aggregate checker echoes those ARGB rows
too, so operators can see exact bitmap parity even while the full WM gate is
blocked on missing RenderDoc logs. The current passing bitmap state classifies
the QEMU screendump as `qemu-wm-rect-scene`, the host artifact as
`hosted-wm-rect-scene`, and reports `simpleos_wm_argb_diff_status=pass` with
`simpleos_wm_argb_mismatch_count=0`. Older or stale QEMU captures may classify
as `qemu-virtio-gpu-test-pattern`; that is valid virtio-gpu readback evidence,
but it is not a WM scene and must leave QEMU scene/titlebar/taskbar rows
missing. A stale host crop may classify as `hosted-wm-diagnostic-crop`; that is
host capture diagnostics only, not full-scene parity evidence.

RenderDoc log comparison is structured, not a nonempty-file check. When QEMU
and host log files exist, the wrapper reads fields such as
`simpleos_wm_compare_scene`, `simpleos_renderdoc_simple_runtime_backend`,
`simpleos_renderdoc_capture_mode`, and `simpleos_renderdoc_rdc_magic` from both
logs. `simpleos_wm_renderdoc_log_compare_status=pass` requires matching WM
scene names, Vulkan backend on both sides, `capture-simple` mode on both sides,
and `RDOC` magic on both sides. The wrapper emits
`simpleos_wm_renderdoc_log_compare_reason`,
`simpleos_wm_renderdoc_log_compare_mode`,
`simpleos_wm_renderdoc_qemu_log_status`,
`simpleos_wm_renderdoc_host_log_status`,
`simpleos_wm_renderdoc_qemu_log_scene`,
`simpleos_wm_renderdoc_host_log_scene`,
`simpleos_wm_renderdoc_qemu_log_backend`, and
`simpleos_wm_renderdoc_host_log_backend` so malformed or mismatched logs remain
blocked instead of silently passing.

Feed the merged file to the aggregate checker:

```powershell
$env:SIMPLE_LIB='src'
src\compiler_rust\target\debug\simple.exe scripts/check/check_simpleos_multiconfig_live_evidence.spl --evidence build/simpleos_multiconfig_live_evidence/wm-host-compare.env --mode=interpreter
```

Static bitmap parity or a host-only RenderDoc capture is not enough for this
lane.

---

## Artifacts

Artifacts are written under:

```text
test/09_baselines/wm_compare/<scene>/
```

Typical files:

- baseline PPMs such as `A.ppm`, `B_live.ppm`, `D.ppm`
- diff outputs such as `diff_A_vs_B.ppm`
- `report.sdn`

## Publishing To SSPEC

When a WM comparison backs a TUI/GUI SSPEC, copy or emit the reviewable image
evidence under `doc/06_spec/image/<spec-relative-path>/` and list it in the
spec docblock with `**Screenshots:**` or `**TUI Captures:**`. Keep structured
reports and logs under `build/test-artifacts/<spec-relative-path>/`.

For phase-by-phase history and current blockers, see
[doc/08_tracking/wm_compare/README.md](../../08_tracking/wm_compare/README.md).

---

## Operational Advice

- Treat source B as the current host/browser truth.
- Refresh baselines when the Web WM fixture or theme intentionally changes.
- Keep phase reports honest: note when a comparison is structural rather than a
  regression signal.
- If a run depends on the live Web WM, verify the browser runtime first with
  [platform/simpleos_web_wm.md](../platform/simpleos_web_wm.md).
