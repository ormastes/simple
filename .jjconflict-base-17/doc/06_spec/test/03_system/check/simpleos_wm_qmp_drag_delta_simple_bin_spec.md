# SimpleOS WM QMP Drag Delta Simple Binary Contract

> The live drag-delta check requires QEMU and a running SimpleOS desktop target, but its binary-selection contract can be verified without launching either. Rust seed overrides must fail before launch artifacts are produced.

<!-- sdn-diagram:id=simpleos_wm_qmp_drag_delta_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simpleos_wm_qmp_drag_delta_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simpleos_wm_qmp_drag_delta_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simpleos_wm_qmp_drag_delta_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS WM QMP Drag Delta Simple Binary Contract

The live drag-delta check requires QEMU and a running SimpleOS desktop target, but its binary-selection contract can be verified without launching either. Rust seed overrides must fail before launch artifacts are produced.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The live drag-delta check requires QEMU and a running SimpleOS desktop target,
but its binary-selection contract can be verified without launching either.
Rust seed overrides must fail before launch artifacts are produced.

## Requirements

**Requirements:** N/A

- REQ-SIMPLEOS-QMP-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-SIMPLEOS-QMP-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before SimpleOS/QMP launch.
- REQ-SIMPLEOS-QMP-BIN-003: Evidence output records selected Simple binary,
  source, and status fields.

## Plan

**Plan:** doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout and report show `simple-bin-forbidden`.
5. Confirm QMP launch and drag artifacts are not created.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before launching the SimpleOS desktop QMP
target so invalid Rust seed overrides cannot masquerade as GUI/QMP evidence.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/simpleos_wm_qmp_drag_delta_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### SimpleOS WM QMP drag-delta Simple binary contract

#### selects self hosted Simple and records launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"$ROOT_DIR\"/bin/release/*/simple")
expect(script).to_contain("\"$ROOT_DIR\"/release/*/simple")
expect(script).to_contain("\"$ROOT_DIR\"/build/bootstrap/stage3/simple")
expect(script).to_contain("\"$ROOT_DIR\"/bin/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("qemu_wm_drag_delta_simple_bin=")
expect(script).to_contain("qemu_wm_drag_delta_simple_bin_source=")
expect(script).to_contain("qemu_wm_drag_delta_simple_bin_status=")
```

</details>

#### rejects explicit Rust seed before SimpleOS QMP launch

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-simpleos-wm-qmp-drag-delta-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-simpleos-wm-qmp-drag-delta-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("qemu_wm_drag_delta_status=fail")
expect(output).to_contain("qemu_wm_drag_delta_reason=simple-bin-forbidden")
expect(output).to_contain("qemu_wm_drag_delta_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("qemu_wm_drag_delta_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("qemu_wm_drag_delta_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason: simple-bin-forbidden")
val (_launch_out, _launch_err, launch_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/launch.out"])
expect(launch_code).to_equal(0)
val (_drag_out, _drag_err, drag_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/drag.out"])
expect(drag_code).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md](doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md)
- **Design:** [doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md](doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md](doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md)


</details>
