# QEMU Capture Fake QMP Simple Binary Contract

> The fake-QMP capture wrapper is used by the QEMU GTK WM capture aggregate when live QMP is unavailable. It must be safe to run standalone without falling back to the Rust bootstrap seed.

<!-- sdn-diagram:id=qemu_capture_fake_qmp_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=qemu_capture_fake_qmp_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

qemu_capture_fake_qmp_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=qemu_capture_fake_qmp_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# QEMU Capture Fake QMP Simple Binary Contract

The fake-QMP capture wrapper is used by the QEMU GTK WM capture aggregate when live QMP is unavailable. It must be safe to run standalone without falling back to the Rust bootstrap seed.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/qemu_capture_fake_qmp_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The fake-QMP capture wrapper is used by the QEMU GTK WM capture aggregate when
live QMP is unavailable. It must be safe to run standalone without falling back
to the Rust bootstrap seed.

## Requirements

**Requirements:** N/A

- REQ-QEMU-FAKE-QMP-BIN-001: Default Simple binary selection is self-hosted
  only.
- REQ-QEMU-FAKE-QMP-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before Node fake-QMP server startup.
- REQ-QEMU-FAKE-QMP-BIN-003: Evidence records selected Simple binary, source,
  and status fields.

## Plan

**Plan:** doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
4. Confirm stdout and report show `simple-bin-forbidden`.
5. Confirm fake-QMP server and Simple capture logs are not created.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before generating the Node fake-QMP server
or temporary Simple capture program.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/qemu_capture_fake_qmp_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### QEMU capture fake-QMP Simple binary contract

#### selects self hosted Simple and records launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-qemu-capture-fake-qmp-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("qemu_capture_fake_qmp_simple_bin=")
expect(script).to_contain("qemu_capture_fake_qmp_simple_bin_source=")
expect(script).to_contain("qemu_capture_fake_qmp_simple_bin_status=")
```

</details>

#### rejects explicit Rust seed before fake QMP server startup

<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-qemu-capture-fake-qmp-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-qemu-capture-fake-qmp-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("qemu_capture_fake_qmp_status=fail")
expect(output).to_contain("qemu_capture_fake_qmp_reason=simple-bin-forbidden")
expect(output).to_contain("qemu_capture_fake_qmp_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("qemu_capture_fake_qmp_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("qemu_capture_fake_qmp_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason: simple-bin-forbidden")
val (_server_out, _server_err, server_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/fake-qmp-server.log"])
expect(server_code).to_equal(0)
val (_simple_out, _simple_err, simple_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/simple-capture.log"])
expect(simple_code).to_equal(0)
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
