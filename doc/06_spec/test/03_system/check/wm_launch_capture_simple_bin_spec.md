# WM Launch Capture Simple Binary Contract

> The WM launch capture wrapper aggregates host WM, SimpleOS WM, Electron, and QEMU capture evidence. It must not hide GUI/WM regressions behind the bootstrap Rust seed, and child wrappers must receive the same selected Simple binary.

<!-- sdn-diagram:id=wm_launch_capture_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_launch_capture_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

wm_launch_capture_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_launch_capture_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# WM Launch Capture Simple Binary Contract

The WM launch capture wrapper aggregates host WM, SimpleOS WM, Electron, and QEMU capture evidence. It must not hide GUI/WM regressions behind the bootstrap Rust seed, and child wrappers must receive the same selected Simple binary.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/wm_launch_capture_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The WM launch capture wrapper aggregates host WM, SimpleOS WM, Electron, and
QEMU capture evidence. It must not hide GUI/WM regressions behind the bootstrap
Rust seed, and child wrappers must receive the same selected Simple binary.

## Requirements

**Requirements:** N/A

- REQ-WM-LAUNCH-CAPTURE-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-WM-LAUNCH-CAPTURE-BIN-002: Explicit Rust seed paths produce
  `simple-bin-forbidden` before contract, spec, Electron, or QEMU work.
- REQ-WM-LAUNCH-CAPTURE-BIN-003: Evidence records selected Simple binary,
  source, and status fields.
- REQ-WM-LAUNCH-CAPTURE-BIN-004: Electron MDI child evidence receives the
  selected Simple binary and source provenance.

## Plan

**Plan:** doc/03_plan/os/wm/simple_gui_wm_restart_2026-05-28.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and provenance fields.
3. Inspect the Electron MDI child call for Simple binary forwarding.
4. Run the wrapper with a Rust seed `SIMPLE_BIN` override.
5. Confirm contract/spec/Electron/QEMU logs are not created on the forbidden
   path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before generating temporary contract sources
or launching any child evidence command.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/wm_launch_capture_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### WM launch capture Simple binary contract

#### selects self hosted Simple and forwards launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-wm-launch-capture-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("wm_launch_capture_simple_bin=")
expect(script).to_contain("wm_launch_capture_simple_bin_source=")
expect(script).to_contain("wm_launch_capture_simple_bin_status=")
expect(script).to_contain("SIMPLE_BIN=")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("run_with_timeout sh scripts/check/check-electron-mdi-evidence.shs")
```

</details>

#### rejects explicit Rust seed before contract specs or child evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-wm-launch-capture-seed-forbidden"
val command = "rm -rf " + root + " && mkdir -p " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-wm-launch-capture-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("wm_launch_capture_evidence_status=fail")
expect(output).to_contain("wm_launch_capture_evidence_reason=simple-bin-forbidden")
expect(output).to_contain("wm_launch_capture_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("wm_launch_capture_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("wm_launch_capture_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason: simple-bin-forbidden")
val (_contract_out, _contract_err, contract_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/contract.log"])
expect(contract_code).to_equal(0)
val (_spec_out, _spec_err, spec_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/spec.log"])
expect(spec_code).to_equal(0)
val (_electron_out, _electron_err, electron_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/electron-mdi.log"])
expect(electron_code).to_equal(0)
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
