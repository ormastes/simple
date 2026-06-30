# GUI Hardening Open Gates Simple Binary Contract

> The open-gates wrapper can launch multiple GUI browser/corpus SSpecs. This contract keeps that launcher on repo self-hosted Simple binaries and makes Rust seed rejection deterministic and cheap.

<!-- sdn-diagram:id=gui_hardening_open_gates_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_hardening_open_gates_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_hardening_open_gates_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_hardening_open_gates_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Hardening Open Gates Simple Binary Contract

The open-gates wrapper can launch multiple GUI browser/corpus SSpecs. This contract keeps that launcher on repo self-hosted Simple binaries and makes Rust seed rejection deterministic and cheap.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The open-gates wrapper can launch multiple GUI browser/corpus SSpecs. This
contract keeps that launcher on repo self-hosted Simple binaries and makes Rust
seed rejection deterministic and cheap.

## Requirements

**Requirements:** N/A

- REQ-GUI-HARDENING-GATES-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-GUI-HARDENING-GATES-BIN-002: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence before any corpus specs run.
- REQ-GUI-HARDENING-GATES-BIN-003: Failure evidence records selected Simple
  binary, source, status, and report path.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Confirm stdout reports `simple-bin-forbidden`.
5. Confirm no corpus spec summary is created for the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates the launcher before artifact snapshots and before any
browser/corpus SSpec process is spawned.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gui_hardening_open_gates_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### GUI hardening open gates Simple binary contract

#### selects self hosted Simple and records launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gui-hardening-open-gates.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("gui_hardening_open_gates_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("gui_hardening_open_gates_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("gui_hardening_open_gates_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### rejects explicit Rust seed before running browser corpus specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-hardening-open-gates-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-hardening-open-gates.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("gui_hardening_open_gates_status=fail")
expect(output).to_contain("gui_hardening_open_gates_reason=simple-bin-forbidden")
expect(output).to_contain("gui_hardening_open_gates_simple_bin=src/compiler_rust/target/release/simple")
expect(output).to_contain("gui_hardening_open_gates_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("gui_hardening_open_gates_simple_bin_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("- reason=simple-bin-forbidden")
val (_ls_out, _ls_err, ls_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/spec-summary.txt"])
expect(ls_code).to_equal(0)
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

- **Plan:** [doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md](doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md)
- **Design:** [doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md](doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md)
- **Research:** [doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md](doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md)


</details>
