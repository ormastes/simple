# Layered Simple GUI/Web/Engine2D Simple Binary Contract

> The layered wrapper aggregates WebRenderer-to-Engine2D bitmap checks across Node, optional Bun, and Electron GUI capture lanes. This contract keeps that evidence on repo self-hosted Simple launchers and prevents a Rust seed binary from being accepted as GUI/Web/2D hardening evidence.

<!-- sdn-diagram:id=layered_simple_gui_web_engine2d_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layered_simple_gui_web_engine2d_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layered_simple_gui_web_engine2d_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layered_simple_gui_web_engine2d_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layered Simple GUI/Web/Engine2D Simple Binary Contract

The layered wrapper aggregates WebRenderer-to-Engine2D bitmap checks across Node, optional Bun, and Electron GUI capture lanes. This contract keeps that evidence on repo self-hosted Simple launchers and prevents a Rust seed binary from being accepted as GUI/Web/2D hardening evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/layered_simple_gui_web_engine2d_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The layered wrapper aggregates WebRenderer-to-Engine2D bitmap checks across
Node, optional Bun, and Electron GUI capture lanes. This contract keeps that
evidence on repo self-hosted Simple launchers and prevents a Rust seed binary
from being accepted as GUI/Web/2D hardening evidence.

## Requirements

**Requirements:** N/A

- REQ-LAYERED-GUI-WEB-2D-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-LAYERED-GUI-WEB-2D-BIN-002: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence.
- REQ-LAYERED-GUI-WEB-2D-BIN-003: Aggregate evidence records selected Simple
  binary, source, and status fields.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the layered wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Read the generated aggregate `evidence.env`.
5. Confirm `reason=simple-bin-forbidden` and `simple_bin_status=forbidden`.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates the Simple launcher before invoking Node, Bun, or
Electron child bitmap evidence scripts. That makes forbidden seed rejection
cheap and deterministic while preserving the full layered evidence path on
prepared GUI hosts.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

This follows the current GUI/Web/2D render-path assessment and the ongoing
RenderDoc coverage evidence lane tracked in the June 27 GUI coverage report.

## Examples

Run the contract:

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/layered_simple_gui_web_engine2d_simple_bin_spec.spl --mode=interpreter --clean
```

Run the deterministic Rust seed rejection probe:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
BUILD_DIR=build/layered-simple-gui-web-engine2d-seed \
REPORT_PATH=build/layered-simple-gui-web-engine2d-seed/report.md \
sh scripts/check/check-layered-simple-gui-web-engine2d-bitmap-evidence.shs
```

## Scenarios

### Layered Simple GUI/Web/Engine2D Simple binary contract

#### selects self hosted Simple and exports provenance to child probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-layered-simple-gui-web-engine2d-bitmap-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("layered_simple_gui_web_engine2d_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("layered_simple_gui_web_engine2d_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("layered_simple_gui_web_engine2d_simple_bin_status=$SIMPLE_BIN_STATUS")
expect(script).to_contain("SIMPLE_BIN=\"$SIMPLE_BIN\"")
```

</details>

#### records explicit Rust seed Simple binary as forbidden evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-layered-simple-gui-web-engine2d-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-layered-simple-gui-web-engine2d-bitmap-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("layered_simple_gui_web_engine2d_status=unavailable")
expect(evidence).to_contain("layered_simple_gui_web_engine2d_reason=simple-bin-forbidden")
expect(evidence).to_contain("layered_simple_gui_web_engine2d_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("layered_simple_gui_web_engine2d_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("layered_simple_gui_web_engine2d_simple_bin_status=forbidden")
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
