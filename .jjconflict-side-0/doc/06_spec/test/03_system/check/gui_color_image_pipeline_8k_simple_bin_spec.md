# GUI Color/Image Pipeline 8K Simple Binary Contract

> `scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` generates a focused Simple probe for the 7680x4320 BGRA8 surface plan, packed hot path, Lab/XYZ roundtrip, and image decoder fail-closed contracts. It also runs focused surface, color, image decode, and TIFF raster specs. This evidence is part of the GUI 8K hardening lane, so it must not silently execute through `src/compiler_rust/**`.

<!-- sdn-diagram:id=gui_color_image_pipeline_8k_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gui_color_image_pipeline_8k_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gui_color_image_pipeline_8k_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gui_color_image_pipeline_8k_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GUI Color/Image Pipeline 8K Simple Binary Contract

`scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` generates a focused Simple probe for the 7680x4320 BGRA8 surface plan, packed hot path, Lab/XYZ roundtrip, and image decoder fail-closed contracts. It also runs focused surface, color, image decode, and TIFF raster specs. This evidence is part of the GUI 8K hardening lane, so it must not silently execute through `src/compiler_rust/**`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_color_image_pipeline_8k.md |
| Design | doc/05_design/compiler/graphics/gui_color_image_pipeline_8k.md |
| Research | doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md |
| Source | `test/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` generates a
focused Simple probe for the 7680x4320 BGRA8 surface plan, packed hot path,
Lab/XYZ roundtrip, and image decoder fail-closed contracts. It also runs
focused surface, color, image decode, and TIFF raster specs. This evidence is
part of the GUI 8K hardening lane, so it must not silently execute through
`src/compiler_rust/**`.

## Requirements

**Requirements:** N/A

- REQ-GUI-8K-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-GUI-8K-BIN-002: Missing self-hosted Simple binaries produce
  `simple-bin-missing` evidence.
- REQ-GUI-8K-BIN-003: Rust seed Simple paths produce `simple-bin-forbidden`
  evidence.
- REQ-GUI-8K-BIN-004: Failure and completed evidence rows include
  `gui_color_image_pipeline_8k_simple_bin`,
  `gui_color_image_pipeline_8k_simple_bin_source`, and
  `gui_color_image_pipeline_8k_simple_bin_status`.

## Plan

**Plan:** doc/09_report/gui_color_image_pipeline_8k.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Read `build/test-gui-color-image-pipeline-8k-seed-forbidden/out/evidence.env`.
5. Confirm `reason=simple-bin-forbidden` and `simple_bin_status=forbidden`.
6. Run the wrapper normally on the current host and confirm the current
   core-module 8K probe passes with self-hosted provenance.

## Design

**Design:** doc/05_design/compiler/graphics/gui_color_image_pipeline_8k.md

The wrapper validates `SIMPLE_BIN` before writing or executing the generated
8K probe. That makes seed rejection cheap and deterministic while preserving
the existing full evidence path for real 8K GUI color/image runs.

## Research

**Research:** doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md

This local hardening follows the same fail-closed Simple binary policy used by
the GUI/Web parity, Chrome/Electron geometry, Node/Web bitmap, Simple Web
Engine2D JS bitmap, macOS live GUI, Metal readback, and CPU/Metal parity
wrappers.

## Examples

Run the contract:

```sh
SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test test/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.spl --mode=interpreter
```

Run the deterministic Rust seed rejection probe:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
BUILD_DIR=build/gui-color-image-pipeline-8k-seed \
REPORT_PATH=build/gui-color-image-pipeline-8k-seed/report.md \
sh scripts/check/check-gui-color-image-pipeline-8k-evidence.shs
```

## Expected Evidence

Explicit Rust seed rejection writes:

```text
gui_color_image_pipeline_8k_status=fail
gui_color_image_pipeline_8k_reason=simple-bin-forbidden
gui_color_image_pipeline_8k_simple_bin=src/compiler_rust/target/release/simple
gui_color_image_pipeline_8k_simple_bin_source=explicit-env-rust-seed-forbidden
gui_color_image_pipeline_8k_simple_bin_status=forbidden
```

Normal completed evidence must include:

```text
gui_color_image_pipeline_8k_simple_bin_status=pass
gui_color_image_pipeline_8k_width=7680
gui_color_image_pipeline_8k_height=4320
gui_color_image_pipeline_8k_framebuffer_bytes=132710400
```

Normal current-source execution must pass without the deleted browser example
specs:

```text
gui_color_image_pipeline_8k_status=pass
gui_color_image_pipeline_8k_reason=pass
gui_color_image_pipeline_8k_simple_bin_status=pass
gui_color_image_pipeline_8k_image_fail_closed_ok=true
```

## Traceability

- Goal: GUI 8K hardening without Rust seed fallback.
- Wrapper: `scripts/check/check-gui-color-image-pipeline-8k-evidence.shs`
- Report index: `doc/09_report/gui_color_image_pipeline_8k.md`

## Scenarios

### GUI color/image pipeline 8K Simple binary contract

#### selects self hosted Simple and rejects Rust seed overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gui-color-image-pipeline-8k-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("build/bootstrap/stage3/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("gui_color_image_pipeline_8k_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("gui_color_image_pipeline_8k_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("gui_color_image_pipeline_8k_simple_bin_status=$SIMPLE_BIN_STATUS")
expect(script).to_contain("SIMPLE_EXECUTION_MODE=interpret")
expect(script).to_contain("gui_color_image_pipeline_8k_simple_execution_mode=interpret")
```

</details>

#### records explicit Rust seed Simple binary as forbidden evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gui-color-image-pipeline-8k-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gui-color-image-pipeline-8k-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("gui_color_image_pipeline_8k_status=fail")
expect(evidence).to_contain("gui_color_image_pipeline_8k_reason=simple-bin-forbidden")
expect(evidence).to_contain("gui_color_image_pipeline_8k_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("gui_color_image_pipeline_8k_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("gui_color_image_pipeline_8k_simple_bin_status=forbidden")
```

</details>

#### keeps normal current source 8K evidence interpreter pinned without generic field len

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gui-color-image-pipeline-8k-evidence.shs")
expect(script).to_contain("gui_color_image_pipeline_8k_status=pass")
expect(script).to_contain("gui_color_image_pipeline_8k_reason=pass")
expect(script).to_contain("gui_color_image_pipeline_8k_width=\" + plan.width.to_text()")
expect(script).to_contain("gui_color_image_pipeline_8k_height=\" + plan.height.to_text()")
expect(script).to_contain("gui_color_image_pipeline_8k_framebuffer_bytes=\" + plan.framebuffer_bytes.to_text()")
expect(script).to_contain("gui_color_image_pipeline_8k_image_fail_closed_ok=\" + image_fail_closed_ok.to_text()")
expect(script).to_contain("gui_color_image_pipeline_8k_simple_bin_status=$SIMPLE_BIN_STATUS")
expect(script).to_contain("gui_color_image_pipeline_8k_simple_execution_mode=interpret")
expect(script).to_contain("transform.pixels[0] == red_argb")
val no_field_len = not script.contains("transform.pixels.len()")
expect(no_field_len).to_be(true)
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

- **Plan:** [doc/09_report/gui_color_image_pipeline_8k.md](doc/09_report/gui_color_image_pipeline_8k.md)
- **Design:** [doc/05_design/compiler/graphics/gui_color_image_pipeline_8k.md](doc/05_design/compiler/graphics/gui_color_image_pipeline_8k.md)
- **Research:** [doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md](doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md)


</details>
