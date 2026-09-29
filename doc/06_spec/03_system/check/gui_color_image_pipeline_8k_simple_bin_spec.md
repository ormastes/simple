# GUI Color/Image Pipeline 8K Simple Binary Contract

> `scripts/check/check-gui-color-image-pipeline-8k-evidence.shs` generates a focused Simple probe for the 7680x4320 BGRA8 surface plan, packed hot path, Lab/XYZ roundtrip, and image decoder fail-closed contracts. It also runs focused surface, color, image decode, and TIFF raster specs. This evidence is part of the GUI 8K hardening lane, so it must not silently execute through `src/compiler_rust/**`.

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
| Updated | 2026-08-26 |
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

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- selects self hosted Simple and rejects Rust seed overrides


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("selects self hosted Simple and rejects Rust seed overrides")
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

- records explicit Rust seed Simple binary as forbidden evidence
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("records explicit Rust seed Simple binary as forbidden evidence")
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

- keeps normal current source 8K evidence interpreter pinned without generic field len


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps normal current source 8K evidence interpreter pinned without generic field len")
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

- **Plan:** `doc/09_report/gui_color_image_pipeline_8k.md`
- **Design:** `doc/05_design/compiler/graphics/gui_color_image_pipeline_8k.md`
- **Research:** `doc/01_research/ui/graphics/gui/gui_color_image_pipeline_8k.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-GUI-8K-BIN-001:`
- `REQ-GUI-8K-BIN-002:`
- `REQ-GUI-8K-BIN-003:`
- `REQ-GUI-8K-BIN-004:`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e241e925860015e4a96059e38b4afe10c54273da7f04de665d3d9d1b4552f1d9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e241e925860015e4a96059e38b4afe10c54273da7f04de665d3d9d1b4552f1d9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e241e925860015e4a96059e38b4afe10c54273da7f04de665d3d9d1b4552f1d9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.spl
mirror: doc/06_spec/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'selects self hosted Simple and rejects Rust seed overrides' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.spl:147:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records explicit Rust seed Simple binary as forbidden evidence' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/check/gui_color_image_pipeline_8k_simple_bin_spec.spl:162:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps normal current source 8K evidence interpreter pinned without generic field len' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
