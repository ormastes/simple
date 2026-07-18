# Electron HTML Compat Geometry Simple Binary Contract

> `scripts/check/check-electron-html-compat-geometry-evidence.shs` captures one HTML compatibility fixture through Electron and compares the geometry with the Simple structural probe. It is a direct web-renderer hardening lane: the Electron side proves browser geometry capture, and the Simple side proves the current renderer/probe interpretation.

<!-- sdn-diagram:id=electron_html_compat_geometry_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=electron_html_compat_geometry_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

electron_html_compat_geometry_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=electron_html_compat_geometry_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Electron HTML Compat Geometry Simple Binary Contract

`scripts/check/check-electron-html-compat-geometry-evidence.shs` captures one HTML compatibility fixture through Electron and compares the geometry with the Simple structural probe. It is a direct web-renderer hardening lane: the Electron side proves browser geometry capture, and the Simple side proves the current renderer/probe interpretation.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/check/electron_html_compat_geometry_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`scripts/check/check-electron-html-compat-geometry-evidence.shs` captures one
HTML compatibility fixture through Electron and compares the geometry with the
Simple structural probe. It is a direct web-renderer hardening lane: the
Electron side proves browser geometry capture, and the Simple side proves the
current renderer/probe interpretation.

The Simple side must not silently run through `src/compiler_rust/**`. This spec
therefore checks both the source contract and a real negative execution where an
explicit Rust seed path is provided. The negative execution must stop before
Electron dependencies matter, write `evidence.env`, and preserve the rejected
path for audit.

## Requirements

**Requirements:** N/A

- REQ-ELECTRON-HTML-GEOM-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-ELECTRON-HTML-GEOM-BIN-002: Missing self-hosted Simple binaries produce
  `simple-bin-missing` evidence.
- REQ-ELECTRON-HTML-GEOM-BIN-003: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence.
- REQ-ELECTRON-HTML-GEOM-BIN-004: Failure and completed evidence rows include
  `simple_bin`, `simple_bin_source`, and `simple_bin_status`.

## Plan

**Plan:** N/A

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Read `build/test-electron-html-compat-geometry-seed-forbidden/out/evidence.env`.
5. Confirm `reason=simple-bin-forbidden` and `simple_bin_status=forbidden`.

## Design

**Design:** N/A

The wrapper validates `SIMPLE_BIN` before Node, npm, xvfb, Electron, or Simple
fixture execution. That makes the seed-forbidden path cheap and deterministic
on hosts without GUI dependencies. The existing stdout fields are preserved for
manual use, while `evidence.env` gives downstream checks a stable typed file.

## Research

**Research:** N/A

This local hardening follows the same fail-closed Simple binary policy used by
the production GUI/Web parity, Chrome geometry manifest, Node/Web bitmap,
Simple Web Engine2D JS bitmap, generated GUI matrix, backend parity, and Metal
readback wrappers.

## Commands

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/check/electron_html_compat_geometry_simple_bin_spec.spl --mode=interpreter
```

## Examples

Explicit Rust seed rejection:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
BUILD_DIR=build/electron-html-compat-geometry-seed \
REPORT_PATH=build/electron-html-compat-geometry-seed/report.md \
sh scripts/check/check-electron-html-compat-geometry-evidence.shs
```

Expected failure provenance:

```text
status=fail
reason=simple-bin-forbidden
simple_bin=src/compiler_rust/target/release/simple
simple_bin_source=explicit-env-rust-seed-forbidden
simple_bin_status=forbidden
```

## Expected Evidence

- `status=fail`
- `reason=simple-bin-forbidden`
- `simple_bin=src/compiler_rust/target/release/simple`
- `simple_bin_status=forbidden`

## Traceability

- Goal: web renderer hardening without Rust seed fallback.
- Wrapper: `scripts/check/check-electron-html-compat-geometry-evidence.shs`
- Guide: `doc/07_guide/ui/web_render_backend.md`
- Generated manual:
  `doc/06_spec/test/03_system/check/electron_html_compat_geometry_simple_bin_spec.md`

## Scenarios

### Electron HTML compat geometry Simple binary contract

#### selects self hosted Simple and rejects Rust seed overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-electron-html-compat-geometry-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("build/bootstrap/stage3/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("simple_bin=$SIMPLE_BIN")
expect(script).to_contain("simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### records explicit Rust seed Simple binary as forbidden evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-electron-html-compat-geometry-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-electron-html-compat-geometry-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("status=fail")
expect(evidence).to_contain("reason=simple-bin-forbidden")
expect(evidence).to_contain("simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("simple_bin_status=forbidden")
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


</details>
