# Chrome HTML Compat Geometry Manifest Simple Binary Contract

> `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs` captures real Chrome headless geometry for many `html_compat` fixtures, then compares the captured border-box geometry and computed structural fields against Simple. This is a broad web-renderer hardening lane, so a successful row must prove the self-hosted Simple path rather than the Rust seed compiler or driver.

<!-- sdn-diagram:id=chrome_html_compat_geometry_manifest_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chrome_html_compat_geometry_manifest_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chrome_html_compat_geometry_manifest_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chrome_html_compat_geometry_manifest_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Chrome HTML Compat Geometry Manifest Simple Binary Contract

`scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs` captures real Chrome headless geometry for many `html_compat` fixtures, then compares the captured border-box geometry and computed structural fields against Simple. This is a broad web-renderer hardening lane, so a successful row must prove the self-hosted Simple path rather than the Rust seed compiler or driver.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/check/chrome_html_compat_geometry_manifest_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs` captures
real Chrome headless geometry for many `html_compat` fixtures, then compares the
captured border-box geometry and computed structural fields against Simple. This
is a broad web-renderer hardening lane, so a successful row must prove the
self-hosted Simple path rather than the Rust seed compiler or driver.

The wrapper writes `build/chrome_html_compat_geometry_manifest_evidence/summary.env`
by default. This spec verifies that the summary always includes `simple_bin`,
`simple_bin_source`, and `simple_bin_status`, and that explicit
`src/compiler_rust/**` overrides are rejected as `simple-bin-forbidden`.

## Requirements

**Requirements:** N/A

- REQ-CHROME-HTML-GEOM-BIN-001: Default Simple binary selection is self-hosted
  only.
- REQ-CHROME-HTML-GEOM-BIN-002: Missing self-hosted Simple binaries produce
  `simple-bin-missing` evidence.
- REQ-CHROME-HTML-GEOM-BIN-003: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence.
- REQ-CHROME-HTML-GEOM-BIN-004: Unavailable and completed summary rows include
  `simple_bin`, `simple_bin_source`, and `simple_bin_status`.

## Plan

**Plan:** N/A

1. Inspect the wrapper for self-hosted candidate selection.
2. Inspect the wrapper for Rust seed detection and exported Simple provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Read `build/test-chrome-html-compat-geometry-seed-forbidden/out/summary.env`.
5. Confirm `status=unavailable`, `reason=simple-bin-forbidden`, and
   `simple_bin_status=forbidden`.

## Design

**Design:** N/A

Simple binary validation happens after the summary/report paths are initialized
and before fixture capture begins. That keeps the negative path deterministic
and avoids doing any Chrome or Simple rendering when the driver is already
invalid. The wrapper preserves the existing generic `status` and `reason` keys
for downstream consumers while adding Simple binary provenance fields.

## Research

**Research:** N/A

This local hardening follows the same fail-closed pattern used by production
GUI/Web parity, generated GUI matrix, Electron layout manifest, backend parity,
Metal readback, Node/Web bitmap parity, and Simple Web Engine2D JS bitmap
evidence.

## Commands

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/check/chrome_html_compat_geometry_manifest_simple_bin_spec.spl --mode=interpreter
```

## Examples

Default self-hosted selection:

```sh
BUILD_DIR=build/chrome-html-compat-geometry \
REPORT_PATH=build/chrome-html-compat-geometry/report.md \
sh scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs
```

Expected successful provenance:

```text
simple_bin=release/x86_64-unknown-linux-gnu/simple
simple_bin_source=repo-self-hosted-fallback
simple_bin_status=pass
```

Explicit Rust seed rejection:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
BUILD_DIR=build/chrome-html-compat-geometry-seed \
REPORT_PATH=build/chrome-html-compat-geometry-seed/report.md \
sh scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs
```

Expected failure provenance:

```text
status=unavailable
reason=simple-bin-forbidden
simple_bin=src/compiler_rust/target/release/simple
simple_bin_source=explicit-env-rust-seed-forbidden
simple_bin_status=forbidden
```

## Expected Evidence

- `status=unavailable`
- `reason=simple-bin-forbidden`
- `simple_bin=src/compiler_rust/target/release/simple`
- `simple_bin_status=forbidden`

## Traceability

- Goal: web renderer hardening without Rust seed fallback.
- Wrapper:
  `scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs`
- Guide: `doc/07_guide/ui/web_render_backend.md`
- Generated manual:
  `doc/06_spec/test/03_system/check/chrome_html_compat_geometry_manifest_simple_bin_spec.md`

## Scenarios

### Chrome HTML compat geometry manifest Simple binary contract

#### selects self hosted Simple and rejects Rust seed overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs")
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
val root = "build/test-chrome-html-compat-geometry-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-chrome-html-compat-geometry-manifest-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/summary.env")
expect(evidence).to_contain("status=unavailable")
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
