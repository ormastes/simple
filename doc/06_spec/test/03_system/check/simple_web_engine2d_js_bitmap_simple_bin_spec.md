# Simple Web Engine2D JS Bitmap Simple Binary Contract

> `scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs` renders the same Simple Web Engine2D scene through a pure Simple static-pixel-cache path and a JavaScript baseline fixture. It is a direct GUI/Web/2D hardening lane because the evidence records scene identity, dimensions, checksums, weighted checksums, ARGB file paths, mismatch count, cache hits, cache stores, and timing.

<!-- sdn-diagram:id=simple_web_engine2d_js_bitmap_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_web_engine2d_js_bitmap_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

simple_web_engine2d_js_bitmap_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_web_engine2d_js_bitmap_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Simple Web Engine2D JS Bitmap Simple Binary Contract

`scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs` renders the same Simple Web Engine2D scene through a pure Simple static-pixel-cache path and a JavaScript baseline fixture. It is a direct GUI/Web/2D hardening lane because the evidence records scene identity, dimensions, checksums, weighted checksums, ARGB file paths, mismatch count, cache hits, cache stores, and timing.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/check/simple_web_engine2d_js_bitmap_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs` renders the
same Simple Web Engine2D scene through a pure Simple static-pixel-cache path and
a JavaScript baseline fixture. It is a direct GUI/Web/2D hardening lane because
the evidence records scene identity, dimensions, checksums, weighted checksums,
ARGB file paths, mismatch count, cache hits, cache stores, and timing.

For the active rendering goal, a parity row is only useful when the Simple side
comes from a production self-hosted binary. If this wrapper accepted
`src/compiler_rust/**`, then a green bitmap row could prove only the seed path,
not the current self-hosted GUI/Web renderer path. The wrapper therefore shares
the fail-closed Simple binary contract used by production GUI/Web parity,
Electron layout manifest, generated GUI matrix, Metal readback, and Node/Web
bitmap parity wrappers.

## Requirements

**Requirements:** N/A

- REQ-SWEB-E2D-JS-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-SWEB-E2D-JS-BIN-002: Missing self-hosted Simple binaries produce
  `simple-bin-missing` evidence.
- REQ-SWEB-E2D-JS-BIN-003: Explicit Rust seed Simple paths produce
  `simple-bin-forbidden` evidence.
- REQ-SWEB-E2D-JS-BIN-004: Every unavailable and completed evidence row includes
  `simple_web_engine2d_js_simple_bin`,
  `simple_web_engine2d_js_simple_bin_source`, and
  `simple_web_engine2d_js_simple_bin_status`.

## Plan

**Plan:** N/A

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Read `build/test-simple-web-engine2d-js-bitmap-seed-forbidden/out/evidence.env`.
5. Confirm the wrapper reports unavailable evidence with reason
   `simple-bin-forbidden` and preserves the explicit seed path for audit.

## Design

**Design:** N/A

Simple binary validation runs before Node availability checks and before the
generated `.spl` fixture is executed. That order keeps seed rejection cheap and
independent from host JavaScript tooling. Default candidate selection allows
only `bin/simple`, `./bin/simple`, `release/*/simple`, `bin/release/*/simple`,
and `build/bootstrap/stage3/simple`. The wrapper preserves explicit non-seed
overrides but annotates their source as `explicit-env`.

## Research

**Research:** N/A

This spec is local repository hardening. It follows the existing typed evidence
shape used across GUI/Web wrappers: a missing binary is not papered over by a
seed fallback, and a Rust seed override is recorded as `forbidden` rather than
executed.

## Commands

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/check/simple_web_engine2d_js_bitmap_simple_bin_spec.spl --mode=interpreter
```

## Examples

Default self-hosted selection:

```sh
BUILD_DIR=build/simple-web-engine2d-js \
REPORT_PATH=build/simple-web-engine2d-js/report.md \
sh scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs
```

Expected successful provenance:

```text
simple_web_engine2d_js_simple_bin=release/x86_64-unknown-linux-gnu/simple
simple_web_engine2d_js_simple_bin_source=repo-self-hosted-fallback
simple_web_engine2d_js_simple_bin_status=pass
```

Explicit Rust seed rejection:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
BUILD_DIR=build/simple-web-engine2d-js-seed \
REPORT_PATH=build/simple-web-engine2d-js-seed/report.md \
sh scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs
```

Expected failure provenance:

```text
simple_web_engine2d_js_status=unavailable
simple_web_engine2d_js_reason=simple-bin-forbidden
simple_web_engine2d_js_simple_bin=src/compiler_rust/target/release/simple
simple_web_engine2d_js_simple_bin_source=explicit-env-rust-seed-forbidden
simple_web_engine2d_js_simple_bin_status=forbidden
```

## Expected Evidence

- `simple_web_engine2d_js_status=unavailable`
- `simple_web_engine2d_js_reason=simple-bin-forbidden`
- `simple_web_engine2d_js_simple_bin=src/compiler_rust/target/release/simple`
- `simple_web_engine2d_js_simple_bin_status=forbidden`

## Traceability

- Goal: GUI/Web/2D renderer hardening without Rust seed fallback.
- Wrapper: `scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs`
- Guide: `doc/07_guide/ui/web_render_backend.md`
- Generated manual:
  `doc/06_spec/test/03_system/check/simple_web_engine2d_js_bitmap_simple_bin_spec.md`

## Scenarios

### Simple Web Engine2D JS bitmap Simple binary contract

#### selects self hosted Simple and rejects Rust seed overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("build/bootstrap/stage3/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("simple_web_engine2d_js_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("simple_web_engine2d_js_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("simple_web_engine2d_js_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### records explicit Rust seed Simple binary as forbidden evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-simple-web-engine2d-js-bitmap-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-simple-web-engine2d-js-bitmap-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("simple_web_engine2d_js_status=unavailable")
expect(evidence).to_contain("simple_web_engine2d_js_reason=simple-bin-forbidden")
expect(evidence).to_contain("simple_web_engine2d_js_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("simple_web_engine2d_js_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("simple_web_engine2d_js_simple_bin_status=forbidden")
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
