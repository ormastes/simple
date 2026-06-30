# Node Web Render Bitmap Simple Binary Contract

> `scripts/check/check-node-web-render-bitmap-evidence.shs` compares a pure Simple bitmap fixture against the JavaScript baseline renderer. That comparison is part of web-renderer hardening, so its Simple side must not silently run through the Rust seed compiler or driver. A green parity row produced by the seed would not prove the production self-hosted path used by the GUI/Web goal.

<!-- sdn-diagram:id=node_web_render_bitmap_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=node_web_render_bitmap_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

node_web_render_bitmap_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=node_web_render_bitmap_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Node Web Render Bitmap Simple Binary Contract

`scripts/check/check-node-web-render-bitmap-evidence.shs` compares a pure Simple bitmap fixture against the JavaScript baseline renderer. That comparison is part of web-renderer hardening, so its Simple side must not silently run through the Rust seed compiler or driver. A green parity row produced by the seed would not prove the production self-hosted path used by the GUI/Web goal.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/check/node_web_render_bitmap_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`scripts/check/check-node-web-render-bitmap-evidence.shs` compares a pure Simple
bitmap fixture against the JavaScript baseline renderer. That comparison is part
of web-renderer hardening, so its Simple side must not silently run through the
Rust seed compiler or driver. A green parity row produced by the seed would not
prove the production self-hosted path used by the GUI/Web goal.

The wrapper must choose only repository self-hosted Simple binaries when the
caller leaves `SIMPLE_BIN` unset. Accepted default candidates are `bin/simple`,
`./bin/simple`, `release/*/simple`, `bin/release/*/simple`, and
`build/bootstrap/stage3/simple`. If none exists, the wrapper must emit typed
`missing` evidence instead of falling back to `src/compiler_rust`.

Explicit overrides are still allowed for local debugging, but any override under
`src/compiler_rust/**` is classified as `forbidden`. The wrapper records this in
`js_web_render_bitmap_simple_bin`, `js_web_render_bitmap_simple_bin_source`, and
`js_web_render_bitmap_simple_bin_status`, exits nonzero, and does not run the
bitmap parity loop.

## Requirements

**Requirements:** N/A

- REQ-NODE-WEB-SIMPLE-BIN-001: Default Simple binary selection is self-hosted
  only.
- REQ-NODE-WEB-SIMPLE-BIN-002: Missing self-hosted Simple binaries produce
  `simple-bin-missing` evidence.
- REQ-NODE-WEB-SIMPLE-BIN-003: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence.
- REQ-NODE-WEB-SIMPLE-BIN-004: Every unavailable and completed evidence row
  includes the Simple binary path, source, and status.

## Plan

**Plan:** N/A

1. Inspect the wrapper source for candidate selection, seed detection, export,
   and evidence keys.
2. Run a seed-forbidden scenario with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
3. Read `build/test-node-web-render-bitmap-seed-forbidden/out/evidence.env`.
4. Confirm the wrapper reports unavailable evidence with reason
   `simple-bin-forbidden`.

## Design

**Design:** N/A

The wrapper performs Simple binary validation before checking Node availability
or building the generated `.spl` fixture. That ordering keeps seed rejection
deterministic and cheap. The evidence namespace remains
`js_web_render_bitmap_*`; the new provenance fields are appended to both
unavailable rows and normal parity rows so downstream aggregators can audit the
driver independently from bitmap pass/fail status.

## Research

**Research:** N/A

This spec follows the same fail-closed pattern used by the Electron layout
manifest, production GUI/Web parity, backend parity, generated GUI matrix, and
Metal framebuffer readback wrappers. The common rule is that production
evidence may use a self-hosted Simple binary or an explicit non-seed override,
but never an implicit or explicit Rust seed binary.

## Commands

```sh
release/x86_64-unknown-linux-gnu/simple test test/03_system/check/node_web_render_bitmap_simple_bin_spec.spl --mode=interpreter
```

## Examples

Default self-hosted selection, when a release binary is available:

```sh
BUILD_DIR=build/node-web-render-bitmap \
REPORT_PATH=build/node-web-render-bitmap/report.md \
sh scripts/check/check-node-web-render-bitmap-evidence.shs
```

Expected successful provenance fields in `evidence.env`:

```text
js_web_render_bitmap_simple_bin=release/x86_64-unknown-linux-gnu/simple
js_web_render_bitmap_simple_bin_source=repo-self-hosted-fallback
js_web_render_bitmap_simple_bin_status=pass
```

Explicit Rust seed rejection:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
BUILD_DIR=build/node-web-render-bitmap-seed \
REPORT_PATH=build/node-web-render-bitmap-seed/report.md \
sh scripts/check/check-node-web-render-bitmap-evidence.shs
```

Expected failure provenance fields in `evidence.env`:

```text
js_web_render_bitmap_status=unavailable
js_web_render_bitmap_reason=simple-bin-forbidden
js_web_render_bitmap_simple_bin=src/compiler_rust/target/release/simple
js_web_render_bitmap_simple_bin_source=explicit-env-rust-seed-forbidden
js_web_render_bitmap_simple_bin_status=forbidden
```

Missing self-hosted binary behavior:

```sh
SIMPLE_BIN= \
BUILD_DIR=build/node-web-render-bitmap-missing \
REPORT_PATH=build/node-web-render-bitmap-missing/report.md \
sh scripts/check/check-node-web-render-bitmap-evidence.shs
```

The wrapper must report `js_web_render_bitmap_reason=simple-bin-missing` and
must not substitute any `src/compiler_rust/**` path.

## Expected Evidence

- `js_web_render_bitmap_status=unavailable`
- `js_web_render_bitmap_reason=simple-bin-forbidden`
- `js_web_render_bitmap_simple_bin=src/compiler_rust/target/release/simple`
- `js_web_render_bitmap_simple_bin_status=forbidden`

## Traceability

- Goal: web renderer hardening without Rust seed fallback.
- Wrapper: `scripts/check/check-node-web-render-bitmap-evidence.shs`
- Guide: `doc/07_guide/ui/web_render_backend.md`
- Generated manual: `doc/06_spec/test/03_system/check/node_web_render_bitmap_simple_bin_spec.md`

## Scenarios

### Node web render bitmap Simple binary contract

#### selects self hosted Simple and rejects Rust seed overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-node-web-render-bitmap-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("build/bootstrap/stage3/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("js_web_render_bitmap_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("js_web_render_bitmap_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("js_web_render_bitmap_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### records explicit Rust seed Simple binary as forbidden evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-node-web-render-bitmap-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-node-web-render-bitmap-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("js_web_render_bitmap_status=unavailable")
expect(evidence).to_contain("js_web_render_bitmap_reason=simple-bin-forbidden")
expect(evidence).to_contain("js_web_render_bitmap_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("js_web_render_bitmap_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("js_web_render_bitmap_simple_bin_status=forbidden")
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
