# Engine2D CPU/Metal Parity Simple Binary Contract

> `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` runs `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl`. On macOS it is the bit-level CPU/Metal 2D backend parity gate; on non-macOS hosts it records an explicit skip verdict from the harness. Either lane is release evidence only when the Simple binary provenance is self-hosted.

<!-- sdn-diagram:id=engine2d_cpu_metal_parity_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=engine2d_cpu_metal_parity_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

engine2d_cpu_metal_parity_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=engine2d_cpu_metal_parity_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Engine2D CPU/Metal Parity Simple Binary Contract

`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` runs `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl`. On macOS it is the bit-level CPU/Metal 2D backend parity gate; on non-macOS hosts it records an explicit skip verdict from the harness. Either lane is release evidence only when the Simple binary provenance is self-hosted.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/check/engine2d_cpu_metal_parity_simple_bin_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` runs
`test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl`. On macOS it
is the bit-level CPU/Metal 2D backend parity gate; on non-macOS hosts it records
an explicit skip verdict from the harness. Either lane is release evidence only
when the Simple binary provenance is self-hosted.

The wrapper must not silently run through `src/compiler_rust/**`. This spec
checks the source contract and a deterministic negative execution where
`SIMPLE_BIN=src/compiler_rust/target/release/simple` fails before any Metal host
dependency can matter.

## Requirements

**Requirements:** N/A

- REQ-ENGINE2D-CPU-METAL-BIN-001: Default Simple binary selection is
  self-hosted only.
- REQ-ENGINE2D-CPU-METAL-BIN-002: Missing self-hosted Simple binaries produce
  `simple-bin-missing` evidence.
- REQ-ENGINE2D-CPU-METAL-BIN-003: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence.
- REQ-ENGINE2D-CPU-METAL-BIN-004: Failure and completed evidence rows include
  `engine2d_cpu_metal_parity_simple_bin`,
  `engine2d_cpu_metal_parity_simple_bin_source`, and
  `engine2d_cpu_metal_parity_simple_bin_status`.

## Plan

**Plan:** doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Read `build/test-engine2d-cpu-metal-parity-seed-forbidden/out/parity.env`.
5. Confirm `reason=simple-bin-forbidden` and `simple_bin_status=forbidden`.

## Design

**Design:** N/A

The wrapper validates `SIMPLE_BIN` before launching the parity harness. That
makes seed rejection cheap, deterministic, and Linux-safe while preserving the
host-gated macOS Metal proof path for real platform runs.

## Research

**Research:** N/A

This local hardening follows the same fail-closed Simple binary policy used by
the production GUI/Web parity, Chrome geometry manifest, Electron geometry,
Node/Web bitmap, Simple Web Engine2D JS bitmap, generated GUI matrix, backend
parity, macOS live GUI, and Metal readback wrappers.

## Commands

```sh
SIMPLE_LIB=src release/x86_64-unknown-linux-gnu/simple test test/03_system/check/engine2d_cpu_metal_parity_simple_bin_spec.spl --mode=interpreter
```

## Examples

Run the normal host-gated parity wrapper:

```sh
BUILD_DIR=build/engine2d-cpu-metal-parity-current \
REPORT_PATH=build/engine2d-cpu-metal-parity-current/report.md \
SIMPLE_LIB=src \
sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
```

Run the deterministic Rust seed rejection probe:

```sh
SIMPLE_BIN=src/compiler_rust/target/release/simple \
BUILD_DIR=build/engine2d-cpu-metal-parity-seed \
REPORT_PATH=build/engine2d-cpu-metal-parity-seed/report.md \
SIMPLE_LIB=src \
sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
```

The second command must fail before the harness runs.

## Expected Evidence

Explicit Rust seed rejection writes:

```text
engine2d_cpu_metal_parity_status=fail
engine2d_cpu_metal_parity_reason=simple-bin-forbidden
engine2d_cpu_metal_parity_simple_bin=src/compiler_rust/target/release/simple
engine2d_cpu_metal_parity_simple_bin_source=explicit-env-rust-seed-forbidden
engine2d_cpu_metal_parity_simple_bin_status=forbidden
```

Normal non-macOS host evidence writes:

```text
engine2d_cpu_metal_parity_status=pass
engine2d_cpu_metal_parity_reason=not-macos-skipped
engine2d_cpu_metal_parity_simple_bin_status=pass
engine2d_cpu_metal_parity_verdict=skip reason=not-macos
```

Normal macOS host evidence must instead write:

```text
engine2d_cpu_metal_parity_status=pass
engine2d_cpu_metal_parity_reason=cpu-metal-bitexact
engine2d_cpu_metal_parity_simple_bin_status=pass
```

and include scene rows for clear, rects, gradient, line, circle, rounded rect,
and triangle parity.

## Scenario Checklist

1. The wrapper source must contain self-hosted candidates:
   - `bin/simple`
   - `release/*/simple`
   - `bin/release/*/simple`
   - `build/bootstrap/stage3/simple`
2. The wrapper must export `SIMPLE_BIN`, `SIMPLE_BIN_SOURCE`, and
   `SIMPLE_BIN_STATUS`.
3. Explicit Rust seed paths must set `SIMPLE_BIN_STATUS=forbidden`.
4. Missing Simple paths must set `SIMPLE_BIN_STATUS=missing`.
5. Early failures must still write `parity.env` and the markdown report.
6. Completed host-gated runs must keep the original parity verdict rows and add
   the Simple binary provenance rows.

## Traceability

- Goal: 2D Metal backend hardening without Rust seed fallback.
- Wrapper: `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`
- Guide: `doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md`

## Scenarios

### Engine2D CPU/Metal parity Simple binary contract

#### selects self hosted Simple and rejects Rust seed overrides

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-engine2d-cpu-metal-parity-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("build/bootstrap/stage3/simple")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("engine2d_cpu_metal_parity_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("engine2d_cpu_metal_parity_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("engine2d_cpu_metal_parity_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### records explicit Rust seed Simple binary as forbidden evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-engine2d-cpu-metal-parity-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/parity.env")
expect(evidence).to_contain("engine2d_cpu_metal_parity_status=fail")
expect(evidence).to_contain("engine2d_cpu_metal_parity_reason=simple-bin-forbidden")
expect(evidence).to_contain("engine2d_cpu_metal_parity_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("engine2d_cpu_metal_parity_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("engine2d_cpu_metal_parity_simple_bin_status=forbidden")
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

- **Plan:** [doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md](doc/07_guide/ui/engine2d_cpu_metal_bit_parity.md)


</details>
