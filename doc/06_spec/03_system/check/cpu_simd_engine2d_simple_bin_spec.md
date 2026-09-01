# CPU SIMD Engine2D Simple Binary Contract

> The CPU SIMD Engine2D wrapper needs a Simple binary that contains the Engine2D SIMD extern names. This contract keeps automatic evidence on self-hosted/release Simple binaries; if no capable self-hosted binary exists, the wrapper skips instead of falling back to `src/compiler_rust/**`.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CPU SIMD Engine2D Simple Binary Contract

The CPU SIMD Engine2D wrapper needs a Simple binary that contains the Engine2D SIMD extern names. This contract keeps automatic evidence on self-hosted/release Simple binaries; if no capable self-hosted binary exists, the wrapper skips instead of falling back to `src/compiler_rust/**`.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/cpu_simd_engine2d_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The CPU SIMD Engine2D wrapper needs a Simple binary that contains the
Engine2D SIMD extern names. This contract keeps automatic evidence on
self-hosted/release Simple binaries; if no capable self-hosted binary exists,
the wrapper skips instead of falling back to `src/compiler_rust/**`.

## Requirements

**Requirements:** N/A

- REQ-CPU-SIMD-ENGINE2D-BIN-001: Automatic Simple binary selection is
  self-hosted only.
- REQ-CPU-SIMD-ENGINE2D-BIN-002: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence before canonical Engine2D evidence is copied.
- REQ-CPU-SIMD-ENGINE2D-BIN-003: Evidence records selected Simple binary,
  source, and status fields.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Confirm `evidence.env` reports `simple-bin-forbidden`.
5. Confirm the canonical evidence source was not copied for the forbidden path.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before copying the canonical evidence
`.spl`, so forbidden seed rejection is cheap and deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/cpu_simd_engine2d_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### CPU SIMD Engine2D Simple binary contract

#### auto selects only self hosted Simple launchers

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-cpu-simd-engine2d-evidence.shs")
val evidence_src = file_read("scripts/build/cpu-simd-engine2d-evidence/cpu_simd_engine2d_evidence.spl")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("repo-self-hosted-engine2d-simd")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("binary_identifies_as_bootstrap_seed")
expect(script).to_contain("bootstrap seed only")
expect(script).to_contain("binary_runs_engine2d_simd_smoke")
expect(script).to_contain("engine2d_simd_candidate_smoke.spl")
expect(script).to_contain("engine2d_simd_fill_row_u32(4, 0xFF010203u32)")
expect(script).to_contain("engine2d_simd_copy_row_u32([0xFF000001u32")
expect(script).to_contain("engine2d_simd_blend_row_u32([0xFF102030u32")
expect(script).to_contain("blend[0] != 0xFF102030u32")
expect(script).to_contain("blend[1] != 0xFFFFFFFFu32")
expect(script).to_contain("binary_has_runnable_engine2d_simd_externs")
expect(script).to_contain("if [ \"$SIMPLE_BIN_PINNED\" = \"0\" ]; then")
expect(script.contains("|| [ \"$SIMPLE_BIN\" = \"bin/simple\" ]")).to_equal(false)
expect(script).to_contain("\"$SIMPLE_BIN_PINNED\" = \"1\"")
expect(script).to_contain("! binary_runs_engine2d_simd_smoke \"$SIMPLE_BIN\"")
expect(script).to_contain("SIMPLE_BIN_STATUS=incompatible")
expect(script).to_contain("REASON=\"simple-bin-simd-smoke-failed\"")
expect(script).to_contain("rt_engine2d_simd_fill_row_u32")
expect(script).to_contain("rt_engine2d_simd_copy_row_u32")
expect(script).to_contain("rt_engine2d_simd_blend_row_u32")
expect(script.contains("rt_engine2d_simd_fill_u32'")).to_equal(false)
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("cpu_simd_evidence_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("cpu_simd_evidence_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("cpu_simd_evidence_simple_bin_status=$SIMPLE_BIN_STATUS")
val no_seed_candidate = not script.contains("target/debug/simple\"") and not script.contains("target/release/simple\"")
expect(no_seed_candidate).to_be(true)
```

</details>

#### rejects explicit Rust seed before copying canonical Engine2D evidence

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-cpu-simd-engine2d-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-cpu-simd-engine2d-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("cpu_simd_evidence_status=fail")
expect(evidence).to_contain("cpu_simd_evidence_reason=simple-bin-forbidden")
expect(evidence).to_contain("cpu_simd_evidence_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("cpu_simd_evidence_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("cpu_simd_evidence_simple_bin_status=forbidden")

val (_src_out, _src_err, src_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/cpu_simd_engine2d_evidence.spl"])
expect(src_code).to_equal(0)
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

- **Plan:** `doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md`
- **Design:** `doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md`
- **Research:** `doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md`


</details>
