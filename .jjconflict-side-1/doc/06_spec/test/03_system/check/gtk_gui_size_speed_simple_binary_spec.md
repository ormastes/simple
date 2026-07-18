# GTK GUI Size/Speed Simple Binary Contract

> The GTK size/speed baseline is part of GUI performance evidence. It must not silently use `src/compiler_rust/**` when collecting Simple renderer timings or native-size artifacts.

<!-- sdn-diagram:id=gtk_gui_size_speed_simple_binary_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gtk_gui_size_speed_simple_binary_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gtk_gui_size_speed_simple_binary_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gtk_gui_size_speed_simple_binary_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GTK GUI Size/Speed Simple Binary Contract

The GTK size/speed baseline is part of GUI performance evidence. It must not silently use `src/compiler_rust/**` when collecting Simple renderer timings or native-size artifacts.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The GTK size/speed baseline is part of GUI performance evidence. It must not
silently use `src/compiler_rust/**` when collecting Simple renderer timings or
native-size artifacts.

## Requirements

**Requirements:** N/A

- REQ-GTK-GUI-PERF-BIN-001: Default Simple binary selection is self-hosted only.
- REQ-GTK-GUI-PERF-BIN-002: Rust seed Simple paths produce
  `simple-binary-forbidden` evidence before render/native/GTK probes run.
- REQ-GTK-GUI-PERF-BIN-003: Evidence records selected Simple binary, source,
  and status fields.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BINARY=src/compiler_rust/target/release/simple`.
4. Confirm stdout and report record `simple-binary-forbidden`.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BINARY` before running Simple rendering, native
builds, or GTK C probes so forbidden seed rejection is cheap and deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gtk_gui_size_speed_simple_binary_spec.spl --mode=interpreter --clean
```

## Scenarios

### GTK GUI size/speed Simple binary contract

#### selects self hosted Simple and records launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gtk-gui-size-speed-baseline.shs")
expect(script).to_contain("SIMPLE_BINARY_SOURCE=")
expect(script).to_contain("SIMPLE_BINARY_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple_binary")
expect(script).to_contain("SIMPLE_BINARY_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BINARY SIMPLE_BINARY_SOURCE SIMPLE_BINARY_STATUS")
expect(script).to_contain("simple_binary=$SIMPLE_BINARY")
expect(script).to_contain("simple_binary_source=$SIMPLE_BINARY_SOURCE")
expect(script).to_contain("simple_binary_status=$SIMPLE_BINARY_STATUS")
```

</details>

#### rejects explicit Rust seed before running GUI perf probes

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gtk-gui-size-speed-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BINARY=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gtk-gui-size-speed-baseline.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val output = file_read(root + "/stdout.txt")
expect(output).to_contain("gtk_benchmark_evidence_status=unavailable")
expect(output).to_contain("gtk_benchmark_evidence_reason=simple-binary-forbidden")
expect(output).to_contain("simple_binary=src/compiler_rust/target/release/simple")
expect(output).to_contain("simple_binary_source=explicit-env-rust-seed-forbidden")
expect(output).to_contain("simple_binary_status=forbidden")

val report = file_read(root + "/report.md")
expect(report).to_contain("| reason | simple-binary-forbidden |")
val (_test_out, _test_err, no_probe_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/simple_gui_render_bench.trial_1.out"])
expect(no_probe_code).to_equal(0)
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
