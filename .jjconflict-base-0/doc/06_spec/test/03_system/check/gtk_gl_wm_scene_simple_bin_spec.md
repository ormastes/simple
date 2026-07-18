# GTK GL WM Scene Simple Binary Contract

> The GTK GL WM scene wrapper compares a pure Simple retained WM scene against a GTK GLArea capture. This contract prevents `src/compiler_rust/**` from being accepted as the Simple renderer used for that GUI/2D evidence.

<!-- sdn-diagram:id=gtk_gl_wm_scene_simple_bin_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=gtk_gl_wm_scene_simple_bin_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

gtk_gl_wm_scene_simple_bin_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=gtk_gl_wm_scene_simple_bin_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GTK GL WM Scene Simple Binary Contract

The GTK GL WM scene wrapper compares a pure Simple retained WM scene against a GTK GLArea capture. This contract prevents `src/compiler_rust/**` from being accepted as the Simple renderer used for that GUI/2D evidence.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | N/A |
| Plan | doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md |
| Design | doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md |
| Research | doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md |
| Source | `test/03_system/check/gtk_gl_wm_scene_simple_bin_spec.spl` |
| Updated | 2026-06-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The GTK GL WM scene wrapper compares a pure Simple retained WM scene against a
GTK GLArea capture. This contract prevents `src/compiler_rust/**` from being
accepted as the Simple renderer used for that GUI/2D evidence.

## Requirements

**Requirements:** N/A

- REQ-GTK-GL-WM-SCENE-BIN-001: Default Simple binary selection is self-hosted
  only.
- REQ-GTK-GL-WM-SCENE-BIN-002: Rust seed Simple paths produce
  `simple-bin-forbidden` evidence before GTK/OpenGL checks run.
- REQ-GTK-GL-WM-SCENE-BIN-003: Evidence records selected Simple binary,
  source, and status fields.

## Plan

**Plan:** doc/09_report/gui_renderdoc_feature_coverage_status_2026-06-27.md

1. Inspect the wrapper source for self-hosted candidate selection.
2. Inspect the wrapper source for Rust seed detection and exported provenance.
3. Run the wrapper with `SIMPLE_BIN=src/compiler_rust/target/release/simple`.
4. Confirm `evidence.env` reports `simple-bin-forbidden`.

## Design

**Design:** doc/04_architecture/compiler/graphics/accelerated_shared_ui_backend_architecture.md

The wrapper validates `SIMPLE_BIN` before pkg-config, GTK, compiler, Simple,
or OpenGL work so forbidden seed rejection is cheap and deterministic.

## Research

**Research:** doc/01_research/ui/render_path/gui_web_2d_path_assessment_2026-06-12.md

## Examples

```sh
SIMPLE_LIB=src bin/simple test test/03_system/check/gtk_gl_wm_scene_simple_bin_spec.spl --mode=interpreter --clean
```

## Scenarios

### GTK GL WM scene Simple binary contract

#### selects self hosted Simple and records launcher provenance

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val script = file_read("scripts/check/check-gtk-gl-wm-scene-bitmap-evidence.shs")
expect(script).to_contain("SIMPLE_BIN_SOURCE=")
expect(script).to_contain("SIMPLE_BIN_STATUS=pass")
expect(script).to_contain("\"release\"/*/simple")
expect(script).to_contain("\"bin/release\"/*/simple")
expect(script).to_contain("\"build/bootstrap/stage3/simple\"")
expect(script).to_contain("\"bin/simple\"")
expect(script).to_contain("is_rust_seed_simple")
expect(script).to_contain("SIMPLE_BIN_STATUS=forbidden")
expect(script).to_contain("export SIMPLE_BIN SIMPLE_BIN_SOURCE SIMPLE_BIN_STATUS")
expect(script).to_contain("gtk_gl_wm_scene_simple_bin=$SIMPLE_BIN")
expect(script).to_contain("gtk_gl_wm_scene_simple_bin_source=$SIMPLE_BIN_SOURCE")
expect(script).to_contain("gtk_gl_wm_scene_simple_bin_status=$SIMPLE_BIN_STATUS")
```

</details>

#### rejects explicit Rust seed before GTK GL evidence work

<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "build/test-gtk-gl-wm-scene-seed-forbidden"
val command = "rm -rf " + root + " && SIMPLE_BIN=src/compiler_rust/target/release/simple BUILD_DIR=" + root + "/out REPORT_PATH=" + root + "/report.md sh scripts/check/check-gtk-gl-wm-scene-bitmap-evidence.shs > " + root + "/stdout.txt 2> " + root + "/stderr.txt || true"
val (_stdout, _stderr, code) = process_run("/bin/sh", ["-c", command])
expect(code).to_equal(0)

val evidence = file_read(root + "/out/evidence.env")
expect(evidence).to_contain("gtk_gl_wm_scene_status=unavailable")
expect(evidence).to_contain("gtk_gl_wm_scene_reason=simple-bin-forbidden")
expect(evidence).to_contain("gtk_gl_wm_scene_simple_bin=src/compiler_rust/target/release/simple")
expect(evidence).to_contain("gtk_gl_wm_scene_simple_bin_source=explicit-env-rust-seed-forbidden")
expect(evidence).to_contain("gtk_gl_wm_scene_simple_bin_status=forbidden")

val (_simple_out, _simple_err, simple_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/simple.out"])
expect(simple_code).to_equal(0)
val (_gtk_out, _gtk_err, gtk_code) = process_run("/bin/sh", ["-c", "test ! -f " + root + "/out/gtk.out"])
expect(gtk_code).to_equal(0)
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
