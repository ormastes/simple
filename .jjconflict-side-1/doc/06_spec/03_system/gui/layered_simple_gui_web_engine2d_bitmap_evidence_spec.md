# Layered Simple GUI / WebRenderer / Engine2D Bitmap Evidence Spec

> Runs the layered bitmap evidence wrapper with minimal iterations and verifies

<!-- sdn-diagram:id=layered_simple_gui_web_engine2d_bitmap_evidence_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=layered_simple_gui_web_engine2d_bitmap_evidence_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

layered_simple_gui_web_engine2d_bitmap_evidence_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=layered_simple_gui_web_engine2d_bitmap_evidence_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Layered Simple GUI / WebRenderer / Engine2D Bitmap Evidence Spec

Runs the layered bitmap evidence wrapper with minimal iterations and verifies

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/layered_simple_gui_web_engine2d_bitmap_evidence_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Runs the layered bitmap evidence wrapper with minimal iterations and verifies
that both representative scenes pass exact-bitmap, no-blur/no-tolerance checks
through the Node, Bun, and Electron GUI layers.

## Scenarios

### Layered Simple GUI Web Engine2D bitmap evidence

<details>
<summary>Advanced: passes exact bitmap checks through Node, Bun, and Electron layers</summary>

#### passes exact bitmap checks through Node, Bun, and Electron layers _(slow)_

1.  expect exact layer
2.  expect exact layer
3.  expect exact layer
4.  expect exact layer
5.  expect exact layer
6.  expect exact layer


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val run_id = _run_id()
val result = _run_evidence(run_id)
val stdout = result[0]
val stderr = result[1]
val code = result[2]
if code != 0:
    print "layered bitmap evidence stdout: " + stdout
    print "layered bitmap evidence stderr: " + stderr
expect(code).to_equal(0)
expect(stdout).to_contain("layered_simple_gui_web_engine2d_status=pass")
expect(stdout).to_contain("layered_simple_gui_web_engine2d_reason=pass")
expect(stdout).to_contain("layered_simple_gui_web_engine2d_policy=exact-bitmap-no-blur-no-tolerance")
expect(stdout).to_contain("layered_simple_gui_web_engine2d_layers=web-renderer-engine2d-node,web-renderer-engine2d-bun,simple-gui-web-renderer-electron")
expect(stdout).to_contain("layered_simple_gui_web_engine2d_scenes=image_taskbar_command,toolbar_modal_grid")

_expect_exact_layer(stdout, "image_taskbar_command", "node")
_expect_exact_layer(stdout, "image_taskbar_command", "bun")
_expect_exact_layer(stdout, "toolbar_modal_grid", "node")
_expect_exact_layer(stdout, "toolbar_modal_grid", "bun")
_expect_exact_layer(stdout, "image_taskbar_command", "electron_gui")
_expect_exact_layer(stdout, "toolbar_modal_grid", "electron_gui")
expect(stdout).to_contain("layered_image_taskbar_command_electron_gui_captured_argb_written=true")
expect(stdout).to_contain("layered_toolbar_modal_grid_electron_gui_captured_argb_written=true")
expect(stdout).to_contain("layered_image_taskbar_command_electron_gui_captured_argb_bytes=")
expect(stdout).to_contain("layered_image_taskbar_command_electron_gui_captured_argb_cksum=")
expect(stdout).to_contain("layered_toolbar_modal_grid_electron_gui_captured_argb_bytes=")
expect(stdout).to_contain("layered_toolbar_modal_grid_electron_gui_captured_argb_cksum=")

val report = rt_file_read_text(_report_path(run_id))
expect(report).to_contain("# Layered Simple GUI / WebRenderer / Engine2D Bitmap Evidence")
expect(report).to_contain("- status: pass")
expect(report).to_contain("- policy: exact bitmap, no blur, no tolerance")
expect(report).to_contain("- scenes: image_taskbar_command, toolbar_modal_grid")
expect(report).to_contain("layered_image_taskbar_command_electron_gui_captured_argb_bytes=")
expect(report).to_contain("layered_image_taskbar_command_electron_gui_captured_argb_cksum=")
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 1 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
