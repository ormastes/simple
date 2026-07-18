# modern_shell_contract_spec

> Verifies that the OS-facing dock/taskbar layer exposes the same modern

<!-- sdn-diagram:id=modern_shell_contract_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=modern_shell_contract_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

modern_shell_contract_spec -> std
modern_shell_contract_spec -> os
modern_shell_contract_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=modern_shell_contract_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# modern_shell_contract_spec

Verifies that the OS-facing dock/taskbar layer exposes the same modern

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/desktop/modern_shell_contract_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that the OS-facing dock/taskbar layer exposes the same modern
    rounded translucent shell metrics that the Web WM and compositor scene use.

## Scenarios

### SimpleOS modern shell contract

#### defines rounded translucent dock metrics with bounded motion controls

- assert true
- assert true
- assert true
   - Expected: metrics.icon_size_px equals `48`
   - Expected: metrics.height_px equals `64`
   - Expected: metrics.corner_radius_px equals `32`
   - Expected: metrics.icon_radius_px equals `999`
   - Expected: metrics.blur_radius_px equals `24`
   - Expected: metrics.hover_lift_px equals `3`
   - Expected: metrics.motion_ms equals `180`
   - Expected: metrics.reduced_motion_ms equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val metrics = modern_dock_metrics()
assert_true(metrics.translucent)
assert_true(metrics.round_icon_converter)
assert_true(metrics.motion_can_disable)
expect(metrics.icon_size_px).to_equal(48)
expect(metrics.height_px).to_equal(64)
expect(metrics.corner_radius_px).to_equal(32)
expect(metrics.icon_radius_px).to_equal(999)
expect(metrics.blur_radius_px).to_equal(24)
expect(metrics.hover_lift_px).to_equal(3)
expect(metrics.motion_ms).to_equal(180)
expect(metrics.reduced_motion_ms).to_equal(80)
val summary = modern_dock_summary(7)
expect(summary).to_contain("modern_dock")
expect(summary).to_contain("items=7")
expect(summary).to_contain("round_icon_converter=true")
expect(summary).to_contain("motion_can_disable=true")
```

</details>

#### uses modern dock metrics for created dock geometry

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dock = Dock.create(Px(value: 1024), Px(value: 768))
val metrics = modern_dock_metrics()
val expected_width = 7 * metrics.icon_size_px + 6 * metrics.item_spacing_px + metrics.padding_px * 2
expect(dock.width.value).to_equal(expected_width)
expect(dock.height.value).to_equal(metrics.height_px)
expect(dock.x.value).to_equal((1024 - expected_width) / 2)
expect(dock.y.value).to_equal(768 - metrics.height_px - 8)
```

</details>

#### classifies square image icons for round conversion and glyph icons separately

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val image = DockItem(app_name: "Browser", icon_char: "https://simple.local/icon.png", is_pinned: true, is_running: false, window_id: nil)
val glyph = DockItem(app_name: "Terminal", icon_char: ">", is_pinned: true, is_running: false, window_id: nil)
expect(dock_item_modern_icon_kind(image)).to_equal("square-to-round")
expect(dock_item_modern_icon_kind(glyph)).to_equal("glyph-to-round")
```

</details>

#### defines rounded translucent taskbar metrics and summarizes model counts

- assert true
- assert true
- assert true
- assert true
   - Expected: contract.height_px equals `48`
   - Expected: contract.icon_size_px equals `26`
   - Expected: contract.corner_radius_px equals `999`
   - Expected: contract.blur_radius_px equals `24`
   - Expected: contract.hover_lift_px equals `3`
   - Expected: contract.motion_ms equals `150`
   - Expected: contract.reduced_motion_ms equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = modern_taskbar_shell_contract()
assert_true(contract.translucent)
assert_true(contract.rounded_taskbar)
assert_true(contract.rounded_icons)
assert_true(contract.motion_can_disable)
expect(contract.height_px).to_equal(48)
expect(contract.icon_size_px).to_equal(26)
expect(contract.corner_radius_px).to_equal(999)
expect(contract.blur_radius_px).to_equal(24)
expect(contract.hover_lift_px).to_equal(3)
expect(contract.motion_ms).to_equal(150)
expect(contract.reduced_motion_ms).to_equal(80)
val summary = modern_taskbar_shell_summary(_taskbar_model())
expect(summary).to_contain("modern_taskbar")
expect(summary).to_contain("pinned=2")
expect(summary).to_contain("running=2")
expect(summary).to_contain("tray=1")
expect(summary).to_contain("rounded_taskbar=true")
expect(summary).to_contain("rounded_icons=true")
```

</details>

#### writes modern taskbar metadata onto the actual widget tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = build_taskbar_shell_tree(_taskbar_model())
expect(root.get_prop("modern_shell")).to_equal("true")
expect(root.get_prop("modern_taskbar_height_px")).to_equal("48")
expect(root.get_prop("modern_taskbar_radius_px")).to_equal("999")
expect(root.get_prop("modern_taskbar_blur_px")).to_equal("24")
expect(root.get_prop("modern_motion_can_disable")).to_equal("true")
expect(root.get_prop("modern_translucent")).to_equal("true")
val sections = root.children()
expect(sections.len()).to_equal(3)
expect(sections[0].get_prop("modern_shell_section")).to_equal("pinned")
val pinned = sections[0].children()
expect(pinned.len()).to_equal(2)
expect(pinned[0].get_prop("modern_shell_role")).to_equal("pinned_launcher")
expect(pinned[0].get_prop("modern_icon_kind")).to_equal("glyph-to-round")
expect(pinned[1].get_prop("modern_icon_kind")).to_equal("square-to-round")
val running = sections[1].children()
expect(running[1].get_prop("modern_minimized")).to_equal("true")
```

</details>

#### defines portable modern desktop affordances for SimpleOS renderers

- assert true
- assert true
- assert true
- assert true
- assert true
- assert true
- assert true
- assert true
- assert true
   - Expected: contract.reduced_motion_ms equals `80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val contract = modern_desktop_affordance_contract()
assert_true(contract.command_palette)
assert_true(contract.control_center)
assert_true(contract.window_overview)
assert_true(contract.desktop_widgets)
assert_true(contract.snap_assist)
assert_true(contract.motion_verbosity_controls)
assert_true(contract.can_disable_motion)
assert_true(contract.translucent_panels)
assert_true(contract.rounded_controls)
expect(contract.reduced_motion_ms).to_equal(80)
val summary = modern_desktop_affordance_summary()
expect(summary).to_contain("modern_desktop_affordances")
expect(summary).to_contain("control_center=true")
expect(summary).to_contain("window_overview=true")
expect(summary).to_contain("desktop_widgets=true")
expect(summary).to_contain("snap_assist=true")
expect(summary).to_contain("motion_controls=true")
```

</details>

#### writes modern affordance metadata onto the actual taskbar shell tree

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = build_taskbar_shell_tree(_taskbar_model())
expect(root.get_prop("modern_command_palette")).to_equal("true")
expect(root.get_prop("modern_control_center")).to_equal("true")
expect(root.get_prop("modern_window_overview")).to_equal("true")
expect(root.get_prop("modern_desktop_widgets")).to_equal("true")
expect(root.get_prop("modern_snap_assist")).to_equal("true")
expect(root.get_prop("modern_motion_controls")).to_equal("true")
expect(root.get_prop("modern_affordance_reduced_motion_ms")).to_equal("80")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
