# widget_draw_ir_theme_spec

> Purpose: Prove that widget Draw IR semantic theme handoff.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# widget_draw_ir_theme_spec

Purpose: Prove that widget Draw IR semantic theme handoff.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that widget Draw IR semantic theme handoff.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### widget Draw IR semantic theme handoff

#### projects the selected snapshot surface and accent into the same widget tree

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- projects the selected snapshot surface and accent into the same widget tree
- Verify: projects the selected snapshot surface and accent into the same widget tree
   - Expected: _command_color(first_draw, "theme-panel") equals `first.material.window_fill_rgba`
   - Expected: _command_color(second_draw, "theme-panel") equals `second.material.window_fill_rgba`
   - Expected: _command_color(first_draw, "theme-button") equals `first.accent_rgba`
   - Expected: _command_color(second_draw, "theme-button") equals `second.accent_rgba`
   - Expected: _command_color(first_draw, "theme-button") != _command_color(second_draw, "theme-button") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects the selected snapshot surface and accent into the same widget tree")
step("Verify: projects the selected snapshot surface and accent into the same widget tree")
# @req: REQ-LIB-COMMON-001
val root = panel("theme-panel", "", [button("theme-button", "", "activate")])
val first = _theme_snapshot("first", 0xff010203u32, 0xfff0f1f2u32, 0xff123456u32, 0xff202122u32, 0xff303132u32, 0xff404142u32, 0xff505152u32)
val second = _theme_snapshot("second", 0xff111213u32, 0xffe0e1e2u32, 0xffabcdefu32, 0xff606162u32, 0xff707172u32, 0xff808182u32, 0xff909192u32)

val first_draw = widget_tree_to_draw_ir_with_theme(root, 160, 80, DRAW_IR_BACKEND_CPU, first)
val second_draw = widget_tree_to_draw_ir_with_theme(root, 160, 80, DRAW_IR_BACKEND_CPU, second)

expect(_command_color(first_draw, "theme-panel")).to_equal(first.material.window_fill_rgba)
expect(_command_color(second_draw, "theme-panel")).to_equal(second.material.window_fill_rgba)
expect(_command_color(first_draw, "theme-button")).to_equal(first.accent_rgba)
expect(_command_color(second_draw, "theme-button")).to_equal(second.accent_rgba)
expect(_command_color(first_draw, "theme-button") != _command_color(second_draw, "theme-button")).to_equal(true)
```

</details>

#### uses existing hover and pressed widget state as semantic theme roles

- uses existing hover and pressed widget state as semantic theme roles
- Verify: uses existing hover and pressed widget state as semantic theme roles
   - Expected: _command_color(draw, "hover-button") equals `snapshot.material.active_title_fill_rgba`
   - Expected: _command_color(draw, "pressed-button") equals `snapshot.material.inactive_title_fill_rgba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses existing hover and pressed widget state as semantic theme roles")
step("Verify: uses existing hover and pressed widget state as semantic theme roles")
val snapshot = _theme_snapshot("states", 0xff010203u32, 0xfff0f1f2u32, 0xff123456u32, 0xff202122u32, 0xff303132u32, 0xff404142u32, 0xff505152u32)
val hovered = button("hover-button", "", "activate").set_prop("ui_hover", "true")
val pressed = button("pressed-button", "", "activate").set_prop("ui_pressed", "true")
val root = panel("state-panel", "", [hovered, pressed])

val draw = widget_tree_to_draw_ir_with_theme(root, 160, 100, DRAW_IR_BACKEND_CPU, snapshot)

expect(_command_color(draw, "hover-button")).to_equal(snapshot.material.active_title_fill_rgba)
expect(_command_color(draw, "pressed-button")).to_equal(snapshot.material.inactive_title_fill_rgba)
```

</details>

#### projects Aetheric status chip roles and label text through Draw IR

- projects Aetheric status chip roles and label text through Draw IR
- Verify: projects Aetheric status chip roles and label text through Draw IR
   - Expected: _command_color(draw, "error-chip") equals `theme_role_color(snapshot, "semantic.error").rgba`
   - Expected: _command_color(draw, "error-chip") != snapshot.material.window_fill_rgba is true
   - Expected: _command_text(draw, "error-chip-label") equals `Failed`
   - Expected: _command_color(draw, "success-chip") equals `theme_role_color(snapshot, "semantic.success").rgba`
   - Expected: _command_color(draw, "warning-chip") equals `theme_role_color(snapshot, "semantic.warning").rgba`
   - Expected: _command_color(draw, "default-chip") equals `theme_role_color(snapshot, "workbench.panel").rgba`
   - Expected: _command_color(draw, "unknown-chip") equals `theme_role_color(snapshot, "workbench.panel").rgba`
   - Expected: _command_color(draw, "info-toast") equals `theme_role_color(snapshot, "semantic.info").rgba`
   - Expected: _command_text(draw, "info-toast-label") equals `Informational message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 42 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("projects Aetheric status chip roles and label text through Draw IR")
step("Verify: projects Aetheric status chip roles and label text through Draw IR")
val snapshot = theme_package_render_snapshot("aetheric_dark")
var error_chip = WidgetNode.new("error-chip", "status_chip")
error_chip = error_chip.set_prop("label", "Failed")
error_chip = error_chip.set_prop("status", "error")
var success_chip = WidgetNode.new("success-chip", "status_chip")
success_chip = success_chip.set_prop("label", "Saved")
success_chip = success_chip.set_prop("status", "success")
var warning_chip = WidgetNode.new("warning-chip", "status_chip")
warning_chip = warning_chip.set_prop("label", "Caution")
warning_chip = warning_chip.set_prop("status", "warning")
var default_chip = WidgetNode.new("default-chip", "status_chip")
default_chip = default_chip.set_prop("label", "Neutral")
var unknown_chip = WidgetNode.new("unknown-chip", "status_chip")
unknown_chip = unknown_chip.set_prop("label", "Unknown")
unknown_chip = unknown_chip.set_prop("status", "other")
var info_toast = WidgetNode.new("info-toast", "toast")
info_toast = info_toast.set_prop("label", "Ignored label")
info_toast = info_toast.set_prop("message", "Informational message")
info_toast = info_toast.set_prop("status", "info")
val root = panel("status-panel", "", [
    error_chip,
    success_chip,
    warning_chip,
    default_chip,
    unknown_chip,
    info_toast
])

val draw = widget_tree_to_draw_ir_with_theme(root, 240, 240, DRAW_IR_BACKEND_CPU, snapshot)

expect(_command_color(draw, "error-chip")).to_equal(theme_role_color(snapshot, "semantic.error").rgba)
expect(_command_color(draw, "error-chip") != snapshot.material.window_fill_rgba).to_equal(true)
expect(_command_text(draw, "error-chip-label")).to_equal("Failed")
expect(_command_color(draw, "success-chip")).to_equal(theme_role_color(snapshot, "semantic.success").rgba)
expect(_command_color(draw, "warning-chip")).to_equal(theme_role_color(snapshot, "semantic.warning").rgba)
expect(_command_color(draw, "default-chip")).to_equal(theme_role_color(snapshot, "workbench.panel").rgba)
expect(_command_color(draw, "unknown-chip")).to_equal(theme_role_color(snapshot, "workbench.panel").rgba)
expect(_command_color(draw, "info-toast")).to_equal(theme_role_color(snapshot, "semantic.info").rgba)
expect(_command_text(draw, "info-toast-label")).to_equal("Informational message")
```

</details>

#### carries Aetheric glass material from GUI snapshot into canonical Draw IR

- carries Aetheric glass material from GUI snapshot into canonical Draw IR
- Verify: carries Aetheric glass material from GUI snapshot into canonical Draw IR
   - Expected: _material_request_count(draw) equals `1`
   - Expected: initializer.component_id equals `glass-root-surface-initializer`
   - Expected: initializer.x equals `0`
   - Expected: initializer.y equals `0`
   - Expected: initializer.width equals `240`
   - Expected: initializer.height equals `160`
   - Expected: initializer.color equals `theme_draw_ir_surface_initializer_color(snapshot)`
   - Expected: initializer.computed_style.len() equals `0`
   - Expected: _command_style(draw, "glass-root", "wm-theme-id") equals `snapshot.id`
   - Expected: _command_style(draw, "glass-root", "wm-theme-family-id") equals `snapshot.family_id`
   - Expected: _command_style(draw, "glass-root", "wm-theme-source-manifest-sha256") equals `snapshot.source_manifest_sha256`
   - Expected: _command_style(draw, "glass-root", "wm-theme-material-sha256") equals `snapshot.material_sha256`
   - Expected: _command_style(draw, "glass-root", "background-color") equals `snapshot.material.window_fill_rgba.to_string()`
   - Expected: _command_style(draw, "glass-root", "border-radius") equals `snapshot.material.corner_radius_px.to_string()`
   - Expected: _command_style(draw, "glass-root", "border-top-width") equals `snapshot.material.border_width_px.to_string()`
   - Expected: _command_style(draw, "glass-root", "border-top-color") equals `snapshot.material.border_rgba.to_string()`
   - Expected: _command_style(draw, "glass-root", "box-shadow-layer-count") equals `snapshot.material.active_shadows.len().to_string()`
   - Expected: _command_style(draw, "glass-root", "backdrop-filter-capability") equals `engine2d-cpu-composited-material-v1`
   - Expected: _command_style(draw, "glass-root", "backdrop-filter-requested-target") equals `cpu-scalar-glass-v1`
   - Expected: _command_color(draw, "glass-button") equals `snapshot.accent_rgba`
   - Expected: _command_style_count(draw, "glass-button") equals `0`
   - Expected: _command_style_count(draw, "glass-input") equals `0`
   - Expected: _command_style_count(draw, "glass-input-field") equals `0`
   - Expected: _command_style_count(draw, "nested-panel") equals `0`
   - Expected: _command_style_count(draw, "scroll-child") equals `0`
   - Expected: command.hit_rect.present is false
   - Expected: command.clip_rect.present is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 51 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("carries Aetheric glass material from GUI snapshot into canonical Draw IR")
step("Verify: carries Aetheric glass material from GUI snapshot into canonical Draw IR")
val snapshot = theme_package_render_snapshot("aetheric_dark")
var scroll = WidgetNode.new("nested-scroll", "scroll")
scroll = scroll.add_child(button("scroll-child", "Inner", "inner"))
val root = panel("glass-root", "", [
    panel("nested-panel", "", [button("glass-button", "Save", "save")]),
    text_field("glass-input", "theme", "Theme"),
    scroll
])
val draw = widget_tree_to_draw_ir_with_theme(root, 240, 160, DRAW_IR_BACKEND_CPU, snapshot)
val initializer = draw.batches[0].commands[0]

expect(_material_request_count(draw)).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(initializer.component_id).to_equal("glass-root-surface-initializer")
expect(initializer.x).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(initializer.y).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(initializer.width).to_equal(240)  # oracle: 240 — named expected value from the requirement
expect(initializer.height).to_equal(160)  # oracle: 160 — named expected value from the requirement
expect(initializer.color).to_equal(theme_draw_ir_surface_initializer_color(snapshot))
expect(initializer.computed_style.len()).to_equal(0)  # oracle: 0 — named expected value from the requirement

expect(_command_color(draw, "glass-root")).to_equal(
    theme_draw_ir_surface_command_color(
        snapshot, true, "body", DRAW_IR_BACKEND_CPU
    )
)
expect(_command_style(draw, "glass-root", "wm-theme-id")).to_equal(snapshot.id)
expect(_command_style(draw, "glass-root", "wm-theme-family-id")).to_equal(snapshot.family_id)
expect(_command_style(draw, "glass-root", "wm-theme-source-manifest-sha256")).to_equal(snapshot.source_manifest_sha256)
expect(_command_style(draw, "glass-root", "wm-theme-material-sha256")).to_equal(snapshot.material_sha256)
expect(_command_style(draw, "glass-root", "background-color")).to_equal(snapshot.material.window_fill_rgba.to_string())
expect(_command_style(draw, "glass-root", "border-radius")).to_equal(snapshot.material.corner_radius_px.to_string())
expect(_command_style(draw, "glass-root", "border-top-width")).to_equal(snapshot.material.border_width_px.to_string())
expect(_command_style(draw, "glass-root", "border-top-color")).to_equal(snapshot.material.border_rgba.to_string())
expect(_command_style(draw, "glass-root", "box-shadow-layer-count")).to_equal(snapshot.material.active_shadows.len().to_string())
expect(_command_style(draw, "glass-root", "backdrop-filter-capability")).to_equal("engine2d-cpu-composited-material-v1")
expect(_command_style(draw, "glass-root", "backdrop-filter-requested-target")).to_equal("cpu-scalar-glass-v1")

expect(_command_color(draw, "glass-button")).to_equal(snapshot.accent_rgba)
expect(_command_style_count(draw, "glass-button")).to_equal(0)
expect(_command_style_count(draw, "glass-input")).to_equal(0)
expect(_command_style_count(draw, "glass-input-field")).to_equal(0)
expect(_command_style_count(draw, "nested-panel")).to_equal(0)
expect(_command_style_count(draw, "scroll-child")).to_equal(0)
for batch in draw.batches:
    for command in batch.commands:
        if command.component_id == "scroll-child":
            expect(command.hit_rect.present).to_equal(false)
            expect(command.clip_rect.present).to_equal(false)
```

</details>

#### keeps unsupported GUI backend on explicit opaque solid fallback

- keeps unsupported GUI backend on explicit opaque solid fallback
- Verify: keeps unsupported GUI backend on explicit opaque solid fallback
   - Expected: _command_style(draw, "fallback-root", "backdrop-filter-capability") equals `unavailable`
   - Expected: _command_style(draw, "fallback-root", "backdrop-filter-requested-target") equals `solid-material`
   - Expected: _command_style(draw, "fallback-root", "backdrop-filter-fallback") equals `solid-material`
   - Expected: _command_style_count(draw, "fallback-button") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps unsupported GUI backend on explicit opaque solid fallback")
step("Verify: keeps unsupported GUI backend on explicit opaque solid fallback")
val snapshot = theme_package_render_snapshot("aetheric_dark")
val root = panel("fallback-root", "", [button("fallback-button", "Save", "save")])
val draw = widget_tree_to_draw_ir_with_theme(root, 180, 100, "auto", snapshot)

expect(_command_color(draw, "fallback-root")).to_equal(
    theme_draw_ir_surface_command_color(snapshot, true, "body", "auto")
)
expect(_command_style(draw, "fallback-root", "background-color")).to_equal(
    theme_draw_ir_surface_command_color(
        snapshot, true, "body", "auto"
    ).to_string()
)
expect(_command_style(draw, "fallback-root", "backdrop-filter-capability")).to_equal("unavailable")
expect(_command_style(draw, "fallback-root", "backdrop-filter-requested-target")).to_equal("solid-material")
expect(_command_style(draw, "fallback-root", "backdrop-filter-fallback")).to_equal("solid-material")
expect(_command_style_count(draw, "fallback-button")).to_equal(0)
```

</details>

#### maps concrete GUI backends to material policy without claiming a device receipt

- maps concrete GUI backends to material policy without claiming a device receipt
- Verify: maps concrete GUI backends to material policy without claiming a device receipt
   - Expected: _command_style(draw, "matrix-root", "backdrop-filter-capability") equals `engine2d-cpu-composited-material-v1`
   - Expected: _command_style(draw, "matrix-root", "backdrop-filter-requested-target") equals `cpu-scalar-glass-v1`
   - Expected: _command_style(metal, "matrix-root", "backdrop-filter-capability") equals `engine2d-composited-glass-material-v1`
   - Expected: _command_style(metal, "matrix-root", "backdrop-filter-requested-target") equals `metal-device-glass-v1`
   - Expected: _command_style(draw, "matrix-root", "backdrop-filter-capability") equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("maps concrete GUI backends to material policy without claiming a device receipt")
step("Verify: maps concrete GUI backends to material policy without claiming a device receipt")
val snapshot = theme_package_render_snapshot("aetheric_dark")
val root = panel("matrix-root", "", [])
for backend in ["cpu", "software", "cpu_simd", "vulkan"]:
    val draw = widget_tree_to_draw_ir_with_theme(root, 80, 60, backend, snapshot)
    expect(_command_style(draw, "matrix-root", "backdrop-filter-capability")).to_equal("engine2d-cpu-composited-material-v1")
    expect(_command_style(draw, "matrix-root", "backdrop-filter-requested-target")).to_equal("cpu-scalar-glass-v1")
val metal = widget_tree_to_draw_ir_with_theme(root, 80, 60, "metal", snapshot)
expect(_command_style(metal, "matrix-root", "backdrop-filter-capability")).to_equal("engine2d-composited-glass-material-v1")
expect(_command_style(metal, "matrix-root", "backdrop-filter-requested-target")).to_equal("metal-device-glass-v1")
for backend in ["auto", "gpu", "unknown"]:
    val draw = widget_tree_to_draw_ir_with_theme(root, 80, 60, backend, snapshot)
    expect(_command_style(draw, "matrix-root", "backdrop-filter-capability")).to_equal("unavailable")
    expect(_command_style(draw, "matrix-root", "background-color")).to_equal(
        theme_draw_ir_surface_command_color(
            snapshot, true, "body", backend
        ).to_string()
    )
```

</details>

#### preserves a non-surface root's semantic rectangle

- preserves a non-surface root's semantic rectangle
- Verify: preserves a non-surface root's semantic rectangle
   - Expected: _material_request_count(draw) equals `0`
   - Expected: draw.batches[0].commands[1].component_id equals `root-button`
   - Expected: _command_color(draw, "root-button") equals `snapshot.accent_rgba`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("preserves a non-surface root's semantic rectangle")
step("Verify: preserves a non-surface root's semantic rectangle")
val snapshot = theme_package_render_snapshot("aetheric_dark")
val root = button("root-button", "Save", "save")
val draw = widget_tree_to_draw_ir_with_theme(
    root, 120, 48, DRAW_IR_BACKEND_CPU, snapshot
)

expect(_material_request_count(draw)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(draw.batches[0].commands[0].component_id).to_equal(
    "root-button-surface-initializer"
)
expect(draw.batches[0].commands[1].component_id).to_equal("root-button")
expect(_command_color(draw, "root-button")).to_equal(snapshot.accent_rgba)
```

</details>

#### initializes a primitive root that has no root-id rectangle

- initializes a primitive root that has no root-id rectangle
- Verify: initializes a primitive root that has no root-id rectangle
   - Expected: _material_request_count(draw) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("initializes a primitive root that has no root-id rectangle")
step("Verify: initializes a primitive root that has no root-id rectangle")
val snapshot = theme_package_render_snapshot("aetheric_dark")
val root = WidgetNode.new("root-scroll", "scroll")
val draw = widget_tree_to_draw_ir_with_theme(
    root, 120, 48, DRAW_IR_BACKEND_CPU, snapshot
)

expect(_material_request_count(draw)).to_equal(0)  # oracle: 0 — named expected value from the requirement
expect(draw.batches[0].commands[0].component_id).to_equal(
    "root-scroll-surface-initializer"
)
expect(draw.batches[0].commands[1].component_id).to_equal(
    "root-scroll-track"
)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f81d5eae5dcd09992fff6a7f0901d5718a15762bd8d37125a1c6975502c4ff6b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f81d5eae5dcd09992fff6a7f0901d5718a15762bd8d37125a1c6975502c4ff6b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f81d5eae5dcd09992fff6a7f0901d5718a15762bd8d37125a1c6975502c4ff6b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_theme_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_theme_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/widget_draw_ir_theme_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects the selected snapshot surface and accent into the same widget tree' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl:140:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses existing hover and pressed widget state as semantic theme roles' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/widget_draw_ir_theme_spec.spl:154:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'projects Aetheric status chip roles and label text through Draw IR' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
