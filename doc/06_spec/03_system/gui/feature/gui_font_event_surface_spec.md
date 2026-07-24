# GUI Font and Event Surface

> CPU-fixture GUI widget-tree font, Draw IR, framebuffer, and correlated input-event contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 0 | 0 | 1 |

> **Current execution: BLOCKED.** The pure-Simple runner fails before any
> example executes with `runtime error: field access on nil receiver`.
> No framebuffer artifact is currently accepted as PASS.

<details>
<summary>Full Scenario Manual</summary>

# GUI Font and Event Surface

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | AC-3, AC-6, AC-7, AC-8, AC-9 |
| Category | GUI \| Rendering \| Interaction |
| Status | **BLOCKED — no examples executed** |
| Source | `test/03_system/gui/feature/gui_font_event_surface_spec.spl` |
| Updated | 2026-07-24 |
| Mirror | Manual mirror; regenerate with `simple spipe-docgen` after the runtime blocker is fixed |

## Purpose

When the blocked executable scenario can run, it proves that one visible GUI
widget tree:

1. emits the selected `GUI42` text, pinned font identity, ordered advances,
   exact bounds, and `gui_ast` source metadata into the exact
   `DrawIrComposition` submitted to Engine2D;
2. produces a glyph-bearing CPU framebuffer that differs from an otherwise
   identical blank-label framebuffer inside the glyph band;
3. delivers pointer, focus, and keyboard events to the visible `gui-input`;
4. submits the updated `ReadyZ` composition and retains all three framebuffer
   captures.

It uses the canonical `widget_tree_to_draw_ir_cpu`,
`DrawIrComposition`, Engine2D Draw IR executor, and shared PPM encoder. It does
not introduce a GUI-private font renderer, atlas, cache, or command collector.
Its source wiring and fixture assertions are not live-window evidence.

## Primary GUI Font and Event Flow

### renders selected glyphs and delivers pointer focus and keyboard events to the visible input

1. **Load the pinned multilingual font manifest**
   - Build the visible `gui-root` fixture with title `GUI42` and input value
     `Ready`.

2. **Accept exact-face-bound simple-script shaping**
   - Preserve the selected face identity and ordered advances in the submitted
     text command.

3. **Trace the production font and event boundary**
   - Convert the production widget tree with `widget_tree_to_draw_ir_cpu`.
   - Select the `GUI42` text command from that exact composition.

4. **Prepare one shared font batch for 2D and 3D**
   - Text: `GUI42`
   - Family: `Noto Sans Mono`
   - Identity: starts with `sha256=`
   - Ordered advances: `7,7,7,7,7`
   - Bounds: `x=3, y=9, width=35, height=14`

5. **Emit the selected font composite program and plan compilation**
   - Composition: `widget-composition`
   - Scene: `widget:192x80`
   - Source kind: `gui_ast`
   - Source ID: `gui-root`
   - Style key: `widget-tree`

6. **Build the production surface composition**
   - Create the canonical 192×80 CPU Engine2D surface.

7. **Submit the boundary output to its canonical consumer**
   - Submit the same `submitted` value inspected above.
   - Require zero skipped commands.
   - Encode and retain the exact framebuffer as P6 PPM.
   - Render an otherwise-identical blank-label composition.
   - Require more than 20 differing pixels inside the selected glyph band.

7. **Correlate visible pixels and input with one frame identity**
   - Resolve pointer, focus, and key contexts against the submitted scene.
   - Require each resolved context to retain the submitted composition and scene
     identity.
   - Require `gui_ast` source metadata.
   - Require the actual fixture input to be visible and focused after the
     pointer click.
   - Deliver `Z` and require the actual input value to become `ReadyZ`.

8. **Reject disconnected stale or replayed evidence**
   - Resolve the same input against a replayed scene key.
   - Require an unresolved context with `stale_scene_rejected=true` and preserve
     `ReadyZ`.

9. **Capture backend and framebuffer evidence**
   - Convert and submit the updated widget tree.
   - Require zero skipped commands and visible updated glyph pixels.
   - Write the metadata receipt only with `status=pass` when every required
     PPM write succeeds.

10. **Prove native submission and device readback**
   - Require exactly `192 × 80` readback pixels.

## Retained Evidence Contract

All rows are currently **BLOCKED / not produced by a passing execution**.

| Artifact | Required contract | Current status |
|----------|-------------------|----------------|
| `build/test-artifacts/03_system/gui/feature/gui_font_event_surface/submitted.ppm` | Exact submitted `GUI42` framebuffer; P6 size `192×80×3 + 14` bytes | BLOCKED |
| `build/test-artifacts/03_system/gui/feature/gui_font_event_surface/blank_oracle.ppm` | Otherwise-identical blank-label framebuffer; same exact P6 size | BLOCKED |
| `build/test-artifacts/03_system/gui/feature/gui_font_event_surface/updated.ppm` | Exact post-keyboard `ReadyZ` framebuffer; same exact P6 size | BLOCKED |
| `build/test-artifacts/03_system/gui/feature/gui_font_event_surface/gui_font_event.txt` | `status=pass`, composition/scene frame identity, source/bounds/event targets, replay rejection, and all three paths | BLOCKED |
| `build/test-artifacts/03_system/gui/feature/gui_font_event_surface/verification-blocker.txt` | Exact failed commands, results, and resume command | AVAILABLE blocker evidence only |

The scenario fails closed if any framebuffer has the wrong encoded size, any
write fails, glyph-band evidence is blank, any event target is unresolved, or
the metadata status is not `pass`.

## Current Blocker and Reproduction

Failed focused command:

```sh
bin/simple test test/03_system/gui/feature/gui_font_event_surface_spec.spl --mode=interpreter
```

Observed result:

```text
0 passed, 1 failed
runtime error: field access on nil receiver
```

The existing legacy control fails before examples with the same error:

```sh
bin/simple test test/03_system/app/simple_2d/feature/legacy_web_gui_wm_font_route_spec.spl --mode=interpreter
```

After the shared runtime/Engine2D constructor issue is repaired, run the focused
command once, then regenerate this mirror:

```sh
bin/simple spipe-docgen test/03_system/gui/feature/gui_font_event_surface_spec.spl --output doc/06_spec --no-index
```

Do not promote this manual or any listed PPM path to PASS until the focused
scenario executes and the generated mirror reports zero stubs.

<details>
<summary>Executable SSpec flow</summary>

The canonical executable source is
`test/03_system/gui/feature/gui_font_event_surface_spec.spl`. Its visible
scenario steps are:

```simple
step("Load the pinned multilingual font manifest")
step("Accept exact-face-bound simple-script shaping")
step("Trace the production font and event boundary")
step("Prepare one shared font batch for 2D and 3D")
step("Emit the selected font composite program and plan compilation")
step("Build the production surface composition")
step("Submit the boundary output to its canonical consumer")
step("Correlate visible pixels and input with one frame identity")
step("Reject disconnected stale or replayed evidence")
step("Capture backend and framebuffer evidence")
step("Prove native submission and device readback")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Passing scenarios | 0 |
| Blocked scenarios | 1 |
| Placeholder scenarios | 0 |

</details>
