# Bug: GUI widget RenderDoc goal blockers remain

Status: open
Date: 2026-06-23
Area: GUI widget RenderDoc evidence

## Symptom

The GUI widget RenderDoc goal remains incomplete when:

- `gui_widget_renderdoc_goal_status` is not `pass`
- `gui_widget_renderdoc_goal_blocked_gate_count` is nonzero
- `gui_widget_renderdoc_goal_blocked_gates` lists missing Simple or Electron
  widget RenderDoc proof

Widget fixture coverage alone is not enough. Completion requires live RenderDoc
proof for the generated widget HTML fixture.

## Required Evidence

Completion requires:

- `gui_widget_renderdoc_goal_widget_feature_covered_count` matching the emitted
  `gui_widget_renderdoc_goal_widget_count`
- `gui_widget_renderdoc_goal_missing_widget_features` empty after comparing
  against `gui_widget_renderdoc_goal_expected_widget_features`
- `gui_widget_renderdoc_goal_simple_gate_status=pass`
- `gui_widget_renderdoc_goal_electron_gate_status=pass`
- `gui_widget_renderdoc_goal_blocked_gate_count=0`
- Simple GUI widget `.rdc` evidence on Vulkan Engine2D with `RDOC` magic
- Electron Chromium-on-Vulkan widget `.rdc` evidence with nonblank ARGB proof

Use `scripts/check/check-gui-widget-renderdoc-goal-status.shs --strict` only on
hosts with real Simple Vulkan Engine2D and Electron Chromium/Vulkan `.rdc`
evidence.
