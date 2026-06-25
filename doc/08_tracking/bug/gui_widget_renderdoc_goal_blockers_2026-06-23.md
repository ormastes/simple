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

## Current Evidence

As of 2026-06-25 on the Linux Vulkan host, the Simple lane is no longer a
blocker:

- `gui_widget_renderdoc_goal_simple_gate_status=pass`
- `gui_widget_renderdoc_goal_simple_gate_runtime_backend=vulkan`
- `gui_widget_renderdoc_goal_simple_gate_capture_file_magic=RDOC`

The remaining blocker is Electron under RenderDoc:

- `gui_widget_renderdoc_goal_electron_gate_status=fail`
- `gui_widget_renderdoc_goal_electron_gate_reason=chromium-gpu-process-crashed-under-renderdoc`
- `gui_widget_renderdoc_goal_electron_gate_vulkan_log_status=pass`
- `gui_widget_renderdoc_goal_electron_gate_argb_file_status=missing`
- `gui_widget_renderdoc_goal_electron_gate_capture_file_status=missing`

This means the Electron wrapper requests Vulkan/ANGLE and does not hit the
`vulkan-angle-unavailable` log gate, but Chromium's GPU process crashes under
RenderDoc before producing either nonblank ARGB evidence or a `.rdc` capture.

Rejected local variants on this host:

- `--in-process-gpu` changed the failure to Electron main-process `SIGSEGV`
  and produced no ARGB or `.rdc`.
- `--single-process` also produced Electron `SIGSEGV` and no ARGB or `.rdc`.
- `--use-gl=angle --use-angle=gl` still crashed the Chromium GPU process with
  `exit_code=139`, so the failure is not only the Vulkan ANGLE selection.
- Removing `renderdoccmd --opt-hook-children` avoided the GPU-process crash but
  ended with `Failed to shutdown` and still produced no `.rdc`, so it is not
  valid RenderDoc evidence.

Keep the gate failed until Electron produces both a nonblank ARGB proof and an
`RDOC` capture under the Chromium/Vulkan request contract.
