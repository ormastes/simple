# Bug: GUI/web/2D Vulkan RenderDoc blockers remain

Status: open
Date: 2026-06-23
Area: GUI/web/2D Vulkan, RenderDoc capture gates

## Symptom

The aggregate GUI audit must stay incomplete when:

- `gui_web_2d_vulkan_renderdoc_blocker_status=blocked`
- `gui_web_2d_vulkan_renderdoc_blocker_gate_count` is nonzero
- `gui_web_2d_vulkan_renderdoc_blocker_gates` lists missing or unsupported
  Simple, Electron, Chrome, or macOS RenderDoc capture gates

Artifact presence alone is not enough. Required `.rdc` files must pass the
RenderDoc gate checks and have `RDOC` magic.

## Required Evidence

Completion requires the aggregate audit to prove:

- `gui_web_2d_vulkan_renderdoc_blocker_status=pass`
- `gui_web_2d_vulkan_renderdoc_blocker_gate_count=0`
- Simple Vulkan Engine2D RenderDoc evidence passes
- Electron Chromium/Vulkan and Chrome Vulkan `.rdc` evidence passes
- macOS hosts use the supported Simple RenderDoc debug path or record the
  platform blocker without claiming completion

Use the canonical capture entrypoints:

- `scripts/tool/renderdoc-evidence.shs capture-simple`
- `scripts/tool/renderdoc-evidence.shs capture-html`
- `scripts/tool/renderdoc-evidence.shs capture-electron-html`
