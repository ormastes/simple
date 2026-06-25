# Bug: GUI/web/2D Vulkan RenderDoc blockers remain

Status: open
Date: 2026-06-23
Area: GUI/web/2D Vulkan, RenderDoc capture gates

## Symptom

The aggregate GUI audit must stay incomplete when:

- `gui_web_2d_vulkan_renderdoc_blocker_status=blocked`
- `gui_web_2d_vulkan_renderdoc_blocker_reason` names the current missing
  command, source evidence, browser Vulkan, RenderDoc, or pairwise ARGB diff
  gate
- `gui_web_2d_vulkan_renderdoc_blocker_gate_count` is nonzero
- `gui_web_2d_vulkan_renderdoc_blocker_gates` lists missing or unsupported
  Simple, Electron, Chrome, or macOS RenderDoc capture gates

Artifact presence alone is not enough. Required `.rdc` files must pass the
RenderDoc gate checks and have `RDOC` magic.

## Required Evidence

Completion requires the aggregate audit to prove:

- `gui_web_2d_vulkan_renderdoc_blocker_status=pass`
- `gui_web_2d_vulkan_renderdoc_blocker_reason=pass`
- `gui_web_2d_vulkan_renderdoc_blocker_gate_count=0`
- Simple Vulkan Engine2D RenderDoc evidence passes
- Electron Chromium/Vulkan and Chrome Vulkan `.rdc` evidence passes
- macOS hosts use the supported Simple RenderDoc debug path or record the
  platform blocker without claiming completion

Use the canonical capture entrypoints:

- `scripts/tool/renderdoc-evidence.shs capture-simple`
- `scripts/tool/renderdoc-evidence.shs capture-html`
- `scripts/tool/renderdoc-evidence.shs capture-electron-html`

Aggregate evidence may report compatibility check commands such as
`scripts/check/check-renderdoc-external-host-capture.shs`; use the
`renderdoc-evidence.shs` entrypoints above for fresh capture work.

## Current Linux Simple Capture State

2026-06-26 focused passing evidence:
`build/gui-web-2d-vulkan-env-renderdoc-simple-explicit-layer-owner-env/renderdoc/simple/evidence.env`.

Resolved:

- RenderDoc command discovery resolves `/usr/local/bin/renderdoccmd` symlinks to
  the real `/opt/renderdoc` home.
- Simple uses the Rust interpreter at `src/compiler_rust/target/release/simple`
  so `rt_renderdoc_*` externs resolve.
- Simple Vulkan readback passes on Intel(R) Graphics (RPL-P).
- The Simple capture now passes RenderDoc's Vulkan device pointer
  (`*((void **)VkInstance)`), not `VkDevice`; evidence shows a nonzero
  `rdoc_simple_renderdoc_device`.
- The helper creates a per-run RenderDoc Vulkan layer manifest with
  `library_path=/opt/renderdoc/lib/librenderdoc.so` and forces
  `VK_INSTANCE_LAYERS=VK_LAYER_RENDERDOC_Capture`.
- `rdoc_simple_renderdoc_capturing_after_start=1`
- `rdoc_simple_renderdoc_end=1`
- `rdoc_simple_renderdoc_num_captures=1`
- `rdoc_capture_status=pass`
- `rdoc_capture_magic=RDOC`

Still blocked:

- Chrome Vulkan `.rdc` evidence with `RDOC` magic.
- Electron Chromium/Vulkan `.rdc` evidence with `RDOC` magic and nonblank ARGB.

Current 2026-06-26 browser capture findings:

- Browser Vulkan backing itself now passes:
  `build/gui-web-2d-vulkan-env-browser-backing-electron42/evidence.env`
  reports Electron `vulkan=enabled_on` and Chrome `ANGLE_VULKAN`.
- Chrome RenderDoc with child-process hooking on the real Xwayland display
  still crashes the Chromium GPU process repeatedly with `exit_code=139`;
  evidence:
  `build/renderdoc/chrome-display-helper/html/evidence.env` and
  `build/renderdoc/chrome-real-xwayland-hook/renderdoc-html.log`.
- Chrome under Xvfb without child-process hooking no longer hits the same GPU
  crash, but Vulkan presentation fails because Xvfb has no DRI3 support:
  `build/renderdoc/chrome-no-child-hook-x11/renderdoc-html.log`.
- Chrome single-process is not acceptable because Chromium reports
  `Vulkan not supported with in process gpu`; evidence:
  `build/renderdoc/chrome-single-process-real-xwayland/renderdoc-html.log`.
- Chrome headless/in-process does not produce a presentable frame or `.rdc`,
  so it is not acceptable RenderDoc evidence.
- Electron 42 with `--ozone-platform=x11` renders Vulkan-backed ARGB outside
  RenderDoc, but under `renderdoccmd capture` on the real display it exits with
  `SIGTRAP` before ARGB or `.rdc` output. Earlier `xvfb-run` attempts also
  showed `ERR_FAILED` before the document-write fallback; after the fallback,
  both Xvfb and real-display launches trap. Evidence:
  `build/renderdoc/electron-display-helper/electron-html/evidence.env`,
  `build/renderdoc/electron42-real-xwayland-hook/renderdoc-electron-html.log`,
  and
  `build/renderdoc/electron42-explicit-layer-document-write/electron-html/evidence.env`.
