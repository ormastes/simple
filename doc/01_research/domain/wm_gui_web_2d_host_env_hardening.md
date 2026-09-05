<!-- codex-research -->
# WM/GUI/Web/2D Host Environment Hardening — Domain Research

## Recommended Evidence Model

A real graphics test should correlate one run/frame identity across input,
application state, Vulkan submission, readback, and capture. Vulkan validation
and debug labels make command/resource provenance inspectable; explicit image
copy to a host-visible buffer supplies the absolute pixel oracle; RenderDoc's
in-application API supplies deterministic headless capture boundaries.

<!-- sdn-diagram:id=wm_gui_web_2d_host_env_hardening.domain_research -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=wm_gui_web_2d_host_env_hardening.domain_research hash=sha256:auto render=ascii
@layout dag
@direction LR

CDPOrNativeInput -> CorrelatedEvent
CorrelatedEvent -> VulkanDebugLabel
VulkanDebugLabel -> QueueSubmission
QueueSubmission -> ImageToBufferReadback
QueueSubmission -> RenderDocCapture
ImageToBufferReadback -> PixelOracle
RenderDocCapture -> ReplayInspection
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=wm_gui_web_2d_host_env_hardening.domain_research hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Primary-Source Findings

- Khronos recommends the unified validation layer during development and
  `VK_EXT_debug_utils` for named objects plus command/queue labels visible in
  tools such as RenderDoc:
  <https://docs.vulkan.org/guide/latest/validation_overview.html> and
  <https://docs.vulkan.org/guide/latest/extensions/VK_EXT_debug_utils.html>.
- `vkCmdCopyImageToBuffer` is the standard explicit image-to-buffer operation
  for deterministic post-submit pixel inspection:
  <https://docs.vulkan.org/refpages/latest/refpages/source/vkCmdCopyImageToBuffer.html>.
- RenderDoc supports Vulkan and exposes an in-application capture API; its
  maintainer specifically recommends `StartFrameCapture`/`EndFrameCapture` for
  headless workloads without presentation boundaries:
  <https://github.com/baldurk/renderdoc>,
  <https://github.com/baldurk/renderdoc/blob/v1.x/renderdoc/api/app/renderdoc_app.h>,
  <https://github.com/baldurk/renderdoc/issues/1386>.
- RenderDoc's Python API can inspect captures without a GUI:
  <https://github.com/baldurk/renderdoc/tree/v1.x/docs/python_api>.
- Chromium's DevTools Protocol drives real browser input through
  `Input.dispatchMouseEvent`/`dispatchKeyEvent`, exposes GPU identity/status
  through `SystemInfo`, and exposes runtime metrics/tracing:
  <https://chromedevtools.github.io/devtools-protocol/tot/Input/>,
  <https://chromedevtools.github.io/devtools-protocol/tot/SystemInfo/>,
  <https://chromedevtools.github.io/devtools-protocol/tot/Performance/>,
  <https://chromedevtools.github.io/devtools-protocol/tot/Tracing/>.

## Minimal Applicable Infrastructure

1. Reuse the production executable and inject native X11/winit or CDP input.
2. Carry one run/frame/event ID through receipts and Vulkan debug labels.
3. Submit, wait, copy/read back, and compare against an absolute oracle.
4. Capture that frame with the existing RenderDoc helper and validate `RDOC`
   magic; replay inspection is stronger follow-up evidence where available.
5. Bucket performance by physical device/driver/OS/architecture; use warm-up,
   repeated samples, median/p95, max RSS, and reject traces reporting data loss.
6. Treat unavailable native ISA/GPU/capture rows as blocked capability rows,
   never as mocked coverage or cross-device performance comparisons.
