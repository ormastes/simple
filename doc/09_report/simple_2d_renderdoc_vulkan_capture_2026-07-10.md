# Simple 2D RenderDoc Vulkan Capture — 2026-07-10

## Result

Linux qualification capture passed with a real Vulkan Engine2D frame and
RenderDoc injection.

| Evidence | Observed value |
|---|---|
| Capture | `/tmp/simple-renderdoc-live-20260710/simple_gui_capture.rdc` |
| Size | 9,111 bytes |
| Magic | `RDOC` |
| Driver | Vulkan |
| Buffer creation | 1 `vkCreateBuffer` |
| Shader modules | 3 `vkCreateShaderModule` |
| Compute pipelines | 3 `vkCreateComputePipelines` |
| Dispatches | 3 `vkCmdDispatch` |
| XML replay export | 197,070 bytes |

## Procedure

The repo-provided RenderDoc 1.44 Vulkan-only bundle injected
`librenderdoc.so` into `src/compiler_rust/target/release/simple` while it ran
`src/app/test/renderdoc_vulkan_capture.spl`. The program reported
`backend=vulkan`, capture start/end success, and `num_captures=1`. The capture
was opened through `renderdoccmd convert -i rdc -c xml` before chunk markers
were checked.

## Scope

This qualifies real Linux Vulkan/RenderDoc behavior. It does not satisfy the
self-hosted Simple evidence gate: the capture runner is the bootstrap
interpreter because it carries the current RenderDoc externs. The pure-Simple
RDC XML inspector remains separately blocked by the tracked parser failure.

## Translation Lanes

An experimental runtime-selected DirectX-on-Vulkan probe failed with a missing
`vk_version` argument; the same dynamic selector also fails for Vulkan, while
the literal-Vulkan capture above succeeds. This is tracked at
`doc/08_tracking/bug/engine2d_vulkan_translation_vk_version_2026-07-10.md`.
Dedicated literal translation probes are still required; neither translation
lane is counted as a pass.
