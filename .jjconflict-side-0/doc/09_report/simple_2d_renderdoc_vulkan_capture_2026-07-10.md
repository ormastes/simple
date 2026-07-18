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

## Canonical observed-frame record

On 2026-07-10, the live Vulkan probe emitted a schema-valid record directly
from the Engine2D capture frame: 3,072 readback pixels, a positive Vulkan
device handle, and matching target/readback SHA-256
`694777e154ed923198495c4f0060a87f0f593bf2dbbe6ae52c8a06793506c52f`.
Its semantic record hash was
`6f25a5f82aaf8da1cfc36a9fa9198b7c534c1922160bd55609b6e2049ac4ce61`.
The probe uses the bootstrap runner only, so this is Linux qualification—not
self-hosted release evidence.

## Translation Lanes

An experimental runtime-selected DirectX-on-Vulkan probe failed with a missing
`vk_version` argument; the same dynamic selector also fails for Vulkan, while
the literal-Vulkan capture above succeeds. This is tracked at
`doc/08_tracking/bug/engine2d_vulkan_translation_vk_version_2026-07-10.md`.
Dedicated literal translation probes are still required; neither translation
lane is counted as a pass.

The literal Linux probe now confirms that `directx-on-vulkan` initializes and
renders through Vulkan. The literal `metal-on-vulkan` constructor returns
`backend unavailable` on this host, so no pairwise-equivalence result is
claimed. This remains fail-closed: an unavailable Metal translation must not
fall back to a pass-shaped Vulkan result.

The DirectX-on-Vulkan framebuffer hash is
`694777e154ed923198495c4f0060a87f0f593bf2dbbe6ae52c8a06793506c52f`,
matching the Vulkan capture scene. This proves this one literal Linux
translation scene only; it does not qualify native DirectX or native Metal.
The translated record also validates with semantic hash
`30f04ea7efafbe88f3f97798e2a43b948b9b18b5a23b233644f63fc0afbaeece`.
