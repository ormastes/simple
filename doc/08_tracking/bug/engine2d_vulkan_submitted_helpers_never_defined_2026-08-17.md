# engine2d imports five `vulkan_submitted_*` helpers that are never defined

- **Status:** OPEN (filed, not fixed — out of scope for the de-JIT lane that found it)
- **Found:** 2026-08-17, lane ENGINE2D2, while repairing the
  `VulkanBackend.fenced_submission_generation` whole-module de-JIT.
- **Tool attribution:** Rust SEED (`bin/simple`, `bin/simple run`).

## Defect

`src/lib/gc_async_mut/gpu/engine2d/engine.spl:41` imports

```
use std.gpu.engine2d.backend_vulkan.{VulkanBackend, VulkanFrameReceipt,
    vulkan_submitted_framebuffer_handle, vulkan_submitted_device_identity,
    vulkan_submitted_generation, vulkan_framebuffer_ownership_handle,
    vulkan_cancel_submitted_present_source}
```

Only `VulkanBackend` (`backend_vulkan.spl:185`) and `VulkanFrameReceipt`
(`backend_vulkan.spl:102`) exist. The other **five names are defined nowhere in
the tree** — `/usr/bin/grep -rn` over `src/` returns only the `use` line itself
and the call sites in `engine.spl`. They are *called*, not merely imported:

| caller | line |
|---|---|
| `Engine2D.vulkan_framebuffer_handle` | `engine.spl:1229` |
| `Engine2D.vulkan_ownership_framebuffer_handle` | `engine.spl:1234` |
| `Engine2D.vulkan_device_identity` | `engine.spl:1239` |
| `Engine2D.vulkan_submission_generation` | `engine.spl:1244` |
| `Engine2D.cancel_vulkan_present_source` | `engine.spl:1249` |

## Why it looks green

The seed reports each one as a non-fatal `[use-warning] '<name>' is named in
`use ...` but module '.../backend_vulkan.spl' does not provide it`, and
`bin/simple run src/lib/gc_async_mut/gpu/engine2d/engine.spl` exits **rc=0**.
Nothing fails until one of those five `Engine2D` methods is actually invoked on
a Vulkan surface. A rc=0 parse check is therefore not evidence that this file's
Vulkan presentation path works.

## Repair options (undecided — needs the engine2d Vulkan owner)

Either implement the five free functions in `backend_vulkan.spl` against the
real `VulkanBackend` submission state, or delete the five `Engine2D` methods and
the import entries. Do not leave the half-state. Note that `VulkanBackend` has
**no** submission-generation field at all today (see the sibling fix in commit
`50cf89b6a66`), so "implement" means designing that state, not just adding
accessors.
