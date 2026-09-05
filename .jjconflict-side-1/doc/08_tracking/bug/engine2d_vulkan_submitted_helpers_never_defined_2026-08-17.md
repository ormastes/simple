# engine2d imported five `vulkan_submitted_*` helpers that were never defined

- **Status:** FIXED 2026-08-17 (implemented) — commit adding them to `backend_vulkan.spl`.
- **Found:** lane ENGINE2D2, while repairing the
  `VulkanBackend.fenced_submission_generation` whole-module de-JIT.
- **Tool attribution:** Rust SEED (`bin/simple`, `bin/simple run`).

## Defect

`src/lib/gc_async_mut/gpu/engine2d/engine.spl:41` imported seven names from
`std.gpu.engine2d.backend_vulkan`. Only `VulkanBackend`
(`backend_vulkan.spl:185`) and `VulkanFrameReceipt` (`backend_vulkan.spl:102`)
existed. The other **five were defined nowhere in the tree** — and they were
*called*, not merely imported:

| caller | line | missing symbol |
|---|---|---|
| `Engine2D.vulkan_framebuffer_handle` | `engine.spl:1229` | `vulkan_submitted_framebuffer_handle` |
| `Engine2D.vulkan_ownership_framebuffer_handle` | `engine.spl:1234` | `vulkan_framebuffer_ownership_handle` |
| `Engine2D.vulkan_device_identity` | `engine.spl:1239` | `vulkan_submitted_device_identity` |
| `Engine2D.vulkan_submission_generation` | `engine.spl:1244` | `vulkan_submitted_generation` |
| `Engine2D.cancel_vulkan_present_source` | `engine.spl:1249` | `vulkan_cancel_submitted_present_source` |

## Why it looked green

The seed reports each as a non-fatal `[use-warning] '<name>' is named in
`use ...` but module '.../backend_vulkan.spl' does not provide it`, and
`bin/simple run src/lib/gc_async_mut/gpu/engine2d/engine.spl` exited **rc=0**.
A rc=0 parse check is therefore NOT evidence that this file's Vulkan
presentation path works.

It also dropped the whole module out of the JIT. It was the *second* de-JIT
cause in this module, hidden behind the first: only after the
`fenced_submission_generation` write was deleted did the seed get far enough to
report `[jit-fallback] unresolved external symbol
'vulkan_submitted_framebuffer_handle': whole module dropped to the interpreter`.

## Repair: implemented, not deleted

Deleting the five `Engine2D` methods was rejected — eight assertions across
`test/01_unit/lib/gpu/engine2d/engine_branch_coverage_spec.spl:120-124` and
`draw_ir_adv_branch_coverage_spec.spl:482-484` call them and require the
fail-closed `0`/`false` results. All the state they need already existed on
`VulkanBackend`, so the five functions were written against it, plus one shared
predicate `_vulkan_submission_is_proven`:

- A submission is "proven" only when `cpu_fallback_used` is false,
  `completion_unknown` is false, the surface is `initialized`,
  `observed_device_submit_count > 0`, and
  `observed_device_fence_count >= observed_device_submit_count`. Those two
  counters are the file's own documented contract: a submit is recorded only
  after the SFFI returns a concrete fence, a fence only after the wait succeeds.
- `vulkan_submitted_generation` returns the *fence* count, never the submit
  count, so the generation can never name work still in flight.
- `vulkan_framebuffer_ownership_handle` deliberately does NOT require a proven
  submission — ownership exists as soon as the device allocation does — but is
  still 0 on CPU fallback or before initialization.
- `vulkan_cancel_submitted_present_source` is exact-match: the caller must name
  both the framebuffer handle and the generation it was handed, so a late
  cancel cannot tear down a newer frame's present source.

## Evidence

- `bin/simple run src/lib/gc_async_mut/gpu/engine2d/engine.spl` → rc=0 with
  **zero** `use-warning`s for the five names (previously five).
- `bin/simple run src/app/test/renderdoc_vulkan_capture.spl` → rc=0 with
  **zero** `[jit-fallback]` lines (previously one).
- `engine_branch_coverage_spec.spl`: 10 passed / 45 failed both before
  (baseline worktree at `280f8eacece`) and after — no regression. That spec's
  pre-existing red is a separate, unrelated defect: `Engine2D.create` yields an
  empty dict, so every example fails with `method <name> not found on type
  `dict` (receiver value: {})`, including methods this change never touched.
