# DirectX Engine2D has no GPU text path, so the Vulkan/Metal font batching has nothing to port into

- **Filed:** 2026-09-05
- **Status:** OPEN, not started. Recorded while porting the Vulkan font
  frame-batching optimization to Metal.
- **Owner surface:** `src/lib/gc_async_mut/gpu/engine2d/backend_directx.spl`,
  `src/runtime/runtime_directx_core.c`
- **Platform:** Windows (native D3D11) and Linux (DXVK). Neither is available
  on the host where this was found (aarch64-apple-darwin), so nothing below
  was executed.

## What was being ported

Vulkan received a five-commit 2D font optimization in August 2026:
`b4237c5f815` (bound frame resources), `a2eaba3a49a` (one command buffer, one
submission, one fence per frame), `ef933994d6e` (warm glyph resources),
`63687490087` (packed atlas dispatches) and `75874ef4676` (retained frames on
the same device). Metal received the equivalent on 2026-09-05.

## Why DirectX gets nothing from it

The two properties the port delivers are already true or already impossible
on this backend, for reasons that have nothing to do with the optimization:

- **One submission per frame is structural, not an optimization.** The
  DirectX backend does not submit per operation at all. It encodes a bounded
  CLEAR / FILL_RECT / opaque-IMAGE subset into a packed u32 frame-record
  stream (`DIRECTX_FRAME_MAGIC`, `DIRECTX_FRAME_RECORD_WORDS`) and executes
  the whole stream through exactly one `directx_execute_readback_checked`
  call. There is no per-quad submission to collapse.
- **There is no GPU text to batch.** Both text entrypoints delegate straight
  to the software mirror (`backend_directx.spl:221` `draw_text_bg` and `:382`
  `draw_text`, each calling `self.sw.<same>`). Text therefore never enters the
  record stream, and per this backend's own receipt rule any operation outside
  the eligible subset poisons native receipt eligibility for that frame.

## What a real DirectX font path needs

None of this exists today and none of it is a rename of existing code:

1. An HLSL compute twin of `font_atlas_composite_vulkan_glsl_source` /
   `font_atlas_composite_metal_packed_source`, added to
   `src/lib/common/gpu/font_atlas_composite.spl`, keeping the frozen word
   layout (8 header words, then 7 per glyph).
2. A new frame-record opcode for the atlas composite, plus the atlas upload
   and params buffer lifetime, alongside the existing three opcodes.
3. New `rt_directx_*` runtime entries. The current C surface has no compute
   dispatch, no fence, and no present entry at all — the whole exported set is
   open/close device, adapter identity, one execute-readback, and small pure
   helpers.
4. A Windows or DXVK host to run any of it. `-fsyntax-only` style checking
   cannot substitute: the existing C-runtime gate compiles source, it does not
   execute a device.

## Why this is a record and not a change

Writing an unverifiable D3D compute path on a machine that cannot compile,
link, or execute it would produce exactly the kind of green-looking, never-run
code the stage-binary and unbacked-extern guards exist to catch. The scope is
recorded here instead so the work is visible and can be picked up on a host
that can prove it.
