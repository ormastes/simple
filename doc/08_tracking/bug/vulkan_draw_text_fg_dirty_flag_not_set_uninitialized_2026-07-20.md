# Bug: `VulkanBackend.draw_text` does not set `dirty=true` on uninitialized-Vulkan fallback (sibling `draw_text_bg` does)
## Resolved 2026-11-22 — `_draw_text_impl` and `_gpu_draw_text_fallback` aligned and verified

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

Date: 2026-07-20

## Symptom

`test/01_unit/lib/gpu/engine2d/backend_vulkan_text_fallback_spec.spl`:
```
Engine2D Vulkan text fallback
  ✗ skips foreground glyph upload when Vulkan is uninitialized
    expected false to equal true
  ✓ skips background glyph staging when Vulkan is uninitialized

2 examples, 1 failure
```

Command:
```
SIMPLE_RUST_SEED_WARNING=0 timeout 25 bin/release/x86_64-unknown-linux-gnu/simple \
  test test/01_unit/lib/gpu/engine2d/backend_vulkan_text_fallback_spec.spl --no-session-daemon
```

## Minimal repro (trimmed from the spec)

```
use std.gpu.engine2d.backend_vulkan.{VulkanBackend}

var backend = VulkanBackend.create()
backend.draw_text(0, 0, "A", 0xff112233u32, 7)

expect(backend.initialized).to_equal(false)  # passes
expect(backend.dirty).to_equal(true)         # FAILS — actual is false
```

## Root cause (asymmetry between sibling foreground/background text paths)

`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl:333-338`, the background
path `draw_text_bg` explicitly sets `dirty = true` before returning early when
Vulkan is uninitialized:

```
me draw_text_bg(x: i32, y: i32, text_val: text, fg: u32, bg: u32, font_size: i32):
    if self.completion_unknown: return
    self.cpu_fallback_used = true
    if not self.initialized:
        self.dirty = true
        return
    ...
```

But the foreground path `draw_text` (`backend_vulkan.spl:725-730`) delegates to
`_gpu_draw_text_fallback` in `src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl:144-153`,
which does NOT set `dirty` on the uninitialized early-return branch:

```
me _gpu_draw_text_fallback(x: i32, y: i32, text_val: text, color: u32, font_size: i32):
    self.cpu_fallback_used = true
    if not self.initialized:
        return          # <-- missing `self.dirty = true` here, unlike draw_text_bg
    ...
```

The spec's two `it` blocks are structurally symmetric (draw_text vs
draw_text_bg, same assertions) which is why only the foreground one fails —
it exercises the helper that's missing the flag set.

## Suggested fix (not applied — out of shard scope, not an import/rename)

Add `self.dirty = true` before the early `return` in
`_gpu_draw_text_fallback` (backend_vulkan_helpers.spl:152-153), mirroring
`draw_text_bg`'s inline uninitialized branch.

## Affected

- `test/01_unit/lib/gpu/engine2d/backend_vulkan_text_fallback_spec.spl` (1 of 2 examples)

## Resolution (2026-11-22)

- `_draw_text_impl` (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan.spl`) and `_gpu_draw_text_fallback` (`src/lib/gc_async_mut/gpu/engine2d/backend_vulkan_helpers.spl`) both now set `self.dirty = true`, `self.host_mirror_frame_fresh = false`, `self.note_damage_full()`, `self.last_text_path = "cpu-raster-blit"`, and `self.last_text_fallback_reason = "backend-uninitialized"` before returning when `not self.initialized`.
- `_gpu_draw_text_fallback` also sets `self.last_text_path = "cpu-raster-blit"` and `self.last_text_fallback_reason = "legacy-text-host-framebuffer-fallback"` on the initialized fallback path. When the GPU upload succeeds, it invalidates `self.host_mirror_valid = false` and `self.host_mirror_frame_fresh = false` with `self.dirty = true`; when the GPU upload fails (`not uploaded`), it promotes `self.host_buf` as the authoritative fallback surface (`host_mirror_valid = true`, `host_mirror_frame_fresh = true`, `cpu_fallback_host_surface = true`, `dirty = true`, updated `last_host_checksum`, and recorded `last_error`) so subsequent `read_pixels_with_source()` / `present()` never overwrite the rendered text from a stale `d_framebuffer`.
- Added direct `_gpu_draw_text_fallback` regression coverage in `test/01_unit/lib/gpu/engine2d/backend_vulkan_text_fallback_spec.spl` and verified 4/4 examples pass.

