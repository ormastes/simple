# Bug: `VulkanBackend.draw_text` does not set `dirty=true` on uninitialized-Vulkan fallback (sibling `draw_text_bg` does)

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
