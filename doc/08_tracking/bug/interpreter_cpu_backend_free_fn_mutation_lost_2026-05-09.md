# Bug — CpuBackend drawing primitives that delegate to free functions drop pixel mutations in interpreter mode

**Filed:** 2026-05-09 (engine2d_drawing_spec.spl integration test authoring)
**Severity:** High — `draw_rect`, `draw_circle_filled`, `draw_line`, `draw_triangle_filled` are silently no-ops on the cpu backend in interpreter mode; pixels remain black after drawing.

## Symptom

```spl
var engine = Engine2D.create_with_backend(20, 20, "cpu")
engine.clear(rgb(0, 0, 0))
engine.draw_rect(2, 2, 16, 16, rgb(0, 255, 0))
engine.present()
val pixels = engine.read_pixels()
# pixel at (2,2) — the top-left border corner — is black, not green
print(color_g(pixels[2 * 20 + 2]))  # prints 0, expected 255
```

## Affected Methods (cpu backend, interpreter mode only)

| Method | Delegates to | Status |
|---|---|---|
| `draw_rect` | `_hline`, `_vline` | BROKEN — no pixels written |
| `draw_circle_filled` | `_hline` | BROKEN — no pixels written |
| `draw_line` | `_bresenham` | BROKEN — no pixels written |
| `draw_triangle_filled` | `_fill_triangle_scanlines` → `_hline` | BROKEN — no pixels written |
| `draw_rect_filled` | inline `self.buf[idx] = color` | WORKS |
| `clear` | inline `self.buf[i] = color` | WORKS |

## Repro

```bash
cat > /tmp/repro_cpu.spl << 'EOF'
use std.spec.{describe, it, expect}
use std.gc_async_mut.gpu.engine2d.engine.{Engine2D}
use std.gc_async_mut.gpu.engine2d.color.{rgb, color_g}

fn pix(pixels: [u32], x: i32, y: i32, w: i32) -> u32:
    pixels[y * w + x]

describe "cpu backend mutation bug repro":
    it "draw_rect border pixel is black (bug)":
        var engine = Engine2D.create_with_backend(20, 20, "cpu")
        engine.clear(rgb(0, 0, 0))
        engine.draw_rect(2, 2, 16, 16, rgb(0, 255, 0))
        engine.present()
        val pixels = engine.read_pixels()
        # Expected 255, actual 0 — BUG
        expect(color_g(pix(pixels, 2, 2, 20))).to_equal(255)
        engine.shutdown()
EOF
bin/simple test /tmp/repro_cpu.spl
# → expected 0 to equal 255
```

## Root Cause (hypothesis)

`draw_rect` (and the other affected methods) delegates to free functions:

```spl
me draw_rect(x: i32, y: i32, w: i32, h: i32, color: u32):
    _hline(self, x, y, w, color)          # self passed by value → copy
    ...

fn _hline(backend: CpuBackend, x: i32, y: i32, length: i32, color: u32):
    var i = 0
    while i < length:
        _set_pixel(backend, x + i, y, color)   # backend passed by value again
        i = i + 1

fn _set_pixel(backend: CpuBackend, x: i32, y: i32, color: u32):
    ...
    backend.buf[idx] = color   # mutates a copy — lost on return
```

In interpreter mode, struct fields (including `[u32]` array fields) appear to be copied when a struct is passed to a free function by value. Writes to `backend.buf[idx]` in `_set_pixel` modify a copy that is discarded on return.

The working methods (`clear`, `draw_rect_filled`) write directly to `self.buf[idx]` inside the `me` body, bypassing the copy.

## Why Software Backend Is Unaffected

`SoftwareBackend` uses an identical delegation pattern (`_sw_hline` → `_sw_set_pixel`) and passes. The difference is not yet understood — it may be related to `SoftwareBackend`'s additional `dirty_tiles: [bool]` field or some other structural difference that affects how the interpreter snapshot/copies the struct. Investigation is needed by the compiler team.

## Impact

- `test/integration/rendering/engine2d_drawing_spec.spl` — 4 of 6 tests fail due to this bug
- Any code using `CpuBackend` as the drawing target in interpreter mode (tests, scripts) will silently produce blank images for the affected primitives
- Compile mode (`--mode=native`) is unaffected (real struct references used)

## Workaround

Use `"software"` backend instead of `"cpu"` for interpreter-mode tests that exercise `draw_rect`, `draw_circle_filled`, `draw_line`, or `draw_triangle_filled`. The `engine2d_primitives_spec.spl` already does this and passes.

## Related

- `doc/08_tracking/bug/interpreter_array_push_u8_literal_lost_2026-05-02.md` — similar interpreter mutation-lost pattern for `[u8]`
- `test/integration/rendering/engine2d_primitives_spec.spl` — covers same primitives on software backend, all passing
- `src/lib/gc_async_mut/gpu/engine2d/backend_cpu.spl` — affected source
