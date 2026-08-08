# game2d `_f64_to_i32`/`_i32_to_f64`/`_i32_to_u32` externs return `nil` under the tree-walk interpreter (2026-07-31)

**Status:** OPEN — workaround applied only in the one file touched by this
lane (`tilemap.spl`). The same defect is still latent in `camera.spl`,
`scene.spl`, `batch.spl`, `__init__.spl` (all in
`src/lib/gc_async_mut/game2d/`).

**Impact:** every `@extern fn _f64_to_i32(x: f64) -> i32` /
`@extern fn _i32_to_f64(x: i32) -> f64` / `@extern fn _i32_to_u32(x: i32) ->
u32` call **always returns `nil`** under `bin/simple test` (the tree-walk
interpreter — see `.claude/rules/testing.md`). No native runtime symbol backs
these externs; they were presumably only ever exercised under the JIT/native
codegen paths, never the interpreter that the spec suite runs on.

## Why this went unnoticed

Every existing caller (`scene.spl::_draw_sprite`, `SpriteBatch.flush`,
`Camera2D`) feeds the `nil` `px`/`py` straight into `Engine2D.draw_image`,
which apparently treats `nil` x/y as *some* fallback location and still draws
*something*. Existing specs (`scene_spec.spl`, `batch_spec.spl`) only assert
"a pixel of the expected color exists somewhere in the canvas" — they never
assert exact position, and several test cases coincidentally expect the
sprite at world (0,0)-ish screen coordinates, which happens to line up with
whatever `draw_image` falls back to for `nil`. So `Results: 8 total, 8
passed` on `scene_spec.spl` today, despite every `_f64_to_i32` call inside it
actually returning `nil`.

Confirmed directly: instrumenting `scene.spl::_draw_sprite` with
`print("... px={px} py={py}")` while running the passing
`test/01_unit/lib/gc_async_mut/game2d/scene_spec.spl` prints `px=nil py=nil`
on every draw call, including the ones the "produces red pixels from a red
sprite" example depends on.

## Minimal reproducer

```simple
use std.spec

@extern fn _f64_to_i32(x: f64) -> i32

describe "extern registration":
    it "returns nil, not 16":
        expect(_f64_to_i32(16.0)).to_equal(16)   # actually gets `nil`
```

## Root cause (once real drawing needs 2 distinct, positioned tiles)

`src/lib/gc_async_mut/game2d/tilemap.spl` (this lane, GAP-5 tilemap texture
sampling) needed **two tiles at two different screen positions in the same
frame** and asserted both real colors are present. With `px`/`py` always
`nil`, `Engine2D.draw_image` apparently draws every tile at the *same*
fallback location, so the second tile's write clobbers the first — the
"real colors present" assertion failed until this was worked around.

## Fix applied (this file only)

Replaced the `@extern` calls with the equivalent builtin conversion methods,
which ARE implemented under the interpreter (same pattern already used by
`src/os/crypto/chacha20.spl::_i32_to_u32`/`_u32_to_i32`):

- `_f64_to_i32(x)` -> `x.to_i32()`
- `_i32_to_f64(x)` -> `x.to_f64()`
- `_i32_to_u32(x)` -> `x.to_u32()`

Verified via `test/01_unit/lib/common/nogc_sync_mut...` — n/a; verified via
`test/01_unit/lib/gc_async_mut/game2d/texture_registry_spec.spl` (new,
8/8 passing) which exercises real two-tile positioning end-to-end through
`Engine2D`.

## Remaining scope (not fixed — flagging, not silently working around)

`camera.spl:129`, `scene.spl:189` (`_draw_sprite`/`_draw_animated_sprite`),
`batch.spl:91` (`SpriteBatch.flush`), and `__init__.spl:119` all still
declare the same broken `@extern` and will return `nil` for `px`/`py` under
the interpreter. None of their existing specs catch it because none assert
exact multi-sprite screen position. Recommend the same `.to_i32()`/
`.to_f64()` swap there in a follow-up lane, plus a position-asserting spec
addition (e.g. two sprites at two known screen coordinates, assert both
colors at their expected offsets, not just "somewhere in the canvas").
