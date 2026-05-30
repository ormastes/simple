# Mutations Lost When `self` / `self.field` Is Passed to a Free Function

**Date:** 2026-05-29
**Component:** compiler value/reference semantics (method receiver passing)
**Severity:** High (silent data loss; breaks helper-function refactors)
**Status:** Fixed in pure Simple interpreter path
**Found via:** 2D engine software backend rendering — only `draw_rect_filled`
produced pixels; circle/line/gradient/rounded/text drew nothing.

## Summary

When a method (`me` method or trait method) passes `self` — or a field read of
`self` such as `self.buf` — into a **free function**, the callee receives a
**copy**. Mutations the callee makes to that copy (including writes into an
array field) do **not** propagate back to the original object. This reproduces
in **both** interpreter (`SIMPLE_EXECUTION_MODE=interpret`) and the default
JIT/compiled run path.

A local variable passed to the same free function from `main` (or from a method)
**does** persist, so the defect is specific to passing the method *receiver* or
a *field read of the receiver*.

## 2026-05-29 Repair

Worker B fixed the pure Simple tree-walking interpreter in
`src/compiler/10.frontend/core/interpreter/eval_ops_part1.spl`.
`eval_function_call` now records mutable aggregate parameters after the callee
body and writes them back to the original caller argument when that argument is
an identifier or field access. This covers both regression forms:
`write_first(self.values, next)` and `write_holder_first(self, next)`.

Focused verification passed:

```bash
SIMPLE_LIB=src bin/simple check src/compiler/10.frontend/core/interpreter/eval_ops_part1.spl test/unit/compiler/interpreter/self_field_assign_spec.spl --mode=interpreter
SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/self_field_assign_spec.spl --mode=interpreter --clean
SIMPLE_LIB=src bin/simple test test/unit/compiler/interpreter/self_field_assign_spec.spl --clean
```

## Minimal Reproduction

```simple
class B:
    data: [u32]

fn f_arr(a: [u32], i: i64, v: u32):
    a[i] = v
fn f_obj(b: B, i: i64, v: u32):
    b.data[i] = v

impl B:
    me via_inline(i: i64, v: u32):   self.data[i] = v          # persists
    me set_inner(i: i64, v: u32):    self.data[i] = v
    me via_me(i: i64, v: u32):       self.set_inner(i, v)       # persists
    me via_farr(i: i64, v: u32):     f_arr(self.data, i, v)     # LOST
    me via_fobj(i: i64, v: u32):     f_obj(self, i, v)          # LOST
    fn get(i: i64) -> u32:           self.data[i]

fn main() -> i64:
    var b = B(data: [0u32; 6])
    b.via_inline(0, 10u32)
    b.via_me(1, 11u32)
    b.via_farr(2, 12u32)
    b.via_fobj(3, 13u32)
    print b.get(0).to_text()  # 10  (ok)
    print b.get(1).to_text()  # 11  (ok)
    print b.get(2).to_text()  # 0   (want 12) — LOST
    print b.get(3).to_text()  # 0   (want 13) — LOST
    0
```

Observed (both interpreter and JIT): `10, 11, 0, 0`.

## Pattern Matrix

| call pattern (from inside a method) | persists? |
|-------------------------------------|-----------|
| `self.field = v` / `self.buf[i] = v` (inline)      | yes |
| `self.helper(...)` where helper writes `self.*`     | yes |
| local `var a: [..]`; `free_fn(a, ...)`              | yes |
| `free_fn(self.field, ...)` (field read passed)      | **no** |
| `free_fn(self, ...)` (receiver passed)              | **no** |

So: only inline receiver writes and `me`→`me` calls reliably mutate the
receiver. Passing the receiver (or a field of it) into a free function silently
drops writes.

## Concrete Impact

`src/lib/gc_async_mut/gpu/engine2d/backend_software.spl` (the CPU/software 2D
renderer; `CpuBackend` delegates to it) draws via free helpers
`_sw_hline`/`_sw_set_pixel`/`_sw_vline`/`_sw_bresenham`/`_sw_corner_arc` and the
`fill_span`/`copy_span`/`render_text_to_buffer` kernels, all called as
`_sw_xxx(self, ...)` / `fill_span(self.buf, ...)` from the draw `me` methods.
Every such write is dropped. Only `draw_rect_filled`, whose opaque path writes
`self.buf[idx] = color` inline, renders. Verified at 32x32: rect draws, circle /
line / gradient / rounded / text all produce background pixels.

Dirty-tile tracking (`_mark_*` free helpers writing `self.dirty_tiles`) is hit by
the same defect, but that is cosmetic (does not affect `read_pixels` output).

## Workaround (applied to the software backend)

Per the project rule `[No bootstrap rebuild] / [Fix in pure Simple]`, the seed
compiler is **not** patched here. The software backend is being repaired to use
only the persisting patterns: the pixel-write helpers become `me` methods that
write `self.buf` inline (no `fill_span` on `self.buf`), and `draw_text` renders
into a *local* buffer (which persists) then inline-copies into `self.buf`.

## Recommended Real Fix

Method receiver (and field reads thereof) should be passed to free functions by
reference, matching local-variable semantics, so that callee mutations persist.
Until then, code must mutate the receiver only via inline `self.*` writes or
`me`→`me` calls, never by handing `self`/`self.field` to a free function.

## Related

- Render symptom + example app: `examples/ui/engine2d_backend_test.spl`
- Regression guard: `test/unit/lib/gpu/engine2d/backend_software_primitives_spec.spl`
