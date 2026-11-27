# Seed JIT: the "take" idiom on an array field copies and leaks the whole buffer (4x web pages OOM)

- **Date:** 2026-11-23
- **Severity:** P1 (every web catalog page OOM-killed at device scale 4 under
  `SIMPLE_EXECUTION_MODE=jit`)
- **Status:** FIXED 2026-11-23 for the take idiom (seed `array_move.rs`). The
  general JIT array reclamation stays DEFERRED (see
  `seed_jit_array_copy_never_freed_2026-10-19.md`).
- **Area:** `src/compiler_rust/compiler/src/mir/lower/array_move.rs`

## Symptom

On the JIT, every 4x catalog render died at the 8 GB cap:

| run | before | after |
|---|---|---|
| tab-bar 1x, JIT, peak RSS | 6.24 GB, 14.0 s | 1.80 GB, 11.0 s |
| tab-bar 2x, JIT | 8.37 GB, OOM-killed | 1.87 GB, 11.2 s |
| tab-bar 4x, JIT | OOM-killed at 8 GB | 2.44 GB, 11.5 s, PPM written |
| html 4x, JIT | OOM-killed at 8 GB | 4.06 GB, 12.2 s, PPM written |
| tab-bar 1x, interpreter | 0.88 GB, 4.9 s | unchanged |
| forms-media 4x, JIT | OOM-killed at 8 GB | **8.34 GB of the 8.39 GB cap**, 33.5 s, PPM written (thin margin: font-blob copies below) |

At 4x, all 8 catalog pages complete under the JIT and match the interpreter byte for byte. Peak RSS: 2.4 to 4.2 GB, and 8.3 GB for forms-media.

## Root cause

The engine2d software backend takes its surface out of the field around a bulk
write, so that the interpreter can mutate a uniquely owned array
(`interpreter_field_array_write_span_copies_whole_array_2026-11-23`):

```simple
var surface = self.buf      # sw_buf_write_span, sw_fill_*
self.buf = []
surface.write_span(...)
self.buf = surface

var b: [u32] = []           # draw_image_blend
if not masked:
    b = self.buf
    self.buf = []
...b[i] = ...
if not masked:
    self.buf = b
```

On the JIT:
- `var surface = self.buf` is a `Let` from a place, so it emits `rt_array_copy`.
  `self` is a parameter, so Site A of `array_move.rs` never moves it.
- `self.buf = surface` / `self.buf = b` store a place, so each emits a second
  `rt_array_copy`.
- Nothing on the JIT lane frees an array, so every call leaked one or two
  whole surfaces: 5.5 MB at 1x, 22 MB at 2x, 87.5 MB at 4x.

Attribution used the seed's `SIMPLE_JIT_TRACE_ADDR` together with a scratch
probe (not committed) that logs the JIT return address of every large
`rt_array_copy`.

| page | function | copies | size |
|---|---|---|---|
| tab-bar 1x | `sw_buf_write_span` / `sw_fill_*` | 788 | 900x760 |
| tab-bar 2x, after the `Let` fix | `SoftwareBackend.draw_image_blend` (store back) | 113 | 1800x1520 |

## Fix

`collect_take_sites` (`array_move.rs`) recognises a take: `Let x = r.f` or
`x = r.f`, IMMEDIATELY followed by `r.f = []`.

1. **No copy on the `Let`** (`let_locals`). After the overwrite, `r.f` no
   longer holds the buffer. Mutating `x` is then equivalent to mutating `r.f`
   in place, which compiled code already does.
2. **No copy on the store back** (`field_store_locals`), when all of these hold:
   - every value `x` ever holds is a fresh literal or a take;
   - every other use of `x` is in place: the receiver of a builtin array method
     (`write_span`, `push`, `len`, ...), an index base, or the source of
     another array's `write_span`;
   - the store back is `x`'s only field store, its last mention, and outside
     any loop.

   The field is then the buffer's only holder.
3. **Excluded:** a root in `field_release_structs`. Its `r.f = []` may
   `rt_array_free` the old buffer, which `x` now holds.

## Evidence

- `src/compiler_rust/compiler/tests/jit_take_field_array_no_copy.rs`:
  - Base: `take_idiom_moves_without_copy_and_is_flat` FAILS with 2
    `rt_array_copy` in `Back.put`.
  - Fixed: 5/5 pass, including:
    - the conditional-assign take (the `draw_image_blend` shape);
    - the negative cases (a non-take `Let` keeps its copy; a take that
      escapes to another field before the store back keeps the store copy).
- Unchanged: `jit_array_field_release.rs` (8/8) and
  `jit_struct_array_field_leak.rs` (5/5).

## Still open

These sites are smaller or general. All of them need the refcount/ownership
redesign recorded in `seed_jit_array_copy_never_freed_2026-10-19.md`:

- **`val blob = self.selected_outline_blob`.** This is a `val` copy of a
  410,820-element font blob, in `FontRenderer.horizontal_kern_milli` /
  `get_glyph_advance_milli`, plus 42 copies in `parse_cmap_format4`/`12`. On
  tab-bar 2x that is 361 copies, independent of the device scale. On forms-media
  (2x probe) there are about 1,240 copies of 343 K to 415 K elements, which
  is about 4 GB retained. This is what holds forms-media 4x at the cap.
  Possible design: a `val` Let from a field place may alias (no copy) when no
  store to that field, and no call taking `self` mutably, happens while the
  `val` is live. Value semantics are only observable through such a write.
- **Callee-side parameter re-binds** such as `var out = fb` in
  `fb_fill_rows_const`, combined with `fb = f(fb, ...)` callers.
