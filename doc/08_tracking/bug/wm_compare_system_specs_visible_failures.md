# wm_compare System Specs Visible Failures

Status: RESOLVED (2026-05-29)

After moving the former `test/sys/wm_compare` suite to
`test/system/wm_compare`, focused SPipe runs exposed existing system-spec
failures that should not be hidden by layout migration.

Passing moved specs:

- `test/system/wm_compare/html_compat_spec.spl`
- `test/system/wm_compare/emulated_capture_spec.spl`
- `test/system/wm_compare/famous_site_engine2d_backend_spec.spl`

Previously failing moved specs (now fixed):

- `test/system/wm_compare/v1_v2_parity_spec.spl`: 8/8 passing.
- `test/system/wm_compare/golden_gate_spec.spl`: 10/10 passing.
- `test/system/wm_compare/v1_v3_parity_spec.spl`: 6/6 passing.
- `test/system/wm_compare/v1_v4_parity_spec.spl`: 6/6 passing.

## Root Causes and Fixes

### A — v1_v2_parity: parity booleans were false

Three layered bugs in `src/app/wm_compare/v1_v2_parity.spl`:

1. **`render_v1` returned the wrong array.** It called `fb.host_pixels()`
   twice — once to get a local `buf` alias, then again at the end as the
   return value. The second call returned the original unmodified
   `host_buffer`. Fix: return `buf` instead of `fb.host_pixels()`.

2. **`_pack_argb` produced truncated u8 values.** The expression
   `(a << 24) | (r << 16) | (g << 8) | b` with `u8` operands truncates
   each shifted component to u8 width in the interpreter (e.g. `255u8 <<
   24 = 0`), leaving only `b`. Fix: widen each component via `.to_u32()`
   before shifting.

3. **`_v2_*` helpers mutated a function-parameter copy, not the caller's
   array.** The interpreter uses value semantics for `[u32]` parameters
   when stored values exceed the i32 range — writes inside the helper do
   not propagate back. Fix: rewrite all `_v2_put`, `_v2_clear`,
   `_v2_fill_rect`, `_v2_draw_char`, `_v2_blend_rect`, and `_v2_blend_one`
   to return the modified array; callers reassign `buf = _v2_*(buf, ...)`.
   Also fixed `_v2_blend_one` to widen `u8` operands via `.to_u32()` before
   arithmetic and use explicit `u32` literal suffixes to avoid overflow.

### B — golden_gate: drift-budget checks were false

The golden PPMs were written correctly (matching the expected pixel values),
but `check_golden` compared them against `render_v1` output that was all-zeros
due to bug A. Once bug A was fixed, the fresh render matches the goldens and
all drift-budget checks pass without needing to regenerate golden files.

### C — v1_v3 / v1_v4: missing `blend_rect` on BrowserCompositorBackend

The bug doc incorrectly identified the missing method as `clear` — `clear`
was already present in the `impl CompositorBackend` block. The actual missing
piece was `blend_rect` (and the other `CompositorGlassCapable` methods):
`BrowserCompositorBackend` returned `nil` from `as_glass_capable()` and had
no `impl CompositorGlassCapable` block.

Fix in `src/os/compositor/browser_compositor_backend.spl`:
- Changed `as_glass_capable()` to return `self` instead of `nil`.
- Added `impl CompositorGlassCapable for BrowserCompositorBackend` with a
  real per-channel alpha-blend formula matching `_v2_blend_one` exactly:
  `(src*a + dst*(255-a) + 128) >> 8` per R/G/B channel, result packed
  with full-opaque alpha. `blur_region` and `gradient_v` are no-op stubs
  (not exercised by any parity scene).
- Removed a duplicate `fill_rect` method that appeared in both the class
  body and the `impl CompositorBackend` block.
