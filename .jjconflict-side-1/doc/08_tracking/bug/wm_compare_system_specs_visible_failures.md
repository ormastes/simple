# wm_compare System Specs Visible Failures

Status: RESOLVED (2026-05-29)

After moving the former `test/sys/wm_compare` suite to
`test/system/wm_compare`, focused SPipe runs exposed existing system-spec
failures that should not be hidden by layout migration.

Passing moved specs:

- `test/system/wm_compare/html_compat_spec.spl`
- `test/system/wm_compare/emulated_capture_spec.spl`
- `test/system/wm_compare/famous_site_engine2d_backend_spec.spl`

Previously failing moved specs (all now fixed):

- `test/system/wm_compare/backend_parity_spec.spl`: 8/8 passing.
- `test/system/wm_compare/golden_gate_spec.spl`: 10/10 passing.
- `test/system/wm_compare/browser_shell_parity_spec.spl`: 6/6 passing.
- `test/system/wm_compare/electron_reference_parity_spec.spl`: 6/6 passing.

## Root Causes and Fixes

### A — backend_parity: parity booleans were false

Three layered bugs in `src/app/wm_compare/backend_parity.spl`:

1. **`render_framebuffer_baseline` returned the wrong array.** It called `fb.host_pixels()`
   twice — once to get a local `buf` alias, then again at the end as the
   return value. The second call returned the original unmodified
   `host_buffer`. Fix: return `buf` instead of the second `fb.host_pixels()`.

2. **`_pack_argb` produced truncated u8 values.** The expression
   `(a << 24) | (r << 16) | (g << 8) | b` with `u8` operands truncates
   each shifted component to u8 width in the interpreter (e.g. `255u8 <<
   24 = 0`), leaving only `b`. Fix: widen each component via `.to_u32()`
   before shifting.

3. **`_software_*` helpers mutating array function parameters was unreliable.**
   In certain interpreter contexts (observed inside `render_software_reference`'s for-loop),
   element writes to an array passed as a function parameter do not propagate
   back to the caller. Isolated tests showed the writes DO propagate in simple
   call patterns; the exact trigger within `render_software_reference`'s context was not
   isolated (not array size, not value magnitude alone). Fix: rewrite `_software_put`,
   `_software_clear`, `_software_fill_rect`, `_software_draw_char`, `_software_blend_rect`, and
   `_software_blend_one` to return the (possibly modified) array; callers reassign
   `buf = _software_*(buf, ...)`. This is the documented robust pattern for Simple
   arrays ("return modified array"). Also fixed `_software_blend_one` to widen `u8`
   operands via `.to_u32()` before arithmetic and use explicit `u32` literal
   suffixes to avoid overflow.

   TODO: file a concrete interpreter bug for the array-mutation-through-param
   unreliability so the root cause can be pinned. Repro: `render_software_reference` returning
   zeros for all pixels despite `_software_clear` writing correct values internally.

### B — golden_gate: drift-budget checks were false

The golden PPMs contained correct pixel data. `check_golden` compared them
against `render_framebuffer_baseline` output that was all-zeros due to bug A. Once bug A was
fixed, the fresh render matches the goldens and all drift-budget checks pass
without regenerating golden files.

### C — browser/electron parity: missing `blend_rect` on BrowserCompositorBackend

The original bug doc incorrectly said the missing method was `clear` — `clear`
was already present in the `impl CompositorBackend` block. The actual gap was
`blend_rect` (and the full `CompositorGlassCapable` surface): `BrowserCompositorBackend`
returned `nil` from `as_glass_capable()` and had no `impl CompositorGlassCapable` block,
so the browser and electron parity paths calling `bcb.blend_rect(...)` would fail at runtime.

Fix in `src/os/compositor/browser_compositor_backend.spl`:
- Changed `as_glass_capable()` to return `self` (the backend now genuinely
  implements glass-capable operations).
- Added `impl CompositorGlassCapable for BrowserCompositorBackend` with a
  real per-channel alpha-blend formula matching `_software_blend_one` exactly:
  `(src*a + dst*(255-a) + 128) >> 8` per R/G/B channel, result packed with
  full-opaque alpha. `blur_region` and `gradient_v` are no-op stubs (not
  exercised by any parity scene). `read_pixel` reads directly from `self.pixels`.
- Removed the duplicate `fill_rect` that appeared in both the class body and
  the `impl CompositorBackend` block.
