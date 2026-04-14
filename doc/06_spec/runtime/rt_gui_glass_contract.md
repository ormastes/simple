# `rt_gui_*` Glass-Effect Runtime Contract

> Date: 2026-04-14 · Scope: D2 glass subtrait migration · Status: draft

## 1. Scope

Pins down the observable pixel semantics of the four glass-effect runtime
symbols currently routed through C stubs: `rt_gui_blend_fill`,
`rt_gui_box_blur`, `rt_gui_gradient_v`, `rt_gui_read_pixel`. This contract is
the normative reference for the five per-backend native re-implementations
that D2 Phase 2 will land (Fb, Gpu, HostedWinit, Browser, Engine2D). Out of
scope: the wider `rt_gui_*` family (shadow, rounded_rect, text, wallpaper,
noise_blend, vignette, gradient_h/radial) — those are tracked separately and
remain C-only during Phase 2.

## 2. Symbol list

| Symbol | Simple signature (today, coords packed as `(hi<<32)|lo`) | Return | Buffer ownership | Caller tier |
|---|---|---|---|---|
| `rt_gui_blend_fill` | `(xy: u64, wh: u64, color: u64, alpha: u64)` | `0` (unused) | Writes active FB (Fb/Gpu) or winit buffer (Hosted). Caller owns lifetime. | backend-internal |
| `rt_gui_box_blur` | `(xy: u64, wh: u64, radius: u64, unused: u64)` | `0` (unused) | Reads+writes same buffer in-place; 3 scratch rows `blur_row_{r,g,b}[2048]` are static in C. | backend-internal |
| `rt_gui_gradient_v` | `(xy: u64, wh: u64, c1: u64, c2: u64)` | `0` (unused) | Writes only. No read. | backend-internal |
| `rt_gui_read_pixel` | `(x_y: u64, _, _, _) -> u64` | `u32` packed in low bits, 0 on out-of-range | Reads only. | app-level (query) |

## 3. Per-symbol semantics

### 3.1 `rt_gui_blend_fill`

- **C signature** — `examples/simple_os/arch/x86_64/boot/glass_render.c:348`:
  `RuntimeValue rt_gui_blend_fill(xy, wh, color, alpha)`
- **Simple signature** — `src/os/compositor/display_backend.spl:43`:
  `extern fn rt_gui_blend_fill(xy: u64, wh: u64, color: u64, alpha: u64)`
- **Pixel math** — srcOver with 8-bit integer math, rounded (glass_render.c:298):
  `result = (src*alpha + dst*(255-alpha) + 128) >> 8` per channel, then pack as
  `0xFF000000 | (r<<16) | (g<<8) | b`. Output alpha forced to `0xFF`.
- **Coordinate system** — origin top-left. `xy = (x<<32)|y`, `wh = (w<<32)|h`,
  unsigned 32-bit. Right/bottom edge **exclusive** — columns `[x, x+w)`, rows
  `[y, y+h)` (loops `for col<w` / `for row<h`, glass_render.c:365-371). Aligns
  with D1 `fill_rect` decision.
- **Color format** — pre-alpha storage: surface is always packed
  `0xFFRRGGBB` (glass_render.c:319 `0xFF000000u | (rr<<16) | (rg<<8) | rb`),
  i.e. **ARGB8888 with opaque output alpha, straight (non-premultiplied) RGB
  input**. No sRGB conversion; math is done in the stored gamma space.
- **Out-of-range** — `x >= fb_w || y >= SCREEN_H` → early `return 0` with no
  writes (glass_render.c:359). `x+w` / `y+h` overshoot is clamped to surface
  (`w = fb_w - x`, `h = SCREEN_H - y`). Negative coords: the C side casts to
  `uint32_t`, so negatives alias to huge positives and clamp out — callers
  must pre-clamp. The Simple wrappers use `clamp_u64` for this.
- **Threading** — not re-entrant. Writes a shared shadow buffer plus dirty
  rect (`dirty_mark`, glass_render.c:363). All four C symbols assume a single
  compositor thread.

### 3.2 `rt_gui_box_blur`

- **C signature** — `glass_render.c:554` — `rt_gui_box_blur(xy, wh, radius, _)`.
- **Simple signature** — `display_backend.spl:44`.
- **Pixel math** — **5-pass separable box blur H→V→H→V→H**
  (glass_render.c:575-579), each pass window size `d = 2*radius+1`, kernel is
  unweighted integer average `acc/d` per channel. Output alpha forced `0xFF`.
  Radius is clamped to `30` (glass_render.c:567), so effective kernel ≤ 61.
- **Coordinate system** — same packing as blend_fill. Same exclusive
  right/bottom. Edge handling: samples outside `[x, x+w)` / `[y, y+h)` are
  clamped to the edge (glass_render.c:475 `if left < x0: left = x0`; 483 mirror
  on right). This is "clamp-to-edge", not "wrap" and not "zero".
- **Color format** — ARGB8888, same as blend_fill.
- **Out-of-range** — `radius == 0 || w == 0 || h == 0` → no-op. Dirty rect
  **not marked** in the C path for blur (the five H/V passes each read+write
  in place, relying on a preceding `blend_fill` or `fill_rect` to have marked
  the rect). Native re-impls MUST mark the rect or keep their own dirty state.
- **Threading** — not re-entrant. Uses static scratch arrays
  `blur_row_r/g/b[2048]` (glass_render.c:455), which caps supported surface
  width at 2048 px.

### 3.3 `rt_gui_gradient_v`

- **C signature** — `glass_render.c:626`.
- **Simple signature** — `display_backend.spl:45`.
- **Pixel math** — vertical linear interpolation in stored color space.
  Per row `t = row / max(h-1, 1)`, per channel
  `c = c1 + (c2 - c1) * t` using **signed** 32-bit math (glass_render.c:326-329)
  to avoid unsigned underflow when a channel of `c2` is smaller than `c1`.
  Columns in the row are written with the same color (no horizontal blend).
  Output alpha forced `0xFF`.
- **Coordinate system** — exclusive right/bottom. `c1` paints row `y`, `c2`
  paints row `y+h-1`. Single-row rects collapse to `c1`.
- **Color format** — ARGB8888, straight.
- **Out-of-range** — same clamp behaviour as blend_fill. Zero `w` or `h`
  becomes a no-op via the `for row<h` / `for col<w` loops.
- **Threading** — not re-entrant.

### 3.4 `rt_gui_read_pixel`

- **C signature** — `glass_render.c:737`.
- **Simple signature** — `display_backend.spl:46`:
  `extern fn rt_gui_read_pixel(x_y: u64, unused1: u64, unused2: u64, unused3: u64) -> u64`.
- **Pixel math** — none. Returns the raw stored `u32` widened to `u64`, from
  the shadow buffer if ready else a `volatile` MMIO read
  (glass_render.c:193-199).
- **Color format** — ARGB8888; the top byte is `0xFF` by construction since
  all writers force it.
- **Out-of-range** — returns `0` for `x >= fb_w || y >= SCREEN_H`
  (glass_render.c:744). Negative coordinates alias to huge unsigned and also
  return `0`.
- **Threading** — reader, not re-entrant with writers on the same frame.

## 4. Per-backend compliance matrix

Rows = backend. Columns = `blend_fill` · `box_blur` · `gradient_v` · `read_pixel`. Cell = current state on main.

| Backend | blend_fill | box_blur | gradient_v | read_pixel |
|---|---|---|---|---|
| `FbCompositorBackend` (`display_backend.spl:120-138`) | compliant via C | compliant via C | compliant via C | compliant via C |
| `GpuCompositorBackend` (`display_backend.spl`) | **opt-out in Phase 1; native impl deferred to Phase 2** — no `impl CompositorGlassCapable`; callers degrade to opaque `fill_rect` via `glass_dispatch.cap_*`. | same | same | same |
| `HostedCompositorBackend` (`hosted_backend.spl:136-163`) | compliant via `rt_winit_buffer_blend_rect` (winit_ffi.rs:1507-1549) | compliant via `rt_winit_buffer_blur` (winit_ffi.rs:1551-1644), **3-pass** not 5-pass | compliant via `rt_winit_buffer_gradient_v` (winit_ffi.rs:1646-1687) | compliant via `rt_winit_buffer_read_pixel` (winit_ffi.rs:1487-1505) |
| `BrowserCompositorBackend` (`browser_compositor_backend.spl:95,129,214,238`) | compliant — pure Simple srcOver | **approximate** — HVHVH native, matches C pass count | compliant | compliant |
| `Engine2dCompositorBackend` (`compositor_engine2d.spl`) | **opt-out in Phase 1; native impl deferred to Phase 2** — no `impl CompositorGlassCapable`; extern block and glass method impls deleted. Callers degrade to opaque `fill_rect` via `glass_dispatch.cap_*`. | same | same | same |

### Arch-layer glass C source status

| Arch | `arch/<arch>/boot/glass_render.c` | Status |
|---|---|---|
| x86_64  | regular file (~3630 lines) — canonical source | compliant |
| arm64   | symlink → `../../x86_64/boot/glass_render.c` | compliant (shared) |
| riscv64 | symlink → `../../x86_64/boot/glass_render.c` | compliant (shared) |

Shared via symlink rather than a fork — the source is portable C (uses only
`<stdint.h>` and `<stddef.h>`, no inline asm, no x86 intrinsics, no
`__builtin_*` gating) and the arm64/riscv64 `RuntimeValue` ABI matches
(`int64_t`).

## 5. Divergences to fix in D2 Phase 2

- **GpuCompositorBackend**: replace all four C-stub calls with a virtio-GPU
  `TRANSFER_TO_HOST_2D`-aware path. Today's "works by coincidence" becomes
  broken the moment the virtio-GPU resource is not identity-mapped to the
  baremetal FB. Phase 1 decision is opt-out; Phase 2 needs a real impl.
- **Engine2dCompositorBackend**: the three `rt_gui_*` calls at
  `compositor_engine2d.spl:144,149,156` are incorrect when Engine2D wraps
  Vulkan, Metal, or a virtio-GPU non-identity resource. Phase 1 opts out
  (no `CompositorGlassCapable`); Phase 2 adds blend/blur primitives to
  `Engine2D.RenderBackend` and reimplements through them.
- **HostedWinit box_blur pass count**: C side does 5 passes (glass_render.c:575-579),
  winit side does 3 (winit_ffi.rs:1580). Either relax the contract ("≥3 passes,
  result within ε of 5-pass") or bring winit to parity. This contract
  currently says **3 passes minimum, 5 passes reference**; specs MUST NOT
  snapshot-compare blur output across backends without a tolerance.
- **Browser**: already re-implements HVHVH natively — covered. Keep.
- **arm64**: ~~`examples/simple_os/arch/arm64/boot/glass_render.c:348/554/626/737`
  is a full fork of the x86_64 source~~ — **resolved**: file is a symlink to
  `../../x86_64/boot/glass_render.c` (verified 2026-04-14), so there is one
  canonical translation unit and no lock-step hazard. The earlier "fork"
  characterisation was inaccurate (same line numbers because it is the same
  file via symlink).
- **riscv64**: ~~no `glass_render.c` exists at `examples/simple_os/arch/riscv64/boot/`~~ —
  **resolved**: added `arch/riscv64/boot/glass_render.c` as a symlink to
  `../../x86_64/boot/glass_render.c`, matching the arm64 precedent. Source
  is portable C (`stdint.h`/`stddef.h` only), so a single shared impl covers
  all three baremetal arches. D2 Phase 2 may still replace this with a
  `CompositorGlassCapable` native-Fb impl, but glass effects are no longer
  unresolved on riscv64.

## 6. Acceptance test outline

Suggested path: `test/unit/os/compositor/glass_contract_spec.spl`. Cases:

1. **blend_fill_srcover_math** — fill buffer with `0x00000000`, call `blend_rect(0,0,4,4, 0x00FF0000, 128)`, assert a sample pixel equals `0xFF7F0000` (± 1 LSB rounding — matches C `>>8` rounding via `+128`).
2. **blend_fill_exclusive_right** — buffer `10×10`, `blend_rect(2,2,3,3, 0x00FFFFFF, 255)`, assert pixel `(4,4)` written and pixel `(5,5)` untouched. Guards D1 exclusive semantics.
3. **blend_fill_oor_clip** — `blend_rect(-5,-5,3,3,...)` on a `4×4` buffer: no writes, no panic.
4. **box_blur_edge_clamp** — 1-pixel white dot at `(5,5)` on black `11×11`; blur radius 2; assert `(0,5)` still near-black (clamp-to-edge should not bleed past edge 0).
5. **gradient_v_endpoints** — `gradient_v(0,0,1,4, 0x00000000, 0x00FFFFFF)`; assert row 0 = `0xFF000000`, row 3 = `0xFFFFFFFF`, row 1 = `0xFF555555`, row 2 = `0xFFAAAAAA` (within ±1).
6. **gradient_v_single_row** — `h=1`: pixel equals `c1` with forced top alpha.
7. **read_pixel_oor** — returns `0` for negative and out-of-bounds coords, not a read panic.
8. **capability_probe** — `Engine2dCompositorBackend.as_glass_capable()` returns `None`; `FbCompositorBackend`, `HostedCompositorBackend`, `BrowserCompositorBackend` return `Some`.

## 7. References

- C reference impl (x86_64, canonical): `examples/simple_os/arch/x86_64/boot/glass_render.c:298,319,348,554,575-579,626,737`.
- C reference impl (arm64): `examples/simple_os/arch/arm64/boot/glass_render.c` → symlink to x86_64 canonical source.
- C reference impl (riscv64): `examples/simple_os/arch/riscv64/boot/glass_render.c` → symlink to x86_64 canonical source.
- Hosted winit analogue: `src/compiler_rust/compiler/src/interpreter_extern/winit_ffi.rs:1487,1507,1551,1646`.
- Simple-side externs and callers: `src/os/compositor/display_backend.spl:43-46,120-138,221-240`; `src/os/compositor/compositor_engine2d.spl:58-60,137-157`; `src/os/compositor/glass_effects.spl:11-18`.
- Hosted Simple-side: `src/os/compositor/hosted_backend.spl:23-26,136-163`.
- Browser Simple-side: `src/os/compositor/browser_compositor_backend.spl:95,129,214,238`.
- Plan: `doc/03_plan/sys_gui/d2_glass_subtrait_migration.md`, `doc/03_plan/sys_gui/d2_unresolved_loose_ends.md` §B.
- Upstream contracts: `doc/04_architecture/gui_layer_contract.md`; `doc/03_plan/sys_gui/gui_layer_contract_fix_plan.md` (D1 fill_rect exclusive-edge decision).
