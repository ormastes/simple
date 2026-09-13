# border-radius corners are not anti-aliased (2026-09-12)

**Status:** FIXED (2026-09-12, second pass). Both painters anti-alias the
corner. The Engine2D half, previously reverted and blocked, landed as a
coordinated CPU + Vulkan + Metal shared-raster change — see "Unblocked: the
coordinated shared-raster change" below. The "Why the Engine2D half was
reverted" section is retained as history; its unblock condition is now met.
**Component:** pure-Simple web renderer paint primitives; Engine2D emulation
backend.

## Defect

Both rounded-corner rasterizers used a hard in/out membership test, so a corner
stepped straight from fill to background with no intermediate value anywhere.
Chrome ramps 234→233→229→223→255 across the same arc. On a 160x160 fixture with
a 100x100 black box at (20,20) and `border-radius:40px`, Simple produced exactly
**2 distinct colours** over 25,600 px.

- Framebuffer painter:
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_paint_primitives.spl`,
  `fb_rounded_rect_corners_opacity_clip` — `inside = dx*dx + dy*dy <= r*r`.
- Engine2D painter: `src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`,
  `_emu_corner_arc` — a midpoint-circle span fill. This is the painter the
  cpu_simd web lane actually reaches (`backend_software.spl:547` delegates
  `draw_rounded_rect` to `emu_draw_rounded_rect`).

`simple_web_css_box_effects.spl:82` parses the radius correctly; the defect is
in the painters.

## Fix (framebuffer painter — landed)

Replaced the boolean with an analytic coverage in 0..256:
`cov = clamp(r*256 + 128 - dist256, 0, 256)`, where `dist256` is an integer
Newton square root of the distance in 1/256-px units. The ramp is one pixel
wide and crosses 1/2 exactly on the arc. New helpers `_isqrt_i64`,
`_corner_coverage256`, `_blend_alpha256` in the same file.

**Amended in the second pass (2026-09-12).** The first version computed
`dist256 = isqrt(sq * 65536)` from `sq = dx*dx + dy*dy`, i.e. it measured from
the arc-centre **pixel**, which puts the arc half a pixel too far out. That is
invisible to this painter's own spec (which only asserts that *some* pixels are
intermediate) but is wrong, and the Engine2D AA spec's AC-1 coordinates detect
it. `_corner_coverage256` now uses the `(2*dx+1)^2 + (2*dy+1)^2` / `* 16384`
pixel-centre form, so it is genuinely the same formula as the Engine2D lanes
rather than merely similar. `border_radius_antialias_spec` stays GREEN (1/1)
across the change.

## Why the Engine2D half was reverted

The analytic-coverage version of `emu_draw_rounded_rect` was written and
**verified to work** — the same fixture rendered 23 distinct colours instead of
2, with a correct ramp along the whole arc (measured values 230/179/134/96/64/38/19/6
across one row).

It was reverted because
`test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` pins the
CPU fill against an independent Simple replica of the GPU
`kernel_draw_rounded_rect` **band/corner membership formula** — an explicit
CPU↔GPU parity contract (see that file's comment at :822-830). The change took
it from 1 pre-existing failure to 5:

```
✗ matches the band/corner formula on the original bug-doc fixture (radius=6, ...)
✗ matches the band/corner formula when radius == min(w,h)/2 (stadium shape)
✗ matches the band/corner formula on a narrow strip (h < 2*radius ...)
✗ matches the band/corner-fill+blend formula on a semi-transparent fill ...
```

Those oracles are not stale — they assert cross-backend agreement. Landing
corner AA on the CPU alone would make the CPU disagree with the Metal and Vulkan
kernels. The unblock condition is a **coordinated shared-raster change**: the
analytic coverage formula must land in `kernel_draw_rounded_rect` (Metal MSL and
Vulkan) and in the parity spec's replica in the same change. Those backends were
owned by another lane at the time of this fix, so it is filed rather than forced.

## Unblocked: the coordinated shared-raster change (2026-09-12, second pass)

The unblock condition stated above — "the analytic coverage formula must land
in `kernel_draw_rounded_rect` (Metal MSL and Vulkan) and in the parity spec's
replica in the same change" — is met.

### One formula, defined once

The **SHARED ROUNDED-RECT CORNER COVERAGE FORMULA v1** is defined in a single
comment block above `emu_draw_rounded_rect` in
`src/lib/gc_async_mut/gpu/engine2d/backend_emu.spl`. Integer only, no `f64`,
no `sqrt()`:

```
dx, dy  = pixel offset from the corner's arc-centre pixel, positive AWAY
          from the rect interior (both >= 0 inside a corner box)
q       = (2*dx + 1)^2 + (2*dy + 1)^2        # 4x the squared distance
dist256 = isqrt(q * 16384)                   # 256 * distance, floored
cov256  = clamp(r*256 + 128 - dist256, 0, 256)
a_eff   = (alpha_byte(color) * cov256) / 256
```

`isqrt` is `floor(sqrt(v))` by integer Newton. That value is
**algorithm-independent**, so any exact integer square root agrees across
lanes; a float `sqrt` is the one thing that can break bit-parity, so no lane
uses one.

The `2*d + 1` terms are load-bearing: the arc centre is the continuous point
`(x+r, y+r)` and a pixel centre is `(px+0.5, py+0.5)`, so the true offset is
`dx + 0.5`. Doubling clears the halves, which makes `q` four times the squared
distance — hence `* 16384` rather than `<< 16`. Measuring from the arc-centre
*pixel* instead (the first thing tried, and what the already-landed framebuffer
painter does) pushes the whole arc outward by half a pixel; it looks plausible
in isolation but puts the ramp in the wrong place, and
`border_radius_antialias_engine2d_spec`'s AC-1 coordinates detect exactly that.

Coverage is applied by modulating the **source alpha byte only**; the blend
itself is the unchanged `blend_src_over` that this repo's parity rows already
prove bit-exact CPU<->Metal. So the only genuinely new shared quantity is
`a_eff`.

### Exclusive regions were a precondition, not a cleanup

The rect is now partitioned into **seven disjoint regions** — a full-height
middle band, two side bands, four `r x r` corner boxes — so every pixel is
blended exactly once. Previously the corner arcs overlapped the side bands at
the seam, and `kernel_draw_rounded_rect`'s comment argued *for* that overlap:
bit-exactness with the CPU required replaying all seven primitives in order,
because an `alpha<255` fill was composited twice on the seam rows.

That reasoning was correct for a hard in/out test and is fatal for AA: a
partial-coverage pixel blended twice is simply wrong. Exclusivity therefore had
to land with the coverage, on every lane at once. The stale rationale in the
MSL comment was rewritten rather than left standing next to code contradicting
it.

### Which lane is which

| lane | where | how |
|---|---|---|
| CPU / software | `backend_emu.spl` `emu_draw_rounded_rect` | `backend_software.spl:547` delegates here |
| **Vulkan** | **the same function** | `backend_vulkan.spl:1201-1208` `draw_rounded_rect` delegates to `emu_draw_rounded_rect`. The AA lives in the **emu expansion** (census R7), reaching the GPU as real `draw_rect_filled` dispatches carrying the modulated alpha. The dedicated `rounded_rect` SPIR-V kernel is **deliberately unwired** — it fills a plain rect and ignores the radius (`vulkan_raster_kernels_noop_and_divergent_2026-06-17`), so **no SPIR-V was regenerated and no `rounded_rect.comp` was added**. |
| Metal | `backend_metal_msl.spl` `kernel_draw_rounded_rect` | per-pixel transliteration of the same formula |
| parity oracle | `engine2d_shared_raster_parity_spec.spl` | an **independent** re-implementation (`_rr_isqrt_ref` / `_rr_cov256_ref` / `_rr_modulate_alpha_ref`), deliberately NOT importing the production helpers — importing them would make the spec assert `f(x) == f(x)` |

Vulkan dispatch cost: per corner row the expansion now emits one coalesced
full-coverage span plus at most a couple of partial pixels, versus the old two
spans per midpoint step. `cov256` is monotonically non-increasing in `dx` for a
fixed `dy`, which is what makes the full-coverage run contiguous and coalescable.

## Specs

- `test/unit/browser_engine/border_radius_antialias_spec.spl` — GREEN.
  Calls `fb_rounded_rect_corners_opacity_clip` directly on a 40x40 buffer:
  exact fill well inside the arc, untouched background at the corner tip, and at
  least 8 pixels in the corner tile that are neither (a hard in/out test produces
  exactly zero).
- `test/unit/browser_engine/border_radius_antialias_engine2d_spec.spl` — **now
  GREEN, 3/3, and the `# @tag:in-development` tag is removed.** Renders the HTML
  fixture through the cpu_simd lane and asserts an intermediate value on the arc
  at (31,31) and (53,20), exact fill at (60,60), exact background at (21,21), and
  no notch on the tangent edges. It was 1-of-3 RED; the failing example was
  exactly the AA assertion, and it is the spec that caught the half-pixel centre
  error described above. **Not weakened** — the assertions are unchanged from
  when they were RED; only the docstring and the tag moved.

- `test/02_integration/rendering/engine2d_shared_raster_parity_spec.spl` — carries
  BOTH oracles for this fix, deliberately separated:
  - context **"Rounded-rect corner ANTI-ALIASING, shared formula v1
    (2026-09-12)"** — 8 new rows, an **ABSOLUTE** oracle. Hand-derived coverage
    at r=6: `(0,0) -> 256`, `(4,3) -> 205`, `(4,4) -> 35`, `(5,5) -> 0`, with the
    arithmetic spelled out in the comment. The monotone 256 -> 205 -> 35 -> 0
    sequence is itself an oracle: a formula that ramped the wrong way, or was
    flat, would still satisfy a bare `0 < v < 256` check.
  - context **"Rounded-rect FILL parity fix (2026-07-07, AA'd 2026-09-12)"** —
    the 5 pre-existing rows, a **PARITY** oracle, updated to the new shared
    formula and still passing.

  The split is the point: parity alone would be satisfied by three lanes
  agreeing on a WRONG formula ("MATCH != correct",
  `.claude/skills/spipe/SKILL.md` § false green), so the absolute rows exist to
  pin the formula itself.

Both unit specs mirrored into `test/01_unit/browser_engine/` (byte-identical).

## Evidence

Runner: `/Users/ormastes/simple/build/cargo-r2/release/simple`
(39368072 bytes, mtime 1789171430), `SIMPLE_EXECUTION_MODE=interpreter
SIMPLE_TIMEOUT_SECONDS=0`.

- `border_radius_antialias_engine2d_spec` — `3 examples, 0 failures`
  (was 1 failure).
- `engine2d_shared_raster_parity_spec` — `48 examples, 1 failure`. The single
  failure is the **pre-existing** `draw_line (thick) diverges — sw
  parallel-offset lines vs emu per-point txt square [canonical: design review]`,
  unrelated to rounded rects and present before this change.

**Cascade — no regression in the specs that also draw rounded rects.** Each was
run with the change in place and again with `backend_emu.spl` /
`backend_metal_msl.spl` reverted to `HEAD`; the failure sets are identical
byte-for-byte, so the reds below are pre-existing and unrelated.

| spec | with fix | at HEAD |
|---|---|---|
| `test/02_integration/rendering/engine2d_primitives_spec.spl` | 24 ex, **0 fail** | 0 fail |
| `test/unit/lib/gpu/engine2d/backend_software_primitives_spec.spl` | 6 ex, **0 fail** | 0 fail |
| `test/03_system/check/engine2d_software_offscreen_dispatch_spec.spl` | 3 ex, 3 fail | 3 fail (pre-existing) |
| `test/03_system/check/cpu_simd_render_scale_contract_spec.spl` | 13 ex, 7 fail | 7 fail (pre-existing) |

The two specs that actually exercise rounded-rect rasterization are the first
two, and both are fully green.

**Sabotage check (the parity rows are load-bearing, not decorative).**
Perturbing the CPU coverage constant alone — `+ 128` -> `+ 64` in
`_emu_corner_cov256`, leaving Metal and the oracle untouched:

| state | parity spec |
|---|---|
| fixed | 48 examples, **1** failure (the pre-existing draw_line row) |
| CPU formula sabotaged (`+128` -> `+64`) | 48 examples, **5** failures — the 4 rounded-rect parity rows all fire |
| restored | 48 examples, **1** failure |

The 1 -> 5 -> 1 triple reproduces the exact signature from the original revert.
A second, independent confirmation: with `backend_emu.spl` and
`backend_metal_msl.spl` reverted to `HEAD` while the spec carried the new
formula, the same 5 failures appeared — i.e. the contract binds in both
directions.

## Gaps, stated rather than papered over

1. **Metal is COMPILE-verified but not device-verified.** The MSL was extracted
   from `_engine2d_msl()` and compiled offline:
   `xcrun -sdk macosx metal -c e2d.metal -o e2d.air` -> **rc=0**, no
   diagnostics, 33,248-byte `.air` (Apple metal 32023.864, target
   air64-apple-darwin25.5.0). The exit status was read into a variable on the
   line after the invocation, never through a pipe. Non-vacuity control:
   injecting `NOT_A_TYPE zz = 1;` into `_rr_cov256` makes the same command
   return **rc=1** with 2 errors, so the compile discriminates. This closes the
   "an MSL syntax slip ships silently" risk; it does NOT prove the kernel's
   output, only that it builds.
2. **No Metal device evidence on this host.** The device harness
   `test/02_integration/rendering/engine2d_gpu_offload_evidence.spl` reports
   `GPU_OFFLOAD: skip reason=metal-unavailable backend=cpu` on this Apple M4
   under the interpreter, so the `rounded_rect` row — including its
   `0x80FFFFFF` semi-transparent fill, the one case where exclusive-vs-overlap
   actually differs — did **not** execute against a real device. The Metal
   kernel is therefore verified only against the Simple-level oracle, exactly
   as the pre-existing header of that harness already warns for this op. This
   matches the standing "no Metal device evidence exists on this mac" finding;
   it is not a regression introduced here, but it IS an open gap for this fix.
   `test/02_integration/rendering/metal_msl_pipeline_spec.spl` likewise reports
   `7 examples, 5 failures` — **identical at the pre-change baseline** (verified
   by reverting `backend_metal_msl.spl` to `HEAD~1`), all device-dependent rows.
3. **No Vulkan device evidence either**, for the same reason —
   `native_shader_backend_readback_matrix_spec` fails on this host with
   `semantic: called unwrap_err on Ok`, and that failure **reproduces at
   `HEAD`** (verified by reverting both source files), so it is pre-existing
   harness/environment breakage, not a divergence caused by this change.
   Note that the Vulkan lane shares the CPU code path, so the CPU-lane
   evidence covers its *arithmetic*; what is unproven is the dispatch round trip.
4. **CUDA, ROCm and Intel are NOT twins and were not changed.** Each carries
   its own hand-written copy of the old hard-membership test —
   `backend_cuda_kernels.spl` (inline PTX), `backend_rocm_kernels.spl` (HIP),
   `backend_intel_kernels.spl` (OpenCL). `backend_cuda.spl:923` already carries
   a standing "KNOWN PARITY NOTE" that its rounded-rect kernel is a filled
   interior test. Those three lanes now additionally lack corner AA. This is
   pre-existing divergence, deliberately left alone (hand-written PTX is a
   high-risk edit with no device here to verify it) rather than silently
   claimed as covered by "one formula".
