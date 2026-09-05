# `emu_*` shape decomposition emits ONE GPU DISPATCH PER PIXEL on GPU backends

Filed 2026-09-03. Status: OPEN, root cause located and measured. Severity: HIGH
(performance only — output is bit-exact, proven below).

## Symptom

On the Engine2D **vulkan** backend, primitives that delegate to the shared
`emu_*` CPU code are 26-144x slower than the **cpu** backend running *the same
`emu_*` code*:

| Primitive | cpu | vulkan | ratio |
|---|---|---|---|
| whole 38-primitive showcase | 32 ms | 449-513 ms | ~16x |
| `draw_circle` | 11 us | 1,590 us | **144x** |
| `draw_circle_thick` | 98 us | 9,062 us | 92x |
| `draw_radial_gradient` | 774 us | 63,846 us | 82x |
| `draw_ellipse` | 23 us | 1,689 us | 73x |
| `draw_bezier` | 40 us | 2,200 us | 55x |
| `draw_arc` | 77 us | 2,012 us | 26x |

Identical source, two orders of magnitude apart. That is the whole finding: the
cost is not in the shape maths.

**Scope, corrected.** This is NOT "vulkan is slower at everything" — an earlier
draft said so, read off a top-by-ratio listing that showed only losers. By
tier: GPU-native 12 primitives, vulkan **faster on 8 of 12** (`clear` 33x
faster, `draw_triangle_filled` 27x, `draw_line` 7.5x); CPU `emu_*` 18
primitives, vulkan slower on **18 of 18**, 42.7x in aggregate. The GPU lane is
fast where it is implemented and catastrophic where `emu_*` decomposes to
per-pixel dispatches — which is precisely this defect.

## Root cause

`emu_*` does not write pixels. It decomposes a shape into calls back into the
backend's own `draw_rect_filled` — and for outlines, **one 1x1 rect per pixel**
(`backend_emu.spl:97-125`):

```simple
core.draw_rect_filled(cx + x, cy + y, 1, 1, color)
core.draw_rect_filled(cx - x, cy + y, 1, 1, color)
...   # 8 such calls per midpoint iteration
```

On the cpu backend `draw_rect_filled` is a memory write (~ns). On the vulkan
backend it is a **GPU compute dispatch** — pipeline bind, push constants,
`vkCmdDispatch`. A radius-35 circle outline is ~200 pixels, so ~200 dispatches
for one `draw_circle`. 200 x ~8 us ≈ 1.6 ms, which is what is measured.

**31 call sites** in `backend_emu.spl` emit a 1x1 `draw_rect_filled`.

The span/no-span split predicts the ratios exactly:
`emu_draw_circle_filled` (`:127-146`) emits **one rect per ROW**
(`2*half+1` wide), i.e. ~2r dispatches, and filled shapes measure ~25x rather
than ~144x. Per-pixel decomposition is the difference.

## Why no existing gate caught it

Every gate compared PIXELS, and the pixels are correct.
`scripts/check/check-engine2d-backend-parity.shs` reports
**PASS — 1,920,000 bytes across 38 primitives, 0 differing** between cpu and
vulkan, and `check-vulkan-2d-bit-diff.shs` reports the Simple output
byte-identical to the C Vulkan reference. This is a pure cost defect behind
correct output.

## Fix direction (not yet landed — blast radius)

The fix belongs in the BACKEND, not in `emu_*`: a 1x1 (or small-area)
`draw_rect_filled` on a GPU backend should accumulate into the host mirror and
upload once, instead of paying a dispatch each. That inverts which side owns
the framebuffer for those writes, so it is an architectural change, not a
patch — deliberately not attempted blind.

It is, however, now *safe to attempt*: both gates above are calibrated (a
single flipped byte is caught and localised), so any such change is provable
pixel-identical before it lands.

Cheaper partial: give the outline algorithms a span-emitting plotter, matching
what `emu_draw_circle_filled` already does. Reduces dispatches without changing
which side owns the buffer.

## Fixes LANDED

| Function | before (vulkan) | after (vulkan) | speedup | technique |
|---|---|---|---|---|
| `emu_draw_circle_thick` | 9,955 us | 1,176 us | **8.5x** | span form (one rect per row) |
| `emu_draw_linear_gradient_stops` | ~87,700 us | ~1,100 us | **~80x** | run-length merge within each row |
| `emu_draw_radial_gradient` | ~76,700 us | ~42,000 us | ~1.8x | run-length merge within each row |
| `emu_draw_radial_gradient_stops` | ~59,400 us | ~37,400 us | ~1.6x | run-length merge within each row |

All verified pixel-identical against a pre-change golden framebuffer (`cmp`
exit 0), with the parity gate PASS at 38 primitives.

**Attribution note:** the three gradient rewrites were produced by a delegated
agent. They were swept into commit `eb458b5a441` ("feat(lint): G2DP003 ...") by
a `git add -A`, so that commit's message does not describe 52 of the lines it
carries. Recorded here rather than rewritten, since the branch history is
shared.

### Why the two RADIAL gradients only improve ~1.6-1.8x — a real limit

Run-length merging only helps where consecutive pixels quantize to the SAME
colour. For the LINEAR stop gradient the position parameter is linear in `px`,
so long spans share one 8-bit colour and the merge wins ~80x. For the RADIAL
gradients the colour is a function of `dist = isqrt(px*px + py*py)`, which
changes at almost every pixel near a row's centre; long runs only form near
the circle's left/right extremities. **This is inherent to run-merging, not a
missed optimisation.** Closing the remaining radial gap needs either a real GPU
gradient shader (making these GPU-native rather than `emu_*`) or a per-row
analytic computation of exact run boundaries from the distance function.

## Fixes ATTEMPTED, MEASURED, and REVERTED (do not retry blind)

- **`val copy = self.host_buf` instead of the per-element copy loop** at
  `backend_vulkan.spl:1504`. `runtime/src/value/collections.rs:5181` states an
  array-typed binding lowers to the native `rt_array_copy`, so this looked like
  a strict win. Measured: readback **2.57 ms/frame -> 11.1 ms/frame, a 4x
  REGRESSION**. Reverted. Whatever `rt_array_copy` does for a packed `[u32]` on
  this path is slower than the interpreted per-element loop it replaces — worth
  its own investigation.

## Hypotheses measured and DISPROVED for the related one-time cost

`draw_rect_blend` costs ~330-350 ms on its FIRST call and 4.1 ms on every call
after (79x cheaper), so that is one-time initialisation, not per-call cost.
Its site is **not** located. Ruled out by measurement, not argument:
per-frame staging-buffer allocation (7 us), per-frame `[u32]` allocation
(351 us), and the `_pixels_to_bytes` upload at `backend_vulkan.spl:1086`
(its trace never fires on this path).

## Reproduce

```sh
sh scripts/check/check-engine2d-backend-parity.shs   # PASS: pixels agree
# per-primitive costs, both backends:
grep '^feat ' build/engine2d-backend-parity/cpu.log
grep '^feat ' build/engine2d-backend-parity/vulkan.log
```
