# BUG: engine2d CPU↔Metal primitive rasterization diverges (line/circle/rounded_rect)

Status: resolved (2026-06-05); re-verified + rounded_rect_outline fixed (2026-07-02)

- id: engine2d-cpu-metal-primitive-raster-divergence
- date: 2026-06-03
- area: rendering / engine2d
- severity: medium
- status: resolved (2026-06-05); re-verified + rounded_rect_outline fixed (2026-07-02)

## Update (2026-07-02): gate was a false-skip; rounded_rect_outline diverged; both fixed

Re-running the parity gate (`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`)
on macOS found it was **not actually asserting anything**: it printed
`pass (not-macos-skipped)` even on real macOS hardware. Root cause was a
global-symbol collision in the interpreter, not a Metal bug:
`test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl` explicitly
imports `is_macos` from `std.nogc_sync_mut.env.platform` (which has a
`uname -s` fallback), but `backend_metal.spl` transitively imports a
same-named `is_macos`/`detect_os` from `std.gc_async_mut.env.platform` →
`std.nogc_async_mut.env.platform` (no `uname -s` fallback, OSTYPE-only). The
interpreter's symbol table is not properly module-scoped, so whichever
definition the dependency graph registers first silently wins over the
file's own explicit import. In a non-interactive shell where `OSTYPE` isn't
an exported env var, the async `detect_os()` returned `"unknown"` — so
`is_macos()` returned `false` **both** for the harness's own macOS gate
*and*, more importantly, inside `MetalBackend` itself (`backend_metal.spl`
gates real GPU dispatch on `is_macos()` at lines 181/238), which made every
scene silently fall back to the CPU mirror (`gpu_frame_complete=false`,
reported as `metal-fell-back-to-cpu-mirror`) — a real, reproducible false
green/false-skip, not a Metal rendering bug.

Fixed by adding the same `uname -s` fallback already present in
`std.nogc_sync_mut.env.platform.detect_os()` to
`src/lib/nogc_async_mut/env/platform.spl::detect_os()` (this file, not
`backend_metal.spl`, was the actual bug — it's a plain platform-detection gap
that affects any caller landing on the async family's `is_macos()`). Also
hardened the harness's own gate (`_harness_is_macos()` in
`engine2d_cpu_metal_parity_run.spl`) with a locally-named, non-colliding
implementation so the gate doesn't regress the same way again even if
another transitive import shadows `is_macos` in the future.

With genuine GPU dispatch restored (`gpu_ok=true` on every scene), a NEW
divergence surfaced that predates this change: `draw_rounded_rect_outline`
(the thick, multi-stroke outline variant with a `thickness` parameter,
distinct from the already-fixed plain `draw_rounded_rect`) mismatched
110/1024 pixels. Its MSL kernel (`kernel_draw_rounded_rect_outline` in
`backend_metal_msl.spl`) implemented the corners as a filled-annulus distance
test (`ri_sq <= dx²+dy² <= ro_sq`), matching a *different*, unused CPU
function (`emu_draw_rounded_rect_outline` in `backend_emu.spl`). The actual
CPU reference used by `SoftwareBackend`/`CpuBackend`
(`backend_software.spl::draw_rounded_rect_outline`) instead loops over each
of the `thickness` offsets and draws a **thin 1px midpoint-circle ring**
(`sw_corner_arc`, the same algorithm already used for plain circles) at
radius `r-off` — a stack of thin rings is not the same shape as one filled
annulus, especially for small `r` relative to `thickness`. Fixed by
rewriting the MSL kernel's corner-handling to replay the same midpoint-circle
recurrence (`_rr_ring_hit` helper) per offset, and added the CPU's
`if thickness > r+1: thickness = r+1` clamp that the kernel was missing.

### Evidence (2026-07-02, macOS arm64, real hardware, genuine GPU readback)

Before (gate falsely skipping — no real assertion at all):
```
engine2d-cpu-metal-parity: pass (not-macos-skipped)
```

After fixing the `is_macos()` platform-detection bug (GPU dispatch now real,
`gpu_ok=true` everywhere), but before fixing `rounded_rect_outline`:
```
clear: MATCH mismatches=0/1024 gpu_ok=true
rects: MATCH mismatches=0/1024 gpu_ok=true
gradient: MATCH mismatches=0/1024 gpu_ok=true
line: MATCH mismatches=0/1024 gpu_ok=true
circle: MATCH mismatches=0/1024 gpu_ok=true
rounded_rect: MATCH mismatches=0/1024 gpu_ok=true
triangle: MATCH mismatches=0/1024 gpu_ok=true
rounded_rect_outline: DIVERGE mismatches=110/1024 gpu_ok=true first_idx=3 cpu=4294936576 metal=4278190080
PARITY: fail failures=1
```

After fixing `kernel_draw_rounded_rect_outline` (all 8 scenes, official gate):
```
$ sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
engine2d-cpu-metal-parity: pass (cpu-metal-bitexact)
```
`build/engine2d-cpu-metal-parity-evidence/parity.env`:
```
engine2d_cpu_metal_parity_status=pass
engine2d_cpu_metal_parity_reason=cpu-metal-bitexact
engine2d_cpu_metal_parity_clear=clear: MATCH mismatches=0/1024 gpu_ok=true
engine2d_cpu_metal_parity_rects=rects: MATCH mismatches=0/1024 gpu_ok=true
engine2d_cpu_metal_parity_gradient=gradient: MATCH mismatches=0/1024 gpu_ok=true
engine2d_cpu_metal_parity_line=line: MATCH mismatches=0/1024 gpu_ok=true
engine2d_cpu_metal_parity_circle=circle: MATCH mismatches=0/1024 gpu_ok=true
engine2d_cpu_metal_parity_rounded_rect=rounded_rect: MATCH mismatches=0/1024 gpu_ok=true
engine2d_cpu_metal_parity_rounded_rect_outline=rounded_rect_outline: MATCH mismatches=0/1024 gpu_ok=true
engine2d_cpu_metal_parity_triangle=triangle: MATCH mismatches=0/1024 gpu_ok=true
```

Files changed:
- `src/lib/nogc_async_mut/env/platform.spl` — added `uname -s` fallback to
  `detect_os()` (root fix for the false-skip / false-CPU-fallback).
- `test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl` —
  replaced the collision-prone `is_macos()` call with a locally-named
  `_harness_is_macos()` so the gate's own macOS check can't be shadowed by a
  same-named symbol pulled in transitively.
- `src/lib/gc_async_mut/gpu/engine2d/backend_metal_msl.spl` — rewrote
  `kernel_draw_rounded_rect_outline`'s corner test from a filled-annulus
  distance check to a replayed stacked-thin-ring midpoint-circle test
  (`_rr_ring_hit`), plus added the missing `thickness > r+1` clamp.
- `scripts/check/check-engine2d-cpu-metal-parity-evidence.shs` — added the
  `rounded_rect_outline` scene to the evidence env/report output (the
  harness already asserted it; the gate script just wasn't surfacing the
  line).

Not touched (per explicit hand-off constraint — another session was actively
editing these for an unrelated hi-res text feature): `backend_metal.spl`,
`backend_metal_runtime_ops.spl`. Neither needed changes for this fix; the
`is_macos()` calls inside `backend_metal.spl` now resolve correctly purely
because the async platform module they import from was fixed.

## Resolution (2026-06-05)

All four primitives are now bit-exact CPU↔Metal with genuine GPU readback
(`gpu_frame_complete=true`), verified by the extended parity harness
(`line/circle/rounded_rect/triangle: MATCH mismatches=0/1024`):

- line: the MSL `kernel_draw_line` now replays the CPU `sw_bresenham` error loop
  per step (instead of a DDA division), visiting the same pixel set.
- circle outline: `kernel_draw_circle` replays the CPU midpoint loop (1D dispatch,
  thread = iteration) and emits the 8 symmetric pixels — keeps the 8-connected
  ring (a per-pixel distance annulus gaps near the diagonals).
- circle filled: both backends use the per-pixel distance test `dx²+dy² ≤ r²`;
  the CPU emits it as `isqrt(r²-dy²)` spans so it stays a fast hline fill.
- rounded_rect outline: `kernel_draw_rounded_rect` was a filled interior test
  (shape mismatch vs the CPU outline); it now draws the outline — straight edges
  plus midpoint corner arcs replayed to match `sw_corner_arc`.
- triangle: GPU dispatch enabled (`_dispatch_metal_triangle`); both backends use
  the same integer barycentric (edge-function) fill, so it is no longer a mirror
  tautology.

The parity gate (`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`)
and harness (`test/02_integration/rendering/engine2d_cpu_metal_parity_run.spl`)
now assert all of these scenes.

Because the harness clears-then-draws and both backends now share the new
formula for `circle_filled`/`triangle`, an all-black-vs-all-black buffer would
also report MATCH. An out-of-band absolute probe was run to rule that out:
filled-circle center == fill color and triangle centroid == fill color on BOTH
CpuBackend and MetalBackend (`gpu_frame_complete=true`), with the far corner ==
background. So MATCH is correct-vs-correct, not empty-vs-empty.

### Follow-up (out of scope here: CUDA, NVIDIA-host-only)

This change moved the CPU reference for `circle_filled` (now the `dx²+dy²≤r²`
distance test) and `triangle` (now integer barycentric). The CUDA PTX kernels:
- `kernel_draw_circle_filled` already uses the same distance test → now matches.
- triangle has no CUDA kernel → CUDA falls back to the (new) CPU mirror → matches.
- `kernel_draw_circle` (annulus) and `kernel_draw_rounded_rect` (filled interior)
  remain as they were and still differ from the CPU midpoint/outline — but this
  is a *pre-existing* CUDA-vs-CPU semantic mismatch (cuda_strict even asserts
  rounded_rect as a fill), not introduced by this fix. Aligning the CUDA kernels
  is tracked as separate follow-up work.

**Status (2026-06-12):** The two mismatched kernels are now formally annotated
with KNOWN PARITY NOTEs in `backend_cuda.spl` (`draw_circle` and
`draw_rounded_rect` methods). The ROCm backend has also received the equivalent
init-guard hardening (`last_probe` field, per-method `initialized` guards,
`read_pixels`/`present` null-pointer guard). PTX kernel realignment
(`kernel_draw_circle` → sw_midpoint, `kernel_draw_rounded_rect` → outline) is
the remaining open item and requires NVIDIA hardware to verify.

## Summary

The CPU (software) backend and the Metal GPU backend produce bit-identical
output for `clear`, `draw_rect_filled`, `draw_rect` (outline), and (after the
integer-lerp fix) `draw_gradient_rect`. The primitive-rasterization ops diverge
because the two backends use different algorithms.

Measured on a 32×32 scene with genuine GPU readback (`gpu_frame_complete=true`):

| op                   | mismatches | cause |
|----------------------|------------|-------|
| draw_line            | 24/1024    | CPU Bresenham vs Metal per-pixel line kernel |
| draw_circle (+filled)| 92/1024    | CPU midpoint vs Metal distance-field check |
| draw_rounded_rect    | 532/1024   | different corner rasterization |

`draw_triangle_filled` is not GPU-dispatched on Metal at all
(`backend_metal.spl` sets `gpu_frame_complete = false`), so it reads back the
CPU mirror and any "match" is a tautology — it must not be added to the parity
gate until a real GPU triangle kernel exists.

## Fix direction

Pick one canonical rasterization per primitive and make both backends follow it,
the same way `draw_gradient_rect` was canonicalized to the MSL integer lerp:

- line: match the MSL `kernel_draw_line` stepping to the CPU Bresenham (or vice
  versa) so both visit the same pixel set.
- circle: align the inclusion test (CPU midpoint vs MSL distance `<= r`).
- rounded_rect: align the corner inclusion test.
- triangle: add a GPU dispatch path (MSL `kernel_draw_triangle_filled` exists)
  so the comparison stops being a mirror tautology, then align the barycentric
  fill rule.

## Reproduce

```
src/compiler_rust/target/gui/debug/simple run build/metalcmp/moreops.spl   # ad-hoc
```

The shipped gate (`scripts/check/check-engine2d-cpu-metal-parity-evidence.shs`) only
asserts the bit-exact ops above; extend it per primitive as each is aligned.
