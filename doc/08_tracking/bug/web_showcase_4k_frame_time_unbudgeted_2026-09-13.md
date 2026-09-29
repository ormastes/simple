# The 4K web showcase lane pins no frame-time budget, and measured cost is not monotonic in pixel count

- **Filed:** 2026-09-13
- **Area:** ui / web renderer showcase 4K lane
- **Status:** open, recorded during test authoring; NOT fixed here

## What was measured

On an Apple M-series host, interpreter execution mode, Vulkan backend,
showcase catalog `overview` page:

| size | backend | elapsed |
|---|---|---|
| 320x180 | cpu_simd | 23,165 ms |
| 320x180 | vulkan | 9,244 ms |
| 160x90 | cpu_simd | 60,553 ms |
| 3840x2160 | vulkan | 177,067 ms |

The 4K render completes and is correct: 8,294,400 pixels, non-blank,
`vk_init=true cpu_fallback=false`, `submits=0`, `readbacks=1` — inside the
audited GPU boundary.

## Two problems

**1. No budget exists to assert against.** The 4K lane
(`scripts/check/check-web-showcase-4k-receipt.shs`) pins only geometry and
schema — `width=3840`, `height=2160`, `requested_backend=vulkan`,
`mode=headless-readback`, `status=measured`. Its only ceilings are process
guards (`ulimit -f 2048`, a 20 s kill timeout), not frame time.
`scripts/check/check-chrome-web-showcase-perf.shs` *reports*
`chrome_web_showcase_backend_<backend>_wall_ms_total` and compares nothing.
The only 4K numbers in the tree are narrative, in
`doc/10_metrics/ui/web_4k_showcase_after_gpu_boundary_fixes_macos_2026-09-12.md`.

**2. Measured cost is not monotonic in pixel count.** 160x90 took **more than
twice as long** as 320x180 on the same backend and page (60.5 s vs 23.2 s).
Cost is dominated by something other than pixel count — layout work, or
per-call setup — so a threshold derived from one size does not transfer to
another, and a naive "ms per megapixel" budget would be wrong in both
directions.

## Consequence for tests

`test/02_integration/ui/web_showcase/overview_4k_render_spec.spl` asserts the
geometry contract and the GPU boundary counters, and captures elapsed time as
evidence only. It deliberately asserts no timing, because inventing one here
would pin a number that neither the lane nor the metrics doc supports, on a
host whose measurements are not even ordered by size.

## What is needed

A decision by the lane's owner on whether 4K frame time is a gated property.
If it is, the budget needs to be measured per size on a known host and
recorded somewhere the gate reads; the non-monotonicity above should be
investigated first, since it suggests the dominant cost is not where a
frame-time budget would assume it is.
