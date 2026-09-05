# Engine2D 2D performance bug register — reproduction + lint detectability

Filed 2026-09-03. One row per measured perf defect: how to reproduce it, and
whether a lint can find it automatically.

## Resolution scaling (the headline)

Same workload (shared scene table, 64 rects, readback on), same device
(Apple M4 / MoltenVK), C reference vs Simple Engine2D:

| Resolution | C fps | Simple fps | Simple as % of C |
|---|---|---|---|
| 800x600 | 1414.6 | 142 | 10.0% |
| 1920x1080 | 1245.6 | 56 | 4.5% |
| 3840x2160 (4K) | 786.0 | 16 | 2.0% |
| **7680x4320 (8K)** | **377.2** | **4** | **1.06%** |

C degrades 3.75x from 800x600 to 8K; Simple degrades 35x. **The gap is not
constant — it widens with pixel count**, which localises it to the
per-pixel/full-frame work rather than to per-primitive overhead.

Simple's 8K frame (244 ms) breaks down as: draw 0.44 ms, submit_batch 4.26 ms,
**present 115 ms, readback 124 ms** — 98% in the two O(pixels) full-frame
operations. C pays 2.65 ms total at the same resolution because its
framebuffer is HOST_COHERENT mapped memory: readback is free.

## Register

| # | Defect | Status | Reproduce | Lint? |
|---|---|---|---|---|
| 1 | Array returned in a tuple deep-copies it (~12.1 ms/frame at 800x600) | **FIXED** | `sh scripts/check/check-vulkan-2d-c-compare.shs` (ratio 25 -> 59-80) | **YES — G2DP001** |
| 2 | Per-element array copy loop (~2.5 ms/frame) | **UNBLOCKED by #7** — the loop can now be replaced by `val copy = self.host_buf` | same gate; `backend_vulkan.spl:1504` | **YES — G2DP002** |
| 3 | 1x1 draw inside a loop = one GPU dispatch per pixel (up to 127x) | 1 of ~20 sites fixed | `sh scripts/check/check-engine2d-backend-parity.shs` then compare `feat` lines in `build/engine2d-backend-parity/{cpu,vulkan}.log` | **YES — G2DP003** |
| 4 | Full-frame readback is O(pixels) with real per-pixel work; C's is a free map | open | resolution sweep above — the gap widens 10% -> 1.06% from 800x600 to 8K | **NO** (see below) |
| 5 | 5 primitives force a device->host round trip PER CALL (~4 ms steady state) | open | `feat draw_rect_blend_2nd` in the vulkan showcase log | **PARTIAL** (see below) |
| 6 | ~330 ms ONE-TIME cost on first forced-readback call | open, **site not located** | `feat draw_rect_blend` (1st) vs `draw_rect_blend_2nd` in one run: ~330 ms vs ~4 ms | **NO** |
| 7 | `rt_array_copy` slower than a per-element loop | **FIXED** (~28x; 3.2x slower -> 8.2x faster) | replace the `backend_vulkan.spl:1504` loop with `val copy = self.host_buf`: readback 2.57 -> 11.1 ms/frame | **NO** |

## Defect #7 — resolved, and the cause was not what was suspected

`[u32]` arrays are **not packed at all**. `[0u32; n]` lowers to
`rt_array_repeat` -> `rt_array_new`, which sets neither `U64_PACKED` nor
`BYTE_PACKED`; only `rt_array_new_uninit_u64` / `rt_byte_array_new` do, and no
source-level construction reaches those. So `rt_array_copy`'s packed fast paths
were dead for this shape and the GENERIC branch ran: `rt_array_new(len)` plus
`rt_array_push` per element — a non-inlined call, heap-handle untag, capacity
compare and length store, 480,000 times.

Replaced with `ptr::copy_nonoverlapping` of the tagged words plus a length
store. Within-run ratio (load-robust): `val b = a` went from **3.2x slower**
than a hand loop to **8.2x faster** — ~28x on the copy itself.

This is a whole-language fix: `rt_array_copy` backs every array-typed binding,
not just this lane.

**New item (reported, unmeasured):** `rt_array_concat`
(`collections.rs:5142`) still carries the identical per-element push loop, so
`a + b` on arrays pays the same cost. Same fix shape should apply.

## Why some are not lint-detectable, stated plainly

Rules 1-3 are **syntactic shapes**: a tuple return carrying an array, a
per-element copy loop, a 1x1 draw inside a loop. A line-oriented rule
recognises each with good precision, and all three are implemented and
fixture-tested (`bin/simple lint --gpu-2d-perf`).

The rest are **architectural or empirical properties, not shapes**:

- **#4 (readback architecture)** is about which memory a buffer was ALLOCATED
  in — `HOST_VISIBLE|HOST_COHERENT` versus device-local plus a staging copy.
  That is a property of allocation flags several call frames away from any
  readback site, and the "slow" code looks identical to the "fast" code. A
  lint cannot see it. It is caught by the resolution sweep instead, which is
  why that sweep belongs in the gate rather than in a rule.
- **#5 (per-call round trip)** is partially reachable: a rule COULD flag a call
  to `_flush_for_host_fallback` outside a frame boundary. But whether that is a
  defect depends on call frequency, which is dynamic. Flagging the 5 sites
  statically would be true-but-useless — they are already known and recorded
  here. Not implemented on purpose.
- **#6 (one-time 330 ms)** has no located site yet. A lint for an unknown cause
  is not possible; three hypotheses were measured and disproved (staging
  allocation 7 us, per-frame array allocation 351 us, `_pixels_to_bytes` upload
  — its trace never fires on this path).
- **#7 (`rt_array_copy` slower than a loop)** was a defect in the RUNTIME, not
  in the calling source, which is why no source-level rule should have flagged
  it: the idiomatic call site was correct and the runtime was wrong. **Now
  fixed** in `runtime/src/value/collections.rs`. This is the clearest case in
  the register for why "can a lint find it?" must sometimes be answered NO —
  a rule that flagged the idiomatic form would have pushed users toward the
  hand loop, i.e. toward permanently slower code, and would have hidden the
  real bug.

## Reproducing tests

Executable, in the repo:
- `scripts/check/check-vulkan-2d-c-compare.shs` — throughput vs C (defects 1, 2, 4)
- `scripts/check/check-vulkan-2d-bit-diff.shs` — pixel equality vs C
- `scripts/check/check-engine2d-backend-parity.shs` — cpu vs vulkan, plus the
  per-primitive `feat` timings that expose defects 3, 5, 6
- `test/01_unit/compiler/lint/gpu_2d_perf_spec.spl` — the lint rules themselves,
  including must-NOT-fire cases (degenerate guards, span form)

The resolution sweep for defect #4 is currently run by hand (commands in the
table above); folding it into the compare gate as extra `evidence.env` rows is
the obvious next step and is not yet done.
