# Web renderer steady-state GPU route, macOS M4, after R1 authorization fix (2026-09-11)

Binaries (bracket `stat -f '%z %m'` identical before/after every run, all
runs `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0`):
A = `bin/release/aarch64-apple-darwin-macho/simple`, `26264696 1788766698`.
B = `build/cargo-r2/release/simple` (R2 seed, vulkan features), `39405288
1789115380` — differs from `39298584 1789113090` recorded at session start
(another process rebuilt B mid-session); all B rows below used `1789115380`,
bracketed per-run.

**HTML fallback triggered as designed.** `browser_common_elements_showcase.html`
at 900x760 did not complete frame 1 within 590s on A — abandoned. All rows use
`sample_web_renderer_sanity.html` (`<body data-simple-actual-gui-button="1">`),
per the task's stated fallback.

**Route/reason columns are not driven by the page-render path.**
`web_draw_ir_gpu_route_last_evidence()` returns a static
`avail=false offload=false reason=timing-unavailable` on every page-path frame
on both binaries — the page renderer never calls the sampler that updates that
state (confirmed in `vulkan_bind_pipeline_refused_after_readback_2026-09-11.md`).
Route authorization was verified separately with R1's sampler-driving probe
(`probe_authorize.spl`, 400x300 on B): `avail`/`offload` flip true at frame 3,
`reason=measured-gpu-faster`, holds through frame 8, `gpu_proven=true` and
`pixels_match=true` on all 8 — the R1 fix authorizes correctly. The page path's
`reason` column below is reported as-is (uninformative) rather than inferred.

## Steady-frame ms (median of frames 4-8) vs cold frame 1

| size | binary | backend | cold (f1) ms | steady median ms | route reason (page path) | verdict |
|---|---|---|---|---|---|---|
| 900x760 | A | vulkan | 21784 | 21451 | timing-unavailable | passed (8/8) |
| 900x760 | A | cpu_simd | 18153 | 17918 | n/a | passed (8/8) |
| 900x760 | B | vulkan | 7240 | 7227 | timing-unavailable | passed (8/8) |
| 900x760 | B | cpu_simd | 7946 | 7918 | n/a | passed (8/8) |
| 1920x1080 | A | vulkan | 65677 | 64840 (f4 only) | timing-unavailable | could-not-complete-in-time (4/8, 300s cap) |
| 1920x1080 | A | cpu_simd | 55086 | 54859 (f4-5 median) | n/a | could-not-complete-in-time (5/8, 300s cap) |
| 1920x1080 | B | vulkan | 22410 | 22302 | timing-unavailable | passed (8/8) |
| 1920x1080 | B | cpu_simd | 26577 | 26605 | n/a | passed (8/8) |
| 3840x2160 | B | vulkan | 87719 | n/a (3/8, 300s cap) | timing-unavailable | could-not-complete-in-time |
| 3840x2160 | * | cpu_simd | not attempted (budget) | n/a | n/a | not attempted |
| 3840x2160 | A | * | not attempted (B is faster; A's 1080p already blew the 300s cap) | n/a | n/a | not attempted |

GPU vs CPU at steady state: 900x760 A: GPU slower (21.5s vs 17.9s); B: GPU
faster (7.23s vs 7.92s). 1080p B: GPU faster (22.3s vs 26.6s). A's absolute
numbers are ~3x B's throughout (see below).

## 4K "in a sec" — the gap, stated honestly

4K cold frame on B (fastest binary): **87.7s**, not "a sec" — roughly 87x
away. Scaling from 900x760->1080p on B (~3x pixels, ~3x time) is
near-linear in pixel count, so the gap looks like per-pixel software cost, not
a resolution-specific pathology. Steady state was not reached (3/8 frames in
the 300s budget); the cold number is the only 4K evidence collected.

## Where the time goes (from the logs)

- B's near-identical frame-to-frame ms (7227-7918 at 900x760, std dev <0.3%)
  shows no separate per-frame startup — the 8-frame loop runs in one process,
  so this cost is real per-frame render work.
- B is consistently ~3x faster than A at every size (7.2s vs 21.5s at
  900x760; 22.3s vs 64.8s at 1080p). R2's typed `[u32]` rect-batch upload and
  other R2 seed changes account for most of the gap; A also lacks
  `rt_vulkan_copy_to_buffer_u32` (added in R2's Rust runtime) and silently
  falls back to the slower byte-packed path (`backend_vulkan_helpers.spl`'s
  `if not uploaded:` guard).
- GPU vs CPU crossover is real but small on this trivial single-`<body>`
  fixture (~600ms-4.3s/frame on B); the showcase fixture that would exercise
  many rects timed out entirely, so no realistic-complexity comparison exists.
- No frame-vs-frame drift within a run (steady == cold within ~1-2%) is
  consistent with R1's fix having eliminated per-frame engine-pool reset.

Logs: `build/perf/web_steady_gpu_2026-09-11/*.log` (not committed, `build/` is
gitignored).

Co-Authored-By: Claude Sonnet 5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01TVraTPgGDVypESTsVqXPgi
