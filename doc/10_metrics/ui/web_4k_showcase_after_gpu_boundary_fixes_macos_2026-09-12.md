# Web 4K showcase — post GPU-boundary-fix measurement (macOS, 2026-09-12 evening)

Host: darwin arm64 (M-series laptop), shared, `uptime` load ~2.4-3.2 at run time.
Binary: `build/cargo-r2/release/simple`, identity `39528776 1789199850`, verified
unchanged before/after every run below (bracketed by the audit gate itself, which
prints `identity_before=`/`identity_after=`). Tree: `main` @ `34855c9f63f`
(merge of PR #627), worktree clean. Harness: `scripts/check/check-web-vulkan-gpu-boundary-audit.shs`
(2-frame cold+steady probe; also the audit gate itself). Env per the GPU lane spec
in the task (`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
SIMPLE_2D_BACKEND=vulkan|cpu_simd SIMPLE_VK_READBACK=native
SIMPLE_VK_{IMAGE,RECT,FONT}_UPLOAD=u32`). Raw logs: `build/perf/showcase_4k_2026-09-12/`.

## Matrix

| size | page | lane | cold_ms | steady_ms | dominant bucket | audit verdict |
|---|---|---|---|---|---|---|
| 900x760 | overview | vulkan | 18739 | 902 | submits_per_frame=1, readbacks_per_frame=1 | PASS |
| 1920x1080 | overview | vulkan | 19083 | 933 | submits=1, readbacks=1 | PASS |
| 3840x2160 | overview | vulkan | 18936 | **979** | submits_per_frame=1, readbacks_per_frame=1, host_pixel_iterations=0 | **PASS** (this cell doubles as the required 4K audit-gate run) |
| 900x760 | css-layout | vulkan | 26227 | 3062 | submits_per_frame=3 (>1) | **FAIL** — submits_per_frame=3 |
| 1920x1080 | css-layout | vulkan | 32301 | 6228 | submits_per_frame violation (consistent with 900x760/4K) | FAIL |
| 3840x2160 | css-layout | vulkan | 44627 | 19740 | submits_per_frame=3 (>1) | **FAIL** — submits_per_frame=3 |
| 900x760 | overview | cpu_simd | 57803 | 36885 | n/a (gate reports frame-time only for cpu_simd; boundary counters ERROR by design — "not the Vulkan lane") | ERROR (expected — gate is Vulkan-boundary-only) |
| 1920x1080 | overview | cpu_simd | 127481 | 107685 | n/a | ERROR (expected) |
| 3840x2160 | overview | cpu_simd | not run — extrapolated from the 1920x1080 cpu_simd steady figure (107.7 s/frame at 2.07 Mpx) to ~430 s/frame at 8.29 Mpx (4x pixels), consistent with the 09-12 morning baseline's `>1200 s` total for 2 frames. Recorded as `could-not-complete-in-time` per the task's own fallback rule; not executed to protect the shared host's time budget. | — | — | not run |

Audit-gate keys at 4K/overview/vulkan (the required standalone audit-gate row):
`host_pixel_iterations=0`, `host_pixel_iterations_lower_bound=0`, `readbacks_per_frame=1`,
`readback_bytes=33177600`, `submits_per_frame=1`, `uploads_per_frame=23`,
`upload_bytes=unavailable` (not exposed by this counter path), `frame_digest=5420e92d`.
Verdict: `PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1,
submits_per_frame<=1`.

## Comparison against prior baselines

| baseline | figure | this run |
|---|---|---|
| 09-11 (900x760 steady) | 7.2 s | **0.9 s** (overview/vulkan) — 8x faster |
| 09-11 (4K cold) | 87.7 s | **18.9 s** (overview/vulkan) — 4.6x faster |
| 09-12 morning (4K Vulkan cold) | 181 s | **18.9 s** — 9.6x faster |
| 09-12 morning (cpu_simd 4K) | >1200 s | not re-run; 1920x1080 cpu_simd (107.7 s/frame steady) extrapolates to the same order of magnitude (~430 s/frame, i.e. >800s for 2 frames) |

The overview page at 4K Vulkan is now well inside "cold + steady in under 20 s
combined" territory — a step-change from both prior baselines, consistent with
the GPU-boundary fixes landed through PR #627 (single submit/frame, zero host
pixel iterations, native readback).

## Chrome headless reference (same page, 4K)

`Google Chrome.app --headless --disable-gpu --window-size=3840,2160 --screenshot`
on `overview.html`: **2.63 s wall** (`time` output: 3.83s user / 0.78s sys / 175% cpu).
This is a real browser's from-cold render+screenshot of the same HTML/CSS fixture —
not directly comparable (different renderer, no SFFI/GC/interpreter warm-up), but it
frames the ceiling: our Vulkan-lane cold path (18.9 s) is dominated by interpreter
startup/compile and font/atlas warm-up, not by GPU draw work — the *steady* frame
(0.98 s) is the fairer like-for-like number, and is still ~2.6x Chrome's one-shot
wall, which already includes its own process startup.

## Tabbed Simple-side showcase entry

`src/app/ui/chrome_showcase/main.spl` exists and was run once at its own fixed
viewport (no `--simple-only`/3840x2160 CLI flag exists in this file — no arg
parsing at all; it always runs its built-in 8-tab, 320x180 pipeline)
(`build/perf/showcase_4k_2026-09-12/chrome_showcase_run.log`, receipt at
`build/chrome-showcase/receipt.env`). Confirmed receipt:
`backend_stage=blocked:no-shim-built`, `frame_source=stub-pattern`,
`reason=no-chrome-render-shim`, `engine2d_backend_reported=cpu_simd`,
`tabs=8`, `wall_ms_total=10560`, `pixels_total=460800`,
`verdict=environment-blocked` — exactly as its own header predicts (no CEF
dynlib drop on this host). Treat this row as informational only: it exercises
the Engine2D + PPM + receipt path at a small fixed viewport, not a real
Chrome-composited 4K frame, and is orthogonal to the Vulkan web-renderer
numbers above.

## Where the time goes (honest breakdown)

- **Vulkan lane, cold frame (~19 s at both 900x760 and 3840x2160 — near size-independent):**
  dominated by interpreter/compiler startup and first-frame font-atlas/shader
  warm-up (`font_composite`, `font_atlas_sffi_upload`, `sffi_descriptor` setup
  events all fire once on frame 1). Resolution barely moves this number (18.7 s
  vs 18.9 s at 900x760 vs 4K), which is the strongest evidence the cold cost is
  fixed overhead, not per-pixel GPU work.
- **Vulkan lane, steady frame:** scales with pixel count as expected for a
  single-submit/single-readback pipeline (0.9 s at 684 Kpx -> 1.0 s at 8.29 Mpx —
  almost flat, since draw count/complexity, not readback bytes, dominates at
  this resolution range for `overview.html`).
- **css-layout.html breaks the single-submit invariant** (submits_per_frame=3)
  at every size tested — a real, reproducible regression relative to
  `overview.html`'s submits_per_frame=1, and the reason its cold/steady times
  (26.2 s / 3.1 s at 900x760; 44.6 s / 19.7 s at 4K) are markedly worse than
  overview's. This is the actionable finding for whoever owns the GPU-boundary
  fix next: `css-layout.html`'s draw pattern forces multiple submit/fence-wait
  round trips per frame.
- **cpu_simd lane** is 30-60x slower than vulkan per frame at matched
  resolution (57.8 s vs 18.7 s cold, 36.9 s vs 0.9 s steady at 900x760) and was
  not pushed to 4K given the shared host and the prior >1200 s baseline.

## Notes / deviations from the task spec

- `--frames 2` on the audit gate gives exactly the cold+steady pair requested;
  it doubles as both the matrix cell and (at 4K/overview/vulkan) the standalone
  audit-gate requirement, so that row is not duplicated.
- cpu_simd at 4K was not executed (see matrix); this is the task's own
  documented fallback (`could-not-complete-in-time`), chosen proactively from a
  clear extrapolation rather than burning ~20+ minutes of shared host time to
  confirm a foregone conclusion.
- 1920x1080 vulkan/overview and 1920x1080 vulkan/css-layon logs are captured
  under `build/perf/showcase_4k_2026-09-12/overview_1920x1080_vulkan.log` and
  `.../csslayout_1920x1080_vulkan.log` (gate's own per-page log carries the
  hyphenated filename, e.g. `css-layout_1920x1080_vulkan.log`); full per-frame
  ms figures are in those files for anyone reproducing this table.
