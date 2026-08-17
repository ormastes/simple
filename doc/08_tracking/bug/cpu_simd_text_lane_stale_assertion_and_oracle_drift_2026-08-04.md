# cpu_simd public text lane: stale assertion rewound by a sync clobber, plus an unrecorded oracle drift

Status: CLOSED (not reproducible)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
"Resolution of OPEN 1" at the foot of this file. OPEN 2 confirmed and re-scoped
(the two declarations do **not** behave identically). Two further defects spun
off, both open:
`web_software_oracle_blanks_text_on_budget_exhaustion_2026-08-04.md`,
`web_renderer_duplicate_public_entry_binding_2026-08-04.md`.
Date: 2026-08-04
Base measured: `f6bd28d1c8726987b2d984ade4d0c2a88b8fa82f` (pristine worktree, Rust bootstrap seed runner)

## Symptom

`test/01_unit/lib/gc_async_mut/gpu/browser_engine/web_renderer_cpu_simd_paint_spec.spl`

```
Results: 6 total, 5 passed, 1 failed
  ✗ skips heuristic routing for public cpu simd text renders
    expected 128 to equal 0
```

`128` is `simd_hit_counts().fill_hits` — the number of `record_simd_fill_hit()`
calls made by `SoftwareBackend.sw_fill_raw_span`
(`src/lib/gc_async_mut/gpu/engine2d/backend_software.spl:745`) while rendering a
32x32 text page through the public entry
`simple_web_render_html_to_pixels_with_engine2d_backend(text_html(), 32, 32, "cpu_simd")`.
`0` was the expected count. Deterministic: 128 on three consecutive runs.

## Root cause of the red: a sync clobber rewound the assertion only

| commit | what it did |
|---|---|
| `d24f780a09e` "perf(simd): skip text routing overhead" | added a `cpu_simd` text short-circuit to `simple_web_engine2d_render_html_pixels` routing text pages to `simple_web_layout_render_html_software_pixels`, AND added this example asserting `fill_hits == 0`. Green together. |
| `3b86328c925` "test(simd): route residual paint through engine2d" (5h later) | **deleted** that short-circuit on purpose, and in the same commit rewrote this example to `fill_hits > 0` plus a pixel-oracle equality check. Its doc edit replaced the sentence *"The public Engine2D renderer also skips heuristic/probe routing for obvious text pages requested as `cpu_simd`"* with the residual-presentation model. |
| `e8444b6b1a6` "chore(sync): WC sweep — parallel-session docs/tests/memory-leveling work" (the **next** commit) | snapshotted a stale working copy and restored the spec blob to `d303c3d0b74843bd5b2b3fe769b09af23ac87206` — the `d24f780a09e` version. The source deletion survived; the assertion update did not. |
| `c6b3ee4721f` "fix(fonts): route web and GUI through Draw IR" | rerouted the public web renderer onto the Draw IR lane so web text gets real glyph rasterization, reinforcing the same direction of travel. |

The spec blob has been byte-identical to the `d24f780a09e` version ever since —
every later touch is a `.jjconflict` / tree-wipe recovery that restored the same
stale blob. This is exactly the failure mode `.claude/rules/vcs.md` § "Sync must
never clobber" describes.

The assertion was therefore **stale**, not a live defect report. Fixed by
restoring `3b86328c925`'s intent in
`web_renderer_cpu_simd_paint_spec.spl`.

Sabotage proof that the assertion is load-bearing on exactly this routing
property: restoring the `d24f780a09e` short-circuit in
`simple_web_engine2d_render_html_pixels` turns the example red with
`expected 0 to be greater than 0` — the exact mirror of the original
`expected 128 to equal 0`.

## OPEN 1 — the public Draw IR text lane drifts 226 px from the CPU oracle

`3b86328c925` set the correctness bar as *"The CPU layout framebuffer remains the
exact oracle"*. On the current tree that bar does **not** hold for the public
lane, which is why `3b86328c925`'s oracle-equality assertion could not simply be
restored alongside the hit-count one.

Measured on the 32x32 `<p>Text lane</p>` fixture, deterministic over three runs:

| lane | fill_hits | copy_hits | non-white px | px differing from oracle |
|---|---|---|---|---|
| `simple_web_layout_render_html_software_pixels` (oracle) | — | — | 134 | 0 |
| `simple_web_layout_render_html_readback_paint(..., "cpu_simd", true)` | 0 | 0 | 134 | **0** |
| `simple_web_render_html_to_pixels_with_engine2d_backend(..., "cpu_simd")` | 128 | 0 | 111 | **226** |

The two public cpu_simd lanes disagree with each other on the same page. The
Draw IR lane lays down 23 fewer inked pixels. Whether the Draw IR glyph raster is
the improvement `c6b3ee4721f` intended or a regression against the CPU ground
truth is **not settled here** — it needs its own lane with a visual oracle, and
must not be closed by picking whichever number is convenient.

Also note the presenter half of `3b86328c925` did **not** survive either:
`_cpu_simd_should_probe_solid_only` and its short-circuit are still present in
`simple_web_html_engine2d_presenter.spl`, which is why the readback lane still
measures 0 fill hits. The tree currently carries one half of `3b86328c925` and
not the other.

## OPEN 2 — the spec's `use` does not name the module that actually runs

The spec imports

```
use std.gc_async_mut.gpu.browser_engine.simple_web_renderer.{simple_web_render_html_to_pixels_with_engine2d_backend}
```

but `simple_web_render_html_to_pixels_with_engine2d_backend` is declared **twice**
— `simple_web_renderer.spl:98` and `simple_web_engine2d_renderer.spl:1170`.
A `BINDMARK` print in each body proves the call resolves to
`simple_web_engine2d_renderer`, i.e. the `use` line is misleading and a reader
tracing the spec lands in the wrong file. This cost one wasted sabotage round:
patching the `simple_web_renderer` body left the spec green because that body
never executes.

Same family as the known bare-name-collision hazard.

**Correction (2026-08-04):** the claim that "both declarations reach the same
endpoint today, so there is no behavioural bug" is **wrong**. The two bodies
differ in more than routing — only `simple_web_renderer.spl:98` passes the
backend name through `_resolved_backend_name(width, height, backend_name)`;
`simple_web_engine2d_renderer.spl:1170` passes `backend_name` straight through.
So the two declarations also disagree about backend resolution, and which one
binds is a behavioural question, not merely a readability one. Full writeup and
suggested rename: `web_renderer_duplicate_public_entry_binding_2026-08-04.md`.

## Provenance note

Nothing here touches GPU-offload provenance. The lane under test is CPU-only:
`cpu_simd` is not a `gpu-paint-candidate`, `readback.source` stays `cpu_mirror`,
and no assertion was added that claims a device produced any frame.

---

## Resolution of OPEN 1 (2026-08-04)

OPEN 1 asked whether the Draw IR glyph raster is the improvement `c6b3ee4721f`
intended or a regression against the CPU ground truth, and insisted it "must not
be closed by picking whichever number is convenient". Settled below on evidence.

### The drift is a rasterizer-family difference, not thinning or dropped glyphs

Reproduced exactly (`oracle_inked=134 lane_inked=111 diff_total=226`), then
decomposed:

```
only_oracle_inked=115   only_lane_inked=92   both_inked_differ=19
```

Each lane inks pixels the other does not, in both directions — so "the Draw IR
lane lays down 23 fewer inked pixels" understates it; 92 of its inked pixels are
in places the oracle leaves blank. The best pure vertical shift between the two
buffers reaches only **0.827** agreement, so no positional offset reconciles
them. Re-run unclipped at 64x64 both lanes render *all* of "Text lane" and still
differ on 432 px (oracle 256 / lane 215) — so it is not clipping and no glyph is
dropped.

The fingerprint is adjacent-row-pair identity within the ink band:

| | software oracle | Draw IR lane |
|---|---|---|
| glyph source | hardcoded 5x7 bitmap, `src/lib/common/ui/glyph_bitmap_5x7.spl` | real TTF outlines, `sfnt_glyf.rasterize_sfnt_glyf` |
| scaling | integer upscale, `glyph_scale(16) = 16/8 = 2` | native, `hmtx` advances |
| antialiasing | none, hard on/off | `_glyf_edge_coverage`, 4x4 supersample, 17 levels |
| identical adjacent row pairs | **6 of 6** | **0 of 6** |
| ink rows @32px | 20..31 — 10x14 cell overflows, **truncated at row 31** | 17..28, fits with clearance |

The oracle emits every source row twice, which mechanically inflates its ink
about 1.2x versus a true outline raster (134/111 = 1.21 at 32px; 256/215 = 1.19
at 64px).

### Verdict: the Draw IR lane is authoritative

Not because it is newer. Because at this viewport **the oracle is the one that is
wrong**: its 2x-upscaled 10x14 cell overflows the 32px canvas and is truncated at
row 31, and its 10px advance walks past col 31. The Draw IR lane fits the canvas,
antialiases from real outlines, and uses real font metrics. `c6b3ee4721f` moved
the public entry there deliberately, for exactly this reason.

### So byte-exactness was the wrong bar — for text only

`3b86328c925`'s equality bar was right *at the time*: both lanes then bottomed out
in the same software rasterizer. `c6b3ee4721f` deliberately broke that premise.
Demanding equality now would mean reimplementing a 5x7 bitmap font inside the
outline rasterizer, i.e. discarding the quality win on purpose.

But **non-text content is still byte-identical** between the two lanes — solid,
translucent and CSS-opacity pages all measure `diff=0`, stable across runs,
because they share the same solid/blend fill code. There `3b86328c925`'s bar is
still exactly right and has been restored verbatim rather than weakened.

### The restored bar

`web_renderer_cpu_simd_paint_spec.spl` goes 6 -> 8 examples:

1. `keeps non-text pages byte-exact between the public lane and the software
   oracle` — exact equality for solid / transparent / opacity. Reports
   `drifted-by-<n>` on failure.
2. `keeps the public text lane structurally in agreement with the software
   oracle` — four checks:
   - **rasterizer-family pin**: oracle `row-doubled`, lane `per-row`. The sharpest
     of the four: the likeliest real regression is the Draw IR lane silently
     falling back to the bitmap font — the very defect `c6b3ee4721f` fixed — which
     flips `per-row` to `row-doubled`. Also catches the oracle's budget collapse
     (`blank`).
   - **ink-coverage bound, factor 2** — derived from the mechanism, not fitted to
     today's numbers: the oracle quantises every glyph pixel up to a whole 2x2
     block (`glyph_scale(16)=2`), and that upscale is the only systematic
     multiplier between the lanes, making 2 the constructive ceiling. Measured
     1.21 / 1.19.
   - **line-box overlap** — ink rows of the two lanes must overlap.
   - **non-vacuity** — both lanes ink > 0, so two blank lanes cannot pass the
     other three by symmetry.

### Sabotage verification

| # | perturbation | result |
|---|---|---|
| S1 | `_glyf_edge_coverage` coverage collapsed to 0 | `8 total, 7 passed, 1 failed` — `expected oracle-over-2x to equal within-2x` |
| S2 | `_glyf_edge_coverage` row-quantised to 2px blocks (simulates the bitmap-font regression) | `8 total, 7 passed, 1 failed` — `expected mixed to equal per-row` |
| S3 | oracle `fb_rect_clip` fill colour shifted 1 LSB | `8 total, 5 passed, 3 failed` — `expected drifted-by-1024 to equal byte-exact` |

After each, sources were restored and verified byte-identical to base by SHA-1,
and the spec returned to `Results: 8 total, 8 passed, 0 failed`. S1/S2 perturb the
rasterizer beneath the *actually bound* entry — per OPEN 2, perturbing
`simple_web_renderer.spl:98` is a no-op and reads as a false green.

### Measurement trap found while doing this

The software oracle **silently returns a blank page** when its wall-clock render
budget expires; on this loaded host it flapped between 134 and 0 ink with no
source change. Every oracle call in the spec now pins an explicit large
`budget_ms`. This is very likely why `3b86328c925`'s oracle-equality assertion
could not simply be restored: even a correct renderer is being compared against a
reference that intermittently blanks. Filed as
`web_software_oracle_blanks_text_on_budget_exhaustion_2026-08-04.md`.

### Provenance

Unchanged: the lane under test is CPU-only, `readback.source` stays `cpu_mirror`,
and no assertion added here claims a device produced any frame.
