# cpu_simd public text lane: stale assertion rewound by a sync clobber, plus an unrecorded oracle drift

Status: assertion fixed; two residual defects OPEN and filed here.
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

Same family as the known bare-name-collision hazard. Both declarations reach the
same endpoint today (`simple_web_layout_render_html_pixels_engine2d`), so there
is no behavioural bug — only an unprovable-by-reading import.

## Provenance note

Nothing here touches GPU-offload provenance. The lane under test is CPU-only:
`cpu_simd` is not a `gpu-paint-candidate`, `readback.source` stays `cpu_mirror`,
and no assertion was added that claims a device produced any frame.
