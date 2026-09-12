# Web text measurement: the residual was the cmap re-parse, not kerning (2026-09-12)

Status: **FIXED.** `measure_text_advances` on
`examples/06_io/ui/web_catalog/css-layout.html` went from **3,946 ms to 450 ms**
for the same 2,601 characters, with both catalog pages byte-identical.

Platform: macOS 25.5.0 / Apple M4. Binary
`/Users/ormastes/simple/build/cargo-r2/release/simple`, `stat -f '%z %m'` =
`39368072 1789171430`, identical for every run below.
`SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
SIMPLE_2D_BACKEND=cpu_simd SIMPLE_WEB_PHASE_TRACE=1 SIMPLE_WEB_STYLE_COUNTERS=1`,
900x760, one page at a time. Baseline runs are from a pristine
`git archive HEAD` tree (F13's tip) so the edited `src/lib` could not reach them.

## The two named suspects were both wrong, and the counters say so

`doc/10_metrics/ui/web_style_cascade_after_memo_macos_2026-09-12.md` closed by
naming two suspects for the 5,346 ms residual, explicitly by elimination rather
than measurement: `horizontal_kern` running per character PAIR uncached, and the
dylib backend lacking a metrics-only entry point so `.advance` reads still
rasterize. New level-gated counters on the same page, same flags:

| leaf | calls | ms | share of the 3,846 ms measurement leaf |
|---|---|---|---|
| advance-cache MISSES | 108 | **3,442** | **89%** |
| ... of which the cmap re-parse | 216 | **3,341** | **87%** |
| ... of which the table-directory parse | 216 | 76 | 2% |
| `horizontal_kern` (all 2,455 calls, uncached) | 2,455 | **26** | **0.7%** |
| rasterize-for-metrics (`get_glyph` fallthrough) | **0** | **0** | **0%** |
| face-identity resolution | 2,601 | 20 | 0.5% |
| loop body + advance-cache hits | 2,493 | ~240 | 6% |

**Kerning was 26 ms, not a lever** — 0.7% of the leaf. Memoizing it was tried
first and made things *worse*: the naive memo inside `horizontal_kern` resolves
the face identity and scans up to 8 identity strings per call, which cost
**204 ms** against the 26 ms of foreign calls it replaced. The memo only pays
once the slot is resolved ONCE per run by the caller.

**Nothing rasterized for metrics.** `raster_metric_calls=0`: these pages take the
`selected_outline_blob` branch, which was already metrics-only. The
"dylib-without-blob backend has no metrics-only entry point" hypothesis is true
of a backend this page never uses.

**What it actually was:** resolving one codepoint to a glyph id re-parses the
entire cmap. `sfnt_cmap_glyph_id` calls `parse_cmap_format12`/`parse_cmap_format4`
(`src/lib/common/encoding/sfnt_cmap.spl`), and those rebuild the complete segment
arrays *and* the whole glyph-id array from the blob on every call — 15 ms per
single-glyph lookup. It was paid **twice per cache miss**: once by
`has_glyph`, which on this backend is `sfnt_blob_glyph_exists` (the same parse),
and once by the advance lookup itself.

## Fix

Three changes, all pure Simple, all exact rather than approximate:

1. **`sfnt_cmap_glyph_ids_into` / `sfnt_blob_glyph_ids_into`** — batch
   codepoint -> glyph id over ONE parse of the cmap subtables, running the same
   two lookups in the same order as `sfnt_cmap_glyph_id`.
2. **Per-face ASCII glyph-id table** in `font_renderer.spl`, keyed on the face
   identity alone (a glyph id does not depend on pixel size). Warmed for ASCII
   32..126 from a single parse on first use. A positive id is exactly what
   `has_glyph` reports true for over the same blob, so the fast lane skips that
   call too; `0` and `-1` both fall through to the original path untouched, so
   every other backend and the vector/bitmap fallbacks keep their behaviour.
3. **`sfnt_glyph_advance_into`** — a metrics-only advance from `hmtx`, skipping
   the `glyf` outline decode that `sfnt_measure_glyph_into` performs for ink
   extents this caller never reads. Same `_round_glyf_metric(h0 * scale)`
   expression, so the two agree by construction (pinned by spec). This turned
   out to be worth only ~2% on these pages — the outline decode was never the
   cost — but it is kept because it is the correct shape and it is what makes
   the by-glyph-index call in (2) possible.

Also folded in, on the strength of the counters: the kern-pair memo is a flat
95x95 `i32` square per `(face, size)` slot read through a slot resolved ONCE per
run (not per call); `measure_text_advances` sizes its result array up front
instead of `push`-growing it; and a run-level `(face, size, text)` advance memo.

## Where the kern memo belongs, and the residual

The memo was first written INSIDE `horizontal_kern` and that was a measured
regression: `kern_ms` went 26 -> 204 with 1,954 of 2,455 calls hitting, because
resolving the face identity and scanning the slot table costs ~0.35 ms against a
~0.01 ms foreign call. Moved so that only the caller that resolves the slot once
per run does the lookup and the store — `measure_text_advances` — the same 2,455
calls cost **5 ms**. `horizontal_kern` itself is back to its original body plus a
probe, so `render_text`/`measure_text_width` are not slowed down either.

`measure_text_advances` is **450 ms** on css-layout, meeting the 500 ms target.
The remainder is 203 ms of first-time advance misses (118 calls, each still one
table-directory parse), ~240 ms of interpreted loop body, and 5 ms of kerning.
The run-level memo scored **0 hits / 146 misses** on css-layout and 0/15 on
overview: neither page repeats an exact (face, size, text) run, so it does
nothing on this corpus and is kept only for corpora that do repeat runs. The
non-ASCII path is unchanged and still pays a cmap parse per codepoint, and the
kern memo is covered only by the pixel oracle — no spec exercises it directly,
because constructing a `FontRenderer` bound to a real face needs the font dylib.

## Evidence

| page | leaf | before | after | |
|---|---|---|---|---|
| css-layout (908 nodes) | `measure_text_advances` | 3,946 ms | **450 ms** | 8.8x |
| | style stage | 9,493 ms | 5,685 ms | 1.7x |
| | pipeline to compose_shaping | 10,406 ms | 6,546 ms | 1.6x |
| overview (43 nodes) | `measure_text_advances` | 2,251 ms | **188 ms** | 12.0x |
| | style stage | 2,805 ms | 733 ms | 3.8x |
| | pipeline to compose_shaping | 2,874 ms | 805 ms | 3.6x |

Pixel oracle: `cmp` byte-for-byte on both pages' PPMs, before vs after —
**identical, 0 mismatching bytes on each**, so no `diff_ppm.js` run was needed.
Neither page tripped the render budget on either side (`grep -c budget-break` = 0).

Spec: `test/01_unit/lib/common/encoding/sfnt_metrics_only_advance_spec.spl`,
5 examples, all green — metrics-only advance equals the full-measure advance for
10 glyphs at 3 sizes, by-index equals by-codepoint, the advance scales with the
requested size, and batched cmap resolution equals 20 per-codepoint lookups
(plus the blob-level wrapper). Sabotage: computing the advance at a hardcoded
16 px instead of the requested size took it 5/5 green -> **3/5 (2 failures)** ->
5/5 green on restore.

## Note on the earlier numbers

The 5,346 ms figure this record was opened against, and F13's 13,084/13,291 ms
style figures, were measured on a COLD first process; every warm run of the same
unmodified tree sits at ~3,900 ms / ~9,500 ms. The before/after pairs in this
record are warm-vs-warm from the pristine tree. Treat the cold numbers as
process-start cost, not as a measurement of this leaf.
