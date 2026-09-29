# Web-rendering perf round 12 (2026-09-13) — whole-picture re-measure

Rounds 2-11 each chased one bucket; none re-measured the whole picture since
round 2. This round does that first, and the table **overturns the lead that
rounds 10/11 handed forward**.

Host: macOS (darwin 25.5.0), shared box. Load at run time `5.4-7.2` with one
foreign `simple` process — **not the quiet host the brief asks for**; the box
did not quiet within the round's deadline. Consequences are stated per column
below rather than hidden: absolute ms are load-contaminated, *counts* and
*ratios between buckets inside one run* are not.

Base: `origin/main` @ `88d760d4c30` (merge of PR #915, round 11).
Binary: `/Users/ormastes/simple/build/cargo-r2/release/simple`, identity
`39528776 1789199850`, unchanged across every run below.
Runner: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 … run <file>`,
`SIMPLE_WEB_STYLE_COUNTERS=1`.

Worktree resolution was **verified, not assumed**: a `__sabotage_probe_r12`
function appended to this worktree's `src/lib/common/ui/draw_ir_sdn.spl`
resolved and printed, proving the binary reads *this* tree's stdlib and that an
A/B swap here is measured rather than silently ignored.

## 1. Whole picture — per page, cold pipeline vs Chrome

`cold_ms` is `simple_web_layout_render_html_draw_ir` alone (parse + CSS +
cascade + layout + Draw IR build; **no raster, no PPM encode**), measured with
`SIMPLE_WEB_STYLE_COUNTERS=1`.

**The Chrome column is not a like-for-like comparison and must not be read as
one.** The only per-page Chrome figures in `doc/10_metrics/ui/` come from
`chrome_vs_simple_catalog_diff_macos_2026-09-12.md` (2026-09-12), where Chrome
wall time is a **headless screenshot round trip with a fresh `--user-data-dir`**
— spawn- and first-run-dominated, ~3-4 s of which is process startup, and it
includes raster which our `cold_ms` excludes. The official harness
`scripts/check/check-chrome-web-showcase-perf.shs` has **no `--simple-only`
mode** (that flag lives on `check-chrome-catalog-pixel-diff.shs`), and was not
re-run on this contended host. So the ratio column below is recorded for
continuity with earlier rounds and is **not evidence** either way.

| page | cold ms | top-5 buckets (ms) | Chrome ms (09-12, spawn-dominated) | ratio |
|---|---|---|---|---|
| overview | 613 | sec_metrics 401, sec_resolve 397, sec_cascade 70, sec_select 17, sec_inherit 13 | 3086 | 0.20 |
| html | 4232 | sec_metrics 949, sec_resolve 870, sec_cascade 636, sec_select 394, sec_inherit 321 | 4093 | 1.03 |
| css-layout | 4449 | sec_cascade 777, sec_metrics 525, sec_resolve 445, sec_select 390, sec_inherit 350 | 3061 | 1.45 |
| css-paint | 5923 | sec_cascade 939, sec_metrics 607, sec_select 515, sec_resolve 505, sec_inherit 452 | 3084 | 1.92 |
| forms-media | 1177 | sec_cascade 171, sec_metrics 154, sec_resolve 136, sec_select 85, sec_inherit 75 | 3077 | 0.38 |
| animation | 1007 | sec_cascade 126, sec_metrics 115, sec_resolve 101, sec_inherit 70, sec_select 66 | 4075 | 0.25 |
| evidence | 159 | sec_metrics 26, sec_resolve 26, sec_cascade 23, sec_select 4, sec_inherit 3 | 3077 | 0.05 |
| tab-bar | 281 | sec_metrics 51, sec_resolve 49, sec_cascade 48, sec_select 18, sec_inherit 12 | 4101 | 0.07 |

`sec_resolve` is **nested inside** `sec_metrics` (it is the
`resolve_font_metrics_with_language` call alone), so the two must not be added.

Catalog totals: **cold 18,228 ms** (incl. the unprofiled raster-free remainder);
`sec_metrics` 2,828; `sec_cascade` 2,790; `sec_resolve` 2,529; `sec_select`
1,489; `sec_inherit` 1,296; `sec_wm` 628; `sec_store` 617; `sec_digest` 219.

**Honest reading of "is every page under 2x Chrome".** On the numbers above
every page is at or under 2x, css-paint worst at 1.92. **That should not be
reported as the target being met**, for two reasons stated plainly: the Chrome
side is spawn-dominated (so it flatters us by ~3 s per page) and our side
excludes raster (which `chrome_vs_simple_catalog_diff` measured at 37-188 s per
page once actually painting). A like-for-like number needs the official harness
on a quiet host; until then the 2x claim is **unproven, not achieved**.

### Draw IR digests (this round's baseline)

```
overview    1d22f0682a6f4ae1
html        8c2d9f380e7dcc3d
css-layout  ea9df39e03ecd2cb
css-paint   fd9d26e9eff2d9b3
forms-media 0d8baa45b77f5bda
animation   066600bb7d9cef53
evidence    4cf797f8c3a8f3a4
tab-bar     56097a5a1ce50dda
```

**Six of eight differ from round 11's recorded digests** (`evidence` and
`tab-bar` match). This was **checked rather than asserted**:
`git log --oneline c9790ff4ea4..88d760d4c30 -- src/lib/nogc_sync_mut/text_layout
src/lib/gc_async_mut/gpu/browser_engine` names `9cd121e00da fix(web): monospace
inline content area is 19/16, not the sans 9/8; system-ui is sans` — a font
metrics change, which is exactly the kind that moves a layout digest on the six
text-heavy pages while leaving `evidence` and `tab-bar` alone. This is a change
of baseline, not a regression introduced here, and every gate in this round
compares before/after *within* this round against the values above.

## 2. Where the time actually is — and why rounds 10/11's lead is dead

Rounds 10 and 11 handed forward `apply_decls` (`tail_inline`, "~283 property
probes per inline-style call") as the next target. **The counters say that lead
is spent.** Across the whole eight-page catalog:

| counter | catalog total |
|---|---|
| `probe_calls` (full 283-probe body) | **255** |
| `probe_ms` | **630** |
| `dispatch_calls` (interned fast path) | 171 |
| `cas_apply_ms` | **287** |

255 calls is not a bucket worth a round. The cascade memo absorbs nearly
everything before `apply_decls` is reached.

**Recon recorded so anyone returning to `apply_decls` starts informed** (this
is a real landmine, it just is not this round's target): the interned-id
dispatch the brief proposes *already exists* — `simple_web_css_property_id.spl`
("Stage 3 of the apply_decls loop-inversion fix"), `_apply_decls_dispatch`, and
`_decl_tbl_all_dispatch_handled`. Its catalog holds **34** properties and the
gate is **all-or-nothing per block**: one unhandled property in a block sends
the whole block to the 283-probe body. A static histogram of the catalog pages'
CSS shows the top blockers are `background` (96 uses), `border` (82),
`background-color` (51), `text-decoration` (50), `position` (32), `top` (25),
plus `flex`/`font`/`border-left`/`border-color` — and
`compute_styles_with_material` merges *all* of a node's matching rules into one
block before calling, so essentially every real block contains a blocker and
the fast path is close to dead on real content. Widening the catalog means
re-implementing `background`/`border`/`font` shorthand semantics in a second
place, which is exactly the silent-rendering-bug risk the module header warns
about. It was **not attempted** here.

## 3. The largest remaining bucket: `sec_resolve` (font metrics), 2,529 ms

`sec_resolve` is one call — `resolve_font_metrics_with_language(st.font_family,
metric_text, st.font_size, language)` at
`simple_web_html_layout_renderer_core.spl:4238`. At 2,529 ms it is the largest
named bucket in the catalog, ~14% of cold total, and it is the brief's own
`sec_measure`/`adv_miss` candidate.

Sub-timed with the font renderer's existing `_fr_probe_*` counters (same
`SIMPLE_WEB_STYLE_COUNTERS=1` gate), catalog totals — these counters are
**cumulative across pages**, so the `tab-bar` row is the whole-catalog figure:

| sub-bucket | catalog total |
|---|---|
| `measure_ms` | 1574 |
| `adv_miss_ms` / `adv_miss_calls` | **495 / 268** (~1.85 ms per miss) |
| `cls_ms` (classifier) | 250 |
| `face_ms` | 216 |
| `lookup_ms` | 49 |
| `key_ms` | 30 |
| `faceid_ms` | 26 |
| `kern_ms` | 20 |
| `lineh_ms` | 17 |
| unattributed (per-char loop) | ~471 |
| `adv_hits` | 10,432 |
| `run_hits` / `run_misses` | **0 / 617** |
| `id_hits` / `id_misses` | **0 / 1,234** |
| `front_hits` / `front_misses` | 999 / 617 |

Two findings, reported separately because they differ in confidence:

- **`adv_miss_ms` is the largest sub-bucket: 495 ms over 268 misses, ~1.85 ms
  per single glyph advance.** The ASCII advance cache is keyed per
  `(loaded-face identity, font_size)` slot, so the *same glyph at a different
  size* is a fresh miss. The advance is a linear function of size, so a cache
  of unscaled per-`(face, codepoint)` advances scaled at read time would
  collapse these to one miss per (face, glyph) — but only if the scaling is
  **bit-exact** with today's arithmetic, or the Draw IR digest moves. That
  exactness has **not** been established here, so the change is named, not
  claimed.
- **`run_hits=0/617` and `id_hits=0/1,234` — two caches that never hit once.**
  Both are keyed on the run *content*; at ~17 chars per run over 617 distinct
  text nodes, a genuine 0% hit rate is plausible rather than necessarily a key
  defect, and the front cache (999 hits) already absorbs what repeats. The
  actionable part is the **1,234 probes of a cache that never answers**, each
  building a key string that concatenates the whole content. `key_ms=30` says
  that waste is currently cheap, so it is recorded as debt, not fixed.

### 3a. Leaf split inside the advance miss — the exact cost, located

The `adv_miss` figure above was not left as a floor. Four new permanent,
default-off leaf timers (same `_fr_probe_*` idiom and the same
`SIMPLE_WEB_STYLE_COUNTERS=1` gate) split the `get_glyph_advance` miss path.
Catalog totals:

| leaf | calls | ms |
|---|---|---|
| `gadv_sfnt` (`sfnt_glyph_advance_into`) | 228 | **248** |
| `gadv_warm` (`_gid_warm`) | 230 | 77 |
| `gadv_inst` (per-instance `GlyphCache` copy + lookup) | 230 | 4 |
| `gadv_blob` (`self.selected_outline_blob` read) | 230 | 0 |
| whole miss (`adv_miss`) | 268 | 489 |

**The single largest exact cost in this bucket is `sfnt_glyph_advance_into` at
~1.09 ms per call.** Two things this rules out, both of which were plausible
from code reading and are now measured false:

- the per-instance `GlyphCache` aggregate copy (`var cache = self.cache` +
  write-back) that the module header calls out as historically dominant is
  **4 ms**, not the cost;
- the glyph-id table warm is 77 ms, and `_gid_warm` returns from its
  `_gid_slot(identity)` hit path on all but the first call per face, so that is
  identity-string comparison, not table rebuilding.

**Why it costs 1.09 ms, and the shape of the fix.**
`sfnt_glyph_advance_into` (`src/lib/common/encoding/sfnt_glyf.spl:625`) is
**pure Simple, not a native call** — so this is in scope for a pure-Simple fix.
Every invocation re-runs `parse_offset_table(blob)` over the whole font blob and
then three `find_table` directory scans (`head`, `hhea`, `hmtx`) before reading
four bytes of `hmtx` and scaling. The per-glyph work is trivial; the per-call
setup is everything.

The fix has a proven precedent **in this same file**: `_gid_warm` already
batches all 95 ASCII codepoints into ONE `sfnt_blob_glyph_ids_into` call rather
than 95 separate parses. The same shape applied to advances — a
`sfnt_blob_glyph_advances_into(blob, glyph_ids, size_px, out)` that parses the
offset table and the three tables once and then loops the ids doing only the
`_hmtx` read and the existing `scale` / `_round_glyf_metric` arithmetic — is
**exact by construction** (identical scale, identical rounding, identical
`_hmtx`) and would collapse ~228 parses into roughly one per (face, size).

This is the recommended round-13 target, and the oracle for its equivalence
spec is the existing per-glyph `sfnt_glyph_advance_into`, kept as-is — the same
oracle discipline rounds 9-11 used.

## 4. Not measured this round, stated rather than implied

- **The official Chrome harness was not run** (contended host); the Chrome
  column is the 2026-09-12 figure with its provenance labelled above.
- **No perf fix was landed this round, and that is the honest outcome.** The
  brief asks for the largest bucket to be fixed with A/B evidence. Part 1
  overturned the inherited lead (`apply_decls`, now measured at 255 calls /
  630 ms and not worth a round), and re-aimed at `sec_resolve`; that bucket was
  then sub-timed twice to an exact leaf. Implementing the batched advance warm
  above, with the equivalence spec it requires, is a larger change than this
  round could carry **with** its gates, and shipping it un-specced against a
  function whose arithmetic feeds every glyph position would risk exactly the
  silent rendering divergence the Draw IR digest gate exists to catch. What is
  landed instead is the measurement that makes round 13 a one-target round.
- **The 4K steady-state frame was not re-measured** as a timing. The standing figure is
  `0.979 s` at 3840x2160 overview/vulkan with
  `submits_per_frame=1, readbacks_per_frame=1, host_pixel_iterations=0`
  (`web_4k_showcase_after_gpu_boundary_fixes_macos_2026-09-12.md`), against
  round 2's 0.98 s — i.e. unchanged. Re-running it on this host would have
  produced a load-contaminated number presented as a steady state, which is
  worse than citing the clean one and saying so. The **boundary invariants were
  re-verified** on this tree, however:
  `check-web-vulkan-gpu-boundary-audit.shs --matrix` →
  `PASS — 4 matrix cell(s) audited (overview + css-layout at 900x760 and
  3840x2160), 0 violations`, each cell
  `host_pixel_iterations=0, readbacks_per_frame<=1, submits_per_frame<=1`
  (selftest 18 examples, 0 failures). Note `css-layout@3840x2160` now **PASSes**;
  on 2026-09-12 it FAILed with `submits_per_frame=3`. That repair came from
  another lane, not this round.
- **`sec_layout*` still has no timers at all.** ~8.4 s of the 18.2 s catalog
  cold total falls outside every style counter (parse, layout, Draw IR build).
  That is the single largest unattributed mass in the pipeline and, on this
  table, the strongest candidate for round 13 — ahead of `sec_resolve`.

## 5. Tooling added

`test/05_perf/ui/web/pipeline_profile.spl` — the gate bench
(`pipeline_bench.spl`) is left byte-for-byte untouched so its digest role stays
pristine; the profile variant additionally prints per-page `cold_ms`,
`web_style_counters_report()` and `font_measure_probe_report()`. Both report
functions already existed and had **zero callers**, which is why rounds 5-11
each had to re-instrument by hand.

`src/lib/nogc_sync_mut/text_layout/font_renderer.spl` — four new leaf counters
(`gadv_inst`, `gadv_blob`, `gadv_warm`, `gadv_sfnt`) on the `get_glyph_advance`
miss path, level-gated and default-off like every counter around them, plus
their fields on `font_measure_probe_report()`.

**Digest neutrality of this round's code change was verified, not assumed:**
`pipeline_bench.spl` re-run after the edits reports all **8/8 digests
byte-identical** to the baseline listed in section 1.
