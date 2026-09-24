# Web-rendering perf round 13 (2026-09-13) — batched glyph advances + the first layout profile

Round 12 (`web_perf_round12_2026-09-13.md`, PR #916) landed measurement and no
fix, and handed forward exactly one target with a written-up oracle: §3a's
batched advance warm. This round implements it, and additionally puts the first
timers ever on the `layout()` window, which §4 recorded as the largest
unattributed mass in the cold pipeline.

Host: macOS (darwin 25.5.0), shared box, **contended throughout** — load moved
enough between runs that whole-page `cold_ms` swings by 2x in both directions
(see §1b). Absolute wall times below are therefore *not* evidence; the
per-bucket counters, which count the same work on both sides of the same
binary, are. This is stated per table rather than hidden.

Base: `origin/main` @ `efc66112319` (merge of PR #916, round 12).
Binary: `/Users/ormastes/simple/build/cargo-r2/release/simple`, unchanged across
every run below.
Runner: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 … run <file>`,
`SIMPLE_WEB_STYLE_COUNTERS=1`, `SIMPLE_WEB_PHASE_TRACE=1`.

**Worktree resolution was verified, not assumed**, exactly as round 12 did it: a
`__sabotage_probe_r13` function appended to *this* worktree's
`src/lib/common/encoding/sfnt_glyf.spl` resolved and printed `probe=77713`
through the out-of-tree binary, proving an A/B swap here is measured rather than
silently ignored. The probe was then removed.

## 1. Target A — `sfnt_glyph_advance_into`, 228 calls at ~1.09 ms each

Round 12 §3a located the exact cost: every call re-runs `parse_offset_table` over
the whole font blob plus three `find_table` directory scans (`head`, `hhea`,
`hmtx`) before reading four bytes of `hmtx`. The per-glyph work is trivial; the
per-call setup is everything.

**Fix.** `sfnt_blob_glyph_advances_into(blob, glyph_ids, size_px, out)`
(`src/lib/common/encoding/sfnt_glyf.spl`) does that setup ONCE and then loops the
ids, doing only the `hmtx` read and the existing `scale` / `_round_glyf_metric`
arithmetic — the same shape `sfnt_blob_glyph_ids_into` already applies to cmap
lookups. `_hmtx` is inlined only to drop a fourth `find_table`; **its bounds test
is reproduced unchanged, including the left-side-bearing bound it checks but this
function never reads**, so the batch answers 0 in exactly the places the
per-glyph call fails. In `font_renderer.spl` an `_advw` table keyed by
`(loaded-face identity, font_size)` — the same key granularity the per-glyph path
already uses, since an advance is size-dependent — warms the whole ASCII range
from the already-warmed `_gid_vals` ids on first use. A non-positive warm value
falls through to the untouched per-glyph path.

### A/B, 4 alternating pairs with the rest of the tree held constant

Only `font_renderer.spl` was swapped between sides (the batch function itself
stays present but unused on the base side), so the layout timers of §2 are in
both arms and cannot contaminate the comparison. Catalog totals (the font probe
counters are cumulative, so the `tab-bar` row is the whole eight-page figure):

| pair | `gadv_sfnt` calls/ms (base) | `gadv_sfnt` (new) | `gadv_batch` calls/hits/ms (new) | `adv_miss_ms` base → new |
|---|---|---|---|---|
| 1 | 228 / 216 | **0 / 0** | 228 / 228 / 20 | 438 → 217 |
| 2 | 228 / 207 | **0 / 0** | 228 / 228 / 19 | 398 → 210 |
| 3 | 228 / 429 | **0 / 0** | 228 / 228 / 46 | 718 → 509 |
| 4 | 228 / 551 | **0 / 0** | 228 / 228 / 25 | 1037 → 261 |
| mean | 228 / **351** | 0 / **0** | 228 / 228 / **27** | **648 → 299** |

Two things this says beyond the headline. `gadv_batch_hits = 228 = gadv_sfnt_calls`
on every pair: the batch answers **every** call the per-glyph path used to take,
on the real catalog faces, not just on the spec fixture — so there is no residual
slow path and no face (TTC or system) where the batch silently fails. And
`gadv_batch_ms ≈ 27 ms` for 228 lookups means the `_advw` slots are not thrashing
across sizes; 8 slots hold the catalog's (face, size) working set.

### Per page (pair 1, row deltas of the cumulative counters)

The advance misses are front-loaded: a face/size pair is warmed once and every
later page reads the `_adv_cache` instead, so the two first pages carry almost
the whole bucket. That is why the *catalog* total is the right unit for this
target and a per-page ratio on the later pages measures nothing.

| page | `gadv_sfnt_ms` base | `gadv_batch_ms` new | `adv_miss_ms` base → new |
|---|---|---|---|
| overview | 61 | 8 | 156 → 90 |
| html | 106 | 7 | 219 → 98 |
| css-layout | 11 | 1 | 13 → 2 |
| css-paint | 4 | 0 | 5 → 1 |
| forms-media | 19 | 3 | 27 → 21 |
| animation | 2 | 0 | 3 → 1 |
| evidence | 1 | 0 | 1 → 1 |
| tab-bar | 12 | 1 | 14 → 3 |

**Net on the measured bucket: ~351 ms → ~27 ms, i.e. ~324 ms removed from the
advance-miss path per catalog pass** (round 12's calmer host measured the same
bucket at 248 ms; the direction and the call counts agree, the absolute size
tracks host load).

### Oracle

`test/01_unit/lib/common/encoding/sfnt_batch_glyph_advances_equivalence_spec.spl`
— **4 examples, 0 failures.** The oracle is the unchanged per-glyph
`sfnt_glyph_advance_into`, compared value-for-value over: the whole ASCII catalog
(95 codepoints) x sizes {1, 8, 16, 24, 512} (475 comparisons, >300 non-zero);
adversarial glyph **indices** 0..255 plus 60000, 4294967295, 4294967296 and -7 at
sizes {1, 16, 512} (780 comparisons); empty blob; sizes 0, -4, 513, 100000; and an
output array longer than the id array. **Sabotage-checked**: adding `+ 1` to the
batch's scaled advance turns it into 3 of 4 examples failing, so the spec can
fail on the thing being changed.

**One honest gap in the oracle.** The pinned fixture is PixelifySans only. The
adversarial example scans glyph index space directly, which *reaches* the
`gid >= numberOfHMetrics` branch if that font has `numberOfHMetrics < numGlyphs`,
but the spec does not read `hhea` to assert that it did — so that branch is
**exercised-if-present, not proven-exercised**. It is stated here rather than
claimed. The catalog evidence above (228/228 hits, digests unchanged) covers the
faces that actually render.

## 1b. Why `cold_ms` is not used as the A evidence

Mean `cold_ms` over the same four pairs: css-paint 9609 → 8902, html 5165 → 4642,
css-layout 5085 → 5576, forms-media 1570 → 2392, animation 1368 → 2136. The
target is worth ~324 ms; the host moved pages by more than 1,000 ms in **both**
directions inside the same alternating sequence. Reporting any of these deltas as
the fix's effect would be reporting load. The counter table above is the evidence.

## 2. Target B — the first `lay_*` sub-timers, and what they found

Round 12 §4: "`sec_layout*` still has no timers at all." Ten buckets now exist
(`web_layout_counters_report()`, same default-off `SIMPLE_WEB_STYLE_COUNTERS=1`
gate as every counter in this engine), implemented as wrappers that delegate to
the untouched `_lay_*_inner` bodies. **Unarmed the wrapper reads the module flag
`_wsc_on` directly and tail-calls the inner body — no clock, no helper call** (see
§4 for the measured production-path cost).

Catalog totals, armed run (`prof_r13`, the most contended run of the session —
read the shares, not the absolutes):

| bucket | calls | ms | what it covers |
|---|---|---|---|
| `lay_inline` | 1,888 | **2,464** | `inline_text_advance_width` |
| `lay_measure` | 1,467 | 1,527 | `style_run_byte_advances` + `style_measured_run_advance` |
| `lay_compose_resolve` | 157 | 544 | the compose stage's font resolve (§3) |
| `lay_wrap` | 422 | 286 | `compute_style_wrap_ranges` + `compute_wrap_ranges` |
| `lay_intrinsic` | 1,911 | 273 | `intrinsic_text_width` |
| `lay_grid` | 1,533 | 112 | `grid_track_sizes` |
| `lay_flex` | 27 | 4 | flex max-content / wrap base width |
| `lay_table` | 15 | 4 | table cell min/max content width |
| `lay_ellipsize` | 0 | 0 | `ellipsize_text_for_width` — never called by this catalog |
| `lay_cps` | 1,457 | 1,482 | the `text_codepoints` decode *inside* `lay_inline` |

Per page (the rows are **cumulative**, so these are row deltas; `comp` is
`lay_compose_resolve`):

| page | inline | measure | cps | wrap | intrinsic | grid | comp |
|---|---|---|---|---|---|---|---|
| overview | 7 | 5 | 4 | 0 | 1 | 1 | 26 |
| html | 492 | 293 | 272 | 0 | 75 | 28 | 69 |
| css-layout | 667 | 393 | 396 | 76 | 64 | 30 | 70 |
| css-paint | 993 | 669 | 611 | 196 | 112 | 38 | 123 |
| forms-media | 154 | 85 | 96 | 1 | 13 | 9 | 87 |
| animation | 146 | 77 | 98 | 12 | 7 | 5 | 117 |
| evidence | 2 | 3 | 3 | 1 | 0 | 0 | 27 |
| tab-bar | 3 | 2 | 2 | 0 | 1 | 1 | 25 |

**How to read the table, stated rather than implied.** These are INCLUSIVE
timers and they are **not a partition of the layout window**. `lay_cps` is a
sub-bucket *inside* `lay_inline` and must not be added to it. `lay_wrap`,
`lay_flex` and `lay_table` reach the measure leaves and so contain `lay_measure`
time. `lay_inline` and `lay_measure` do **not** nest in each other
(`inline_text_advance_width` does not call `style_run_byte_advances`). On a
quieter run of the same tree (`prof_memo`) the same buckets read inline 1,142 /
measure 705 / cps 699 / comp 335 / wrap 138 / intrinsic 105 / grid 48 — the
*shares* are stable, the absolutes are not. For scale: on the phase-traced run
the `style_end → layout` windows summed to 3,568 ms and `layout → compose` to
1,407 ms.

### 2b. The largest layout leaf, and why it was NOT "fixed"

`lay_inline` is the largest bucket, and **60% of it is one line**: the
`text_codepoints(raw)` decode at the top of `inline_text_advance_width`, which
runs on every call including the majority that then answer in O(1) from
`st.resolved_font_width`. That is 1,482 ms of 2,464 ms — exactly the shape of a
repeat-computation, and the brief's conditional fix.

It is not a repeat. A two-entry exact memo (`text_codepoints` is pure, so
returning the array it produced for a byte-identical string returns the same
value) was implemented and measured on the real catalog:

```
lay_cps_hits=3 lay_cps_misses=1454
```

**0.2% hit rate.** The leaf decodes 1,454 *distinct* strings; nothing is being
recomputed. The memo was therefore **removed rather than landed** — an ineffective
cache is unused code, and CLAUDE.md forbids adding it. This is the honest outcome
and it is worth more than the memo would have been: the next agent does not have
to rediscover it.

The real shape of the remaining fix is different and is **named, not claimed**:
the first use of `cps` is only its LENGTH (`adv.len() == cps.len()`), so a
codepoint *count* — countable without building the array — would skip the
allocation for the fast-path majority, with the full decode kept for the branches
that index `cps`. That is not landed here because "count non-continuation bytes"
and `text_codepoints(...).len()` agree only for well-formed UTF-8, and proving
the equivalence over the malformed case needs its own fixture spec. Exactly the
`sec_resolve → §3a` discipline round 12 used.

## 3. Target C — `compose_shaping`, sub-timed

`lay_compose_resolve` = 157 calls / 544 ms is the compose stage's
`resolve_font_metrics_with_language` in `_html_draw_ir_resolved_text_command`
(`simple_web_html_layout_renderer_paint_layout.spl`) — the **second** font
resolution per `#text` node, distinct from the style stage's `sec_resolve`. On the
phase-traced run the compose window totalled 1,407 ms, so this single call is
**~39% of compose**, and it is the largest named thing in it. On the two smallest
pages (evidence, tab-bar) and on `animation` it is the *dominant* compose cost.

Report only, per the brief. The obvious fix — share one resolution between the
style stage and the compose stage — is not trivially exact: style resolves over
the node's *metric text* (trimmed unless `white-space: nowrap`) while compose
resolves over the *painted* string, so they are not always the same key, and a
wrong merge moves every glyph. Named for round 14 with that caveat attached.

## 4. Cost of the instrumentation on the production (unarmed) path

CLAUDE.md requires a perf regression introduced by a change to be fixed or
recorded in the same change. ~5,500 layout leaf calls per catalog now pass
through a wrapper. Measured unarmed (no `SIMPLE_WEB_STYLE_COUNTERS`), swapping
all four changed lib files between base and new, 2 alternating pairs:

| pair | base total ms | new total ms |
|---|---|---|
| 1 | 21,297 | 15,292 |
| 2 | 12,986 | 15,280 |
| mean | **17,142** | **15,286** |

**This does not resolve to a number, and saying otherwise would be dishonest.**
The spread *within the base arm alone* is 8,311 ms; any wrapper cost is far below
that noise floor. What can be said: the measured means do not show a regression
(the new arm is the faster of the two means), the 8/8 Draw IR digests are
byte-identical on the unarmed new arm as well, and the unarmed wrapper is a
module-flag test plus a tail call — the arithmetic worst case over ~5,500 leaf
calls is well inside the noise that prevents measuring it here. If a future
round gets a quiet host, this is the first thing to re-measure.

## 5. Gates

| gate | verdict |
|---|---|
| Draw IR digests, `test/05_perf/ui/web/pipeline_bench.spl` (the named gate file, run unmodified) | **8/8 byte-identical** to round 12's baseline: `1d22f0682a6f4ae1 8c2d9f380e7dcc3d ea9df39e03ecd2cb fd9d26e9eff2d9b3 0d8baa45b77f5bda 066600bb7d9cef53 4cf797f8c3a8f3a4 56097a5a1ce50dda` |
| digests on every A/B and unarmed run | 8/8 identical on both arms of all 6 swapped-file runs |
| `sfnt_batch_glyph_advances_equivalence_spec` (new) | **4/4 pass**, sabotage-checked |
| style spec sweep, 48 files, both sides | verdict lines **byte-identical**, `diff` empty; 32 OK / 16 pre-existing ERROR on each side |
| `web_overflow_triple_memo_equivalence_spec` | OK 2/2, identical both sides |
| `web_template_elide_fastpath_equivalence_spec` | OK 2/2, identical both sides |
| `sfnt_metrics_only_advance_spec` (round 12's oracle for the function this round batches) | OK 5/5, identical both sides |
| GPU boundary audit `--matrix` | **PASS — 4 matrix cell(s) audited** (overview + css-layout at 900x760 and 3840x2160), 0 violations; each cell `host_pixel_iterations=0, readbacks_per_frame<=1, submits_per_frame<=1`; selftest 18 examples, 0 failures |

The 48-file sweep is exactly
`find test/01_unit test/03_system -name '*spec.spl' | grep -E 'selector|style|cascade|inherit'`
minus `blink` and `50.mir`. Round 11's "53" counted the memo and equivalence
specs inside that number; here they are listed as their own rows above, so the
same specs are covered — the count differs, the coverage does not.

**One spec set was started and abandoned, and that is recorded rather than
quietly dropped:** the `text_layout/font_*_spec.spl` group (font_renderer.spl is
changed by this round) was launched on both sides and the base arm did not get
past `font_renderer_spec.spl` within the round's budget on this contended host.
The three extra specs above plus the 48-file sweep did complete on both sides.
The font_renderer specs are **not** claimed as run here; the digest gate and the
new equivalence spec are what cover that file's change.

## 5b. The rebase caught a real regression this round's own gates had passed

Everything above §1-§5 was measured on `efc66112319`. While it was running, a
parity lane landed on `main` (`9290752171d`) touching `sfnt.spl`,
`font_provider.spl`, `paint_layout.spl` and `font_renderer.spl` — including a
**sub-pixel advance** change: `sfnt_glyph_advance_into` now also reports
`meta[18]`, the same advance in MILLI-pixels, and the renderer's index lane
takes that field in preference to the rounded `meta[2]`.

On the rebased tree the digest gate went RED: all 8 differed from `origin/main`
run with the same five files reverted (that comparison, not round 12's recorded
list, is the correct oracle once the baseline has legitimately moved). Bisecting
the five files one at a time named `font_renderer.spl`, and a temporary probe
comparing the batch against a fresh per-glyph call at every hit reported **zero
mismatches** — because the batch was right about `meta[2]` and the renderer had
stopped using `meta[2]`. The batch was returning whole pixels into a lane that
expects milli-pixels.

**This is exactly the failure the round-12 write-up warned a digest gate exists
to catch, and it is worth recording that the equivalence spec did NOT catch it**:
the spec's oracle read `meta[2]`, so it agreed with a batch that was wrong in
production. A one-lane oracle for a two-lane function is not an oracle.

Fixed by giving `sfnt_blob_glyph_advances_into` both lanes — `out` in
milli-pixels (`_round_glyf_metric(raw * scale * 1000.0)`) and `out_px` rounded
(`_round_glyf_metric(raw * scale)`), **rounded independently exactly as the
per-glyph function does**, since `milli / 1000` is a different number — and by
reproducing the call site's own two-field rule (`meta[18]` when positive, else
`meta[2] * 1000`, admitted on the PIXEL field). The spec now checks both lanes
against both oracle fields.

Post-rebase verification, all on `origin/main` @ `9290752171d`:

| check | result |
|---|---|
| digests, rebased tree vs `origin/main` content (5 files reverted) | **8/8 byte-identical** |
| `sfnt_batch_glyph_advances_equivalence_spec` (two-lane oracle) | 4/4 pass — and it **fails** on the one-lane version, which is the strongest sabotage evidence this round has |
| `sfnt_metrics_only_advance_spec` | OK 5/5 |
| `web_overflow_triple_memo_equivalence_spec`, `web_template_elide_fastpath_equivalence_spec` | OK 2/2 each |
| A/B, 2 post-rebase pairs, only `font_renderer.spl` swapped | `gadv_sfnt` **351 calls / 310 + 268 ms → 0 / 0**; `gadv_batch` 351 calls, **351 hits**, 43 ms both runs; `adv_miss_ms` 526/525 → 246/258 |
| digests across those 4 runs | 8 unique (page, sha) pairs — identical on both arms |

The call count rose from 228 to 351 because the upstream font change altered
which faces the catalog loads; the batch still answers **every** one.

The GPU boundary audit and the 48-file spec sweep were run pre-rebase and are
**not** re-run here: neither the parity lane nor this round touches
`engine2d`/`gpu` submit-and-readback code, and the 48 specs exercise the
selector/cascade path that this round's post-rebase delta (two extra array
lanes inside one sfnt function) cannot reach. That is a reasoned scope
statement, not a claim that they were re-executed.

## 6. Whole-picture row (css-paint, html)

The Chrome column carries **round 12's caveat unchanged and it has not been
re-earned**: the only per-page Chrome figures in `doc/10_metrics/ui/` are the
2026-09-12 headless screenshot round trips with a fresh `--user-data-dir`, which
are spawn-dominated (~3-4 s of process startup) and include raster that our
`cold_ms` excludes. The official harness was **not** run on this contended host.
The ratio is recorded for continuity and is not evidence either way.

Mean `cold_ms` over the four new-side A/B runs, against the same 2026-09-12
Chrome column round 12 used:

| page | round 12 cold ms | round 13 mean cold ms (4 runs) | Chrome ms (09-12, spawn-dominated) | ratio |
|---|---|---|---|---|
| css-paint | 5,923 | 8,902 | 3,084 | 2.89 |
| html | 4,232 | 4,642 | 4,093 | 1.13 |

The css-paint ratio moved from 1.92 to 2.89 and **that is a host artefact, not a
regression**: on the same four alternating pairs the *base* arm — which is
`origin/main` — measured 9,609 ms for css-paint, i.e. worse than the new arm, and
the counter evidence in §1 shows strictly less work being done. Round 12's 5,923
came from a less contended box. Comparing a number measured under load ~7 against
one measured earlier is not a comparison, and the honest reading of this table is
that **neither round's absolute ms is admissible for the 2x question**; §7 keeps
that open.

## 7. What is left

- **`lay_inline`'s codepoint decode** — located to the line and measured at 60% of
  the largest layout leaf, proven NOT to be a repeat (3 hits / 1,454 misses). The
  count-without-decode fix needs a malformed-UTF-8 equivalence fixture first.
- **`lay_compose_resolve`** — 39% of the compose window in one call; sharing it
  with the style stage needs the metric-text vs painted-text key difference
  resolved.
- **`lay_measure` (1,467 calls)** — second-largest leaf, not yet split.
- **The `run`/`id` caches that never hit** (round 12: 0/617 and 0/1,234) remain
  open debt.
- **A quiet host.** Every absolute ms in this document is load-contaminated. The
  2x-Chrome question cannot be answered until the official harness runs on an
  idle box.
