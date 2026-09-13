# Web-rendering perf round 10 (2026-09-13)

Continuation of rounds 5-9 (`web_perf_round{5,6,7a,7b,8,9}_2026-09-13.md`).
Two targets were set: **(A)** the ~535 ms `cas_tail` bucket and **(B)** the
~0.9 s `pp_css_us` CSS parse, which had never been sub-timed.

Target B landed: **`pp_css` 875-895 ms -> 374-408 ms across the eight-page
catalog, 4/4 A/B pairs with flat controls (-55% to -58%)**.
Target A is an **honest negative**: it was sub-timed for the first time, two
designs were implemented and measured, and **both made `cas_tail` worse**. They
are reverted; the sub-timers and the reason each design lost are kept, because
the next round should not re-derive them.

Host: macOS (darwin 25.5.0), shared box.
Runner: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
/Users/ormastes/simple/build/cargo-r2/release/simple run <file>`,
`SIMPLE_WEB_STYLE_COUNTERS=1 SIMPLE_WEB_PHASE_TRACE=1`.
Base: `origin/main` @ `82fd73631e7` (PR #905).

## New sub-timers

Both buckets were opaque before this round.

**`cas_tail` (slot 7)** is split by six nested timers, slots 8-13, reported as
`tail_inline_ms` / `tail_imp_ms` / `tail_inlineimp_ms` / `tail_display_ms` /
`tail_overflow_ms` / `tail_struct_ms`. They cost six extra clock reads per node,
which is enough to inflate slot 7 itself (measured 535 ms -> ~1.2 s), so they
are armed by their **own** env var `SIMPLE_WEB_TAIL_SUBTIMERS=1`; a plain
`SIMPLE_WEB_STYLE_COUNTERS=1` run still reports a `cas_tail_ms` comparable with
rounds 5-9. `decl_tbl_hits` / `decl_tbl_misses` were also added to the report
line.

**`pp_css_us`** is split by six timers inside `_extract_css_vw_with_rule_limit`,
printed as one `[web-phase] css_sub` line per document under
`SIMPLE_WEB_PHASE_TRACE=1`: `ppc_tmpl` (the `<template>`-eliding tag walk),
`ppc_props` (the `:root` custom-property pre-pass), `ppc_var` (`var()`
substitution), `ppc_scan` (`_css_scan_rules_simple`), `ppc_rules` (the per-rule
selector/declaration loop) and `ppc_append` (the block-to-document append).

### `pp_css` sub-buckets, µs, before (one run, all eight pages)

| page | ppc_tmpl | ppc_props | ppc_var | ppc_scan | ppc_rules | ppc_append |
|---|---|---|---|---|---|---|
| overview | 3,304 | 2,952 | 52 | 410 | 9,593 | 69 |
| html | 124,691 | 14,155 | 60 | 419 | 9,550 | 70 |
| css-layout | 152,448 | 27,116 | 77 | 440 | 17,788 | 176 |
| css-paint | 250,759 | 24,295 | 62 | 422 | 9,503 | 69 |
| forms-media | 20,148 | 6,389 | 69 | 447 | 9,935 | 72 |
| animation | 15,032 | 5,582 | 47 | 409 | 9,481 | 68 |
| evidence | 1,910 | 2,877 | 45 | 402 | 9,519 | 69 |
| tab-bar | 2,753 | 3,094 | 47 | 402 | 9,545 | 69 |
| **total** | **571 ms** | **86 ms** | **0.5 ms** | **3 ms** | **85 ms** | **0.7 ms** |

`ppc_tmpl` alone is **571 ms of the 892 ms** eight-page total, and it is not a
CSS cost at all — it is `_html_without_inert_template_sources`, which visits
EVERY tag of the HTML document and scans each tag name a character at a time in
interpreted Simple, in order to elide `<template>` bodies.

### `cas_tail` sub-buckets, ms, cumulative over the eight pages

`SIMPLE_WEB_TAIL_SUBTIMERS=1`. The floor of ~44 ms is the timer overhead itself
(six clock reads per node), so read the columns relative to it.

| bucket | total | net of the ~44 ms floor |
|---|---|---|
| tail_inline (inline_normal apply) | 291 | ~247 |
| tail_overflow (`_normalize_final_overflow_axes`) | 315 | ~271 |
| tail_imp | 44 | ~0 |
| tail_inlineimp | 45 | ~0 |
| tail_display | 44 | ~0 |
| tail_struct | 47 | ~3 |

So the prompt's hypothesis for `cas_tail` — per-node declaration VALUE parsing
— is **wrong for slot 7**: the memoized `apply_decls` boundary is slot 6 and
reads ~0 on a hit, and `decl_table_build` is already memoized
(`decl_tbl_hits=8,223` vs `decl_tbl_misses=74` over the whole catalog). What
slot 7 actually pays is (a) the unmemoized `inline_normal` apply and (b) the
overflow/scrollbar normalisation, which does six `decl_table_build` probes per
node — each a Dict lookup keyed on the whole multi-kilobyte merged declaration
string plus an array return — and six backwards linear scans over a table of
hundreds of entries.

## Target B: the `<template`-absent fast path

`_html_without_inert_template_sources` now probes `find_from(lower, "<template",
0)` once — a native substring scan — and returns `source` unchanged when the
substring is absent. That is exactly what the walk returns in that case: the
`name == "template"` branch is never taken, so `parts` ends as the single
element `source.substring(0, source.len())`.

The probe is deliberately made on the WHOLE lowered source rather than on the
walk's script/style-skipping view. A `<template` that appears only inside a
`<script>` or `<style>` body is *not* a template to the walk — and for such a
document the probe finds the substring and falls through to the full walk, which
classifies it exactly as before. The fast path can therefore only fire where the
walk provably returns its input. The walk itself is untouched, split out as
`_html_without_inert_template_sources_scan` so the oracle can drive it.

### Equivalence spec

`test/01_unit/browser_engine/web_template_elide_fastpath_equivalence_spec.spl`
(twin at `test/unit/browser_engine/`), driving a new oracle
`simple_web_layout_debug_template_elide_equivalence(html)` that runs BOTH the
wrapper and the walk and compares the results byte-for-byte.

Two tiers, the shape round 9 established: the eight catalog pages (all of which
take the fast path — none contains `<template` at all) plus twelve adversarial
documents — a real `<template>` body, a template with attributes, nested
templates, an unclosed template, a stray `</template>` with no opener,
`<template` inside a `<script>` body, `<template` inside a `<style>` body,
`<templatex>` (a prefix that is not the tag), uppercase `<TEMPLATE>`, a document
with no tags, and the empty document.

**2/2 examples pass, 0 mismatches.** Unlike round 9 this one found no
divergence — which is the expected outcome for a guard whose skipped branch is
provably a no-op, and is reported as such rather than dressed up.

### A/B evidence

4 alternating BEFORE/AFTER pairs; the core file is swapped in place between
runs, so host-load exposure is symmetric. Controls are `cas_tail` and
`sel_match`, both untouched by this change. Totals across the 8 pages:

| pair | side | pp_css (ms) | cas_tail | sel_match | sec_cascade |
|---|---|---|---|---|---|
| 1 | before | 895 | 596 | 610 | 1964 |
| 1 | after | **374** | 602 | 610 | 1978 |
| 2 | before | 878 | 600 | 608 | 1967 |
| 2 | after | **408** | 606 | 612 | 1993 |
| 3 | before | 885 | 636 | 671 | 2060 |
| 3 | after | **374** | 682 | 681 | 2150 |
| 4 | before | 875 | 602 | 609 | 2021 |
| 4 | after | **484** | 648 | 665 | 2211 |

4/4 pairs improve. Pairs 1-3 give **-55% to -58%**. Pair 4's after-run has
controls ~9% above its before-run (`sel_match` 665 vs 609), so its 484 ms is the
noisiest point and its raw delta is the least attributable; the other three
pairs' controls move by <1%, and their deltas carry the claim.

Per-page `pp_css_us`, pair 1:

| page | before | after |
|---|---|---|
| overview | 35,010 | 17,018 |
| html | 177,873 | 64,566 |
| css-layout | 219,452 | 84,086 |
| css-paint | 341,266 | 114,901 |
| forms-media | 45,046 | 30,667 |
| animation | 40,147 | 29,227 |
| evidence | 17,340 | 16,875 |
| tab-bar | 18,958 | 17,630 |

`cas_tail_ms` per page, pair 1 (unchanged, as a control should be):
4/87/200/260/24/18/1/2 before, 4/87/200/265/25/18/1/2 after.
`sec_cascade_ms` per page, pair 1: 49/404/542/687/132/98/17/35 before,
44/403/543/702/135/99/17/35 after.

## Target A: two designs, both measured worse, both reverted

Named rather than quietly dropped, because each looked obviously right.

**Design 1 — build each cascade origin's declaration table ONCE in
`_normalize_final_overflow_axes` and pass `[text]` to table-taking twins.**
Removes 5 of the 6 `decl_table_build` probes per node. Measured: `cas_tail`
**540 -> 868 ms** across the catalog with every control flat (`sel_match` 612 ->
635, +4%). Passing and rebinding an array COPIES it in this interpreter, and
three copies of a several-hundred-entry table cost more than the three memo
probes saved.

**Design 2 — guard each lookup with a native substring probe**
(`text_index_of(decls, "overflow")`, `text_index_of(decls, "scrollbar-width")`),
skipping the table probe when the property cannot be present. Measured:
`cas_tail` **697 ms** against a same-session control run of **614 ms** with the
change fully reverted — i.e. still ~13% worse. The catalog's merged declaration
strings mostly DO contain `overflow`, so the guard adds a full string scan and
then does the original work anyway.

A control run with target A entirely reverted measured `cas_tail` 614 ms where
the session's first baseline measured 540 ms, with `sel_match` 627 vs 612 — so
~14% of the apparent regression in the first two measurements was host drift,
and the remaining gap is real. Both designs are out of the tree; only the
sub-timers and these two comments survive, in
`_final_overflow_axis_in_decls`.

**What the next round should try instead**, now that the split is known:
`tail_inline` (~247 ms) is three unmemoized
`apply_decls_without_display_on_writing_mode` calls on `inline_normal` /
`combined_important_decls` / `inline_important`; extending the existing cascade
memo boundary to cover them (key = current `memo_key` + the three strings,
leaving `final_display` and `empty_cells_hide` outside, which read inputs not in
the key) is a memo-key change, not an array-passing change, and so does not hit
the copy cost that killed design 1. `tail_overflow` (~271 ms) needs the six
lookups folded into ONE table probe **without** moving an array across a
function boundary — i.e. inlined into `_normalize_final_overflow_axes` itself.

## Cold pipeline totals per page vs round 2

Round 2's marker was css-layout at 6.1 s cold. This round's change removes
135 ms of css-layout's parse phase and 226 ms of css-paint's, on pages whose
cold total is 3-6 s on this host. **Per-page cold totals are not reported as a
claim**: round 9 measured them and found the sign flipping between pairs on the
same page, and nothing about this host has changed. The load-robust claim is the
`pp_css` column above, which is sub-timed, control-flanked, and consistent
across 4/4 pairs. Against the round-2 baseline, the cumulative effect of rounds
2-10 remains an order-of-magnitude marker, not an attribution.

## Gate verdicts

| gate | verdict |
|---|---|
| Draw IR sha256, 8/8 pages | byte-identical across all 8 A/B runs (and every exploratory run): `5cdf8386bad82f0c 85a685ca46fc3527 76c359e483e11e84 2efd1c8c294b705e a16ea7c83d459a5a 616ad24659d7779e 4cf797f8c3a8f3a4 56097a5a1ce50dda` |
| `web_template_elide_fastpath_equivalence_spec` (new) | **2/2 pass**, 8 catalog pages + 12 adversarial documents, 0 mismatches |
| GPU boundary audit | `PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1, submits_per_frame<=1` |
| 53 `*selector*` / `*style*` / `*cascade*` / `*inherit*` specs + `web_cold_pipeline_memo_spec` | verdict lines **byte-identical before vs after** (35 OK, 18 pre-existing ERROR) |

The css-paint digest `2efd1c8c294b705e` differs from the value round 9 recorded
(`d9a0d2a7e71a2960`). That drift is at `origin/main` **before** this change: the
first baseline run of this session already produced `2efd1c8c294b705e`, and both
sides of every pair agree on it. It is not caused by this round and is not
resolved by it.

The spec set here is wider than round 9's 26 (the filter was not restricted to
`browser_engine/`), which is why the OK/ERROR split differs.

## Residuals, named

- `ppc_props` (86 ms) is the `:root` custom-property pre-pass, which re-walks
  the `<style>` blocks a second time; `ppc_rules` (85 ms) is the per-rule
  selector-group split. Both are now visible and neither was touched.
- A document that DOES contain `<template>` still pays the full tag walk. The
  walk itself — per-character tag-name scanning — is unimproved; it is simply no
  longer on the path for documents that have nothing to elide.
- `group_parts = group_parts + [block_group_parts[gi]]` in the block-append loop
  is quadratic in the rule count. `ppc_append` measures it at 0.7 ms over the
  whole catalog, so it is not worth changing at these sizes — recorded so a
  future round does not "discover" it as a suspect without the measurement.
