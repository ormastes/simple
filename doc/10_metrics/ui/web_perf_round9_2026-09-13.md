# Web-rendering perf round 9 (2026-09-13)

Continuation of rounds 5-8 (`web_perf_round{5,6,7a,7b,8}_2026-09-13.md`).
Target A of the round-9 contract: **pre-parse every selector ONCE where
`build_rule_buckets` runs, and make the per-node match path consume only the
parsed record** — the structural fix rounds 5-8 identified but did not
implement. Three prior Sonnet rounds on `sel_match` ended in honest negatives
(a base-selector memo, a viewport memo, a fused pseudo walk); this one lands.

Host: macOS (darwin 25.5.0), shared box, load 3-8 during the sweeps.
Runner: `SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0
/Users/ormastes/simple/build/cargo-r2/release/simple run <file>`.
Base: `origin/main` @ `0388f28be34`.

## What was actually re-parsed per node

`simple_match` / `simple_match_ctx` were called ~4,078 times per 8-page bench
run, and every call re-derived, from selector TEXT, information that does not
depend on the node at all:

- the base/pseudo split (`text_index_of(sel, ":")`) and the `::` probe;
- the `[...]` bracket-group walk, and inside `attr_selector_matches` the
  `^=` / `$=` / `=` probes, the ` i` / ` s` flag strip, and `unquote_css_attr_value`;
- `class_has_all`, which re-split a `.a.b.c` compound on `.` **per node**;
- the pseudo-class chain walk — **twice**, once in `simple_match` and again in
  `_pseudo_ctx_matches` (round 8 proved the duplicate but measured fusing it
  alone as noise);
- the `:not()` / `:is()` / `:where()` / `:has()` top-level comma splits;
- `_nth_child_matches`' `an+b` parse.

All of it is per-character `sel[i:i+1]` slicing in the interpreter, which round
8 named as the likely dominant cost without sizing it. It is.

## Record design

`class ParsedSel` (+ `class ParsedAttr`) in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`:

| field | replaces |
|---|---|
| `kind` (0 compound / 1 empty / 2 `>`) | the `part == ""` / `part == ">"` text tests in the group walk |
| `dead` | every node-independent `return false` of the text path |
| `check_tag`/`want_tag`, `check_id`/`want_id` | `base_selector_matches`' six-branch base split |
| `want_classes: [text]` | `class_has_all`'s per-node `.`-split |
| `attr_tests: [ParsedAttr]` (`name`, `op`, `want`, `want_lower`, `ci`) | the bracket-group walk + `attr_selector_matches`' operator probing, flag strip and unquote |
| `pseudo_codes: [i32]` | the pseudo-chain walk **and** its duplicate in `_pseudo_ctx_matches` — one pre-parsed chain now feeds both halves |
| `pseudo_opts: [[text]]` | the `:not/:is/:where/:has` comma splits |
| `pseudo_nth_kind/_a/_b` | `_nth_child_matches`' `an+b` parse |
| `pseudo_args` | the `:root[attr]` expression (kept as text) |

`check_tag`/`check_id` are explicit flags rather than `""` sentinels, because
the text path's `#` -> `id == ""` branch really does mean "this element must
have no id", which a sentinel would have silently turned into "don't check".

The record is derived by `parse_selector_part`, which mirrors `simple_match`'s
check order statement for statement and reuses the SAME helpers
(`text_index_of`, `find_from`, `substring`, `trim`, `unquote_css_attr_value`).
It is stored on **`RuleBuckets.parsed_groups`** — not on `Rules` — because
`RuleBuckets` has exactly one construction site (`build_rule_buckets`) while
`Rules` has several, so no other constructor had to change. Indexing is
identical to `rules.group_parts`: `[rule][comma-group][part]`.

Per-node consumers: `simple_match_parsed`, `_pseudo_ctx_matches_parsed`,
`simple_match_ctx_parsed`, `selector_group_matches_node_parsed` (keeping the
same `_wsc_armed()` wrapper shape, so `sel_match_ms` measures the same span
before and after). The text functions are kept intact and are still exercised
— by the equivalence oracle, which is their only remaining caller.

`dead` is set ONLY where **`simple_match` itself** returns `false` regardless
of the node: `::`, a malformed attribute group, a malformed pseudo/functional
argument, an unknown pseudo-class name, the interaction-state pseudos, and a
failed `:not()`/`:is()`/`:where()` split. Node-dependent arms (`:root`,
`:root[attr]`) stay runtime. **`:has` is deliberately NOT in that list** — see
the third catch below.

## Equivalence spec — and the defect it caught

`test/01_unit/browser_engine/web_selector_parsed_equivalence_spec.spl` (twin at
`test/unit/browser_engine/`), driving a new debug oracle
`simple_web_layout_debug_selector_parse_equivalence(html, max_nodes)` that runs
BOTH paths over (a) every distinct selector part x every node, for the base
match AND the full-context match, and (b) every real candidate rule-group the
renderer evaluates for that node.

Two tiers, because the eight shared catalog stylesheets contain only **25
distinct selectors** between them:

| page | nodes | comparisons |
|---|---|---|
| overview | 43 | 2,240 |
| html | 836 | 43,485 |
| css-layout | 908 | 47,231 |
| css-paint | 1,200 | 62,417 |
| forms-media | 225 | 11,738 |
| animation | 179 | 9,313 |
| evidence | 9 | 471 |
| tab-bar | 19 | 1,054 |
| **catalog total** | **3,419** | **177,949** |

plus an adversarial fixture (46 rules over 30 nodes) covering `::before`,
`::first-line`, an unbalanced `[`, an unbalanced `(`, >16 `:not()` options,
`:not`/`:is`/`:where`/`:has` (incl. `:has(> li.two)` and a multi-option
`:has`), `:root` / `:root[lang]` / `:root[lang=en]`, `:disabled` with and
without the attribute, `:enabled`, `:hover`/`:focus-visible`/`:visited`,
`[x="WARM" i]` / `[x="WARM" s]` / `^=` / `$=` / bare `[x]`,
`[role="tabpanel"][hidden]`, `:nth-child` in odd/even/`2n+1`/`-n+2`/literal/
garbage forms, `:first-child`/`:last-child`/`:only-child`, `:empty`,
`nav#main.bar`, `#main.bar.baz`, `*`, `>` chains, and an unknown pseudo.

**The adversarial half failed on the first run**, and the failure was real:

```
MISMATCH base node=27 sel=input:disabled text=false parsed=true
```

`:disabled` never matches in the text path — on **either** branch. In
`simple_match`'s elif-chain, an element WITHOUT the attribute takes the
`_is_interaction_state_pseudo` arm (which answers `not
attrs.contains("disabled")` = true) and returns false; an element WITH the
attribute makes that arm answer false, so the chain falls through to the final
`pseudo != empty/first-child/last-child/only-child/nth-child/has` arm — also
true — and returns false again. The `attrs.contains("disabled")` test only
selects *which* branch reports false. The first cut of the parsed path
implemented the apparent intent and made `:disabled` match a disabled element,
which is a **behaviour change**, so it was reverted: `:disabled` is now in the
same dead set as the other interaction-state pseudos, reproducing the renderer
exactly. The quirk is pre-existing at `origin/main` and is documented in
`_pseudo_code_for`; fixing it is a separate, deliberate decision, not a
side effect of a perf round.

**Second catch — `:has` with an argument the splitter rejects is a
pass-through, not a rejection, in `simple_match`.** `simple_match`'s
elif-chain excludes `has`, so it never inspects the argument at all:
`simple_match("ul:has()", <ul>)` returns **true**, and only
`_pseudo_ctx_matches` splits the argument and returns false. The first cut
treated a failed `:has` split like a failed `:not` split and marked the part
`dead`. On a *rightmost* part that is invisible (both paths end at false), but
an **ancestor** part runs `simple_match` only — so `ul:has() > li`,
`ul:has(a,,b) span`, bare `ul:has`, and a 17-option `:has` all matched in the
text path and stopped matching in the parsed one. Fixed by storing an empty
options list instead of dying: `simple_match_parsed` ignores `PSEUDO_HAS`
entirely and `_pseudo_ctx_matches_parsed` returns false on empty options,
which is exactly the two-pass split of responsibility.

**Third catch — a functional argument on `:root` is parsed and then ignored by
the text path.** `:root(x)` takes the `(` branch, sets `arg = "x"`, and then
the `pseudo == "root"` arm checks only `tag != "html"`; the argument is
discarded. Only the `[` branch (`:root[lang]`) carries an attribute test. The
first cut stored every pseudo's `arg` into one array and ran
`attr_selector_matches` on it whenever non-empty, so `:root(x)` stopped
matching `<html>`. The field is now `pseudo_root_attrs`, written only by the
`[` branch.

Both were found the same way: the fixture rows were added, the spec was
confirmed **failing** on them, then the parser was fixed. After all three
corrections: **10/10 examples pass**, 0 mismatches across all 177,949 catalog
comparisons plus the adversarial fixture, and the 8 Draw IR digests are
unchanged (neither shape occurs in the catalog — which is the point).

## A/B evidence

12 alternating BEFORE/AFTER pairs across three sweeps (the core file is swapped
in place between runs so host-load exposure is symmetric),
`SIMPLE_WEB_STYLE_COUNTERS=1`, summing per-page counters across the 8 pages.

Controls: `cas_tail_ms` and `sel_sort_ms` (untouched code paths), and
`candidates` / `selector_calls` (the bucket index, which this change does not
touch). **`candidates=4024` and `selector_calls=4078` on all 24 runs** — the
candidate set is provably unchanged, so the delta is match cost, not pruning.

The host got busier during sweeps 2 and 3, so the raw millisecond columns are
reported as measured AND normalised by `cas_tail`, which is the load proxy
(same process, same pages, untouched code):

| sweep | pair | sel_match before | after | cas_tail before | after | before ratio | after ratio |
|---|---|---|---|---|---|---|---|
| 1 | 1 | 1016 | 618 | 540 | 541 | 1.88 | 1.14 |
| 1 | 2 | 1013 | 613 | 534 | 533 | 1.90 | 1.15 |
| 1 | 3 | 1009 | 623 | 532 | 569 | 1.90 | 1.09 |
| 1 | 4 | 1010 | 638 | 536 | 568 | 1.88 | 1.12 |
| 2 | 1 | 1037 | 609 | 550 | 536 | 1.89 | 1.14 |
| 2 | 2 | 1007 | 612 | 535 | 544 | 1.88 | 1.13 |
| 2 | 3 | 1042 | 893 | 557 | 787 | 1.87 | 1.13 |
| 2 | 4 | 1699 | 659 | 908 | 584 | 1.87 | 1.13 |
| 3 | 1 | 1260 | 642 | 634 | 567 | 1.99 | 1.13 |
| 3 | 2 | 1112 | 1007 | 606 | 865 | 1.83 | 1.16 |
| 3 | 3 | 1202 | 1022 | 638 | 909 | 1.88 | 1.12 |
| 3 | 4 | 1159 | 666 | 609 | 590 | 1.90 | 1.13 |

**12/12 before pairs land in 1.83-1.99; 12/12 after pairs in 1.09-1.16. The
two ranges do not overlap and are not adjacent.** Sweep 1 ran on a quiet host
and needs no normalisation at all: `sel_match` 1009-1016 ms -> 613-638 ms,
**-39%**, with `cas_tail` (532-540 -> 533-569) and `sel_sort` (92-94 -> 93-96)
flat. Sweep 2 pairs 3-4 and sweep 3 pairs 2-3 had controls outside the band and
their raw deltas are **not** attributable; their normalised ratios are, and
agree.

`sec_select_ms` (the enclosing section) tracks it: 1360-1369 -> 966-1007 in
sweep 1, i.e. the `sel_match` saving flows straight through and is not spent
elsewhere.

Per-page `sel_match_ms`, sweep 1 pair 1:

| page | before | after |
|---|---|---|
| overview | 9 | 5 |
| html | 231 | 139 |
| css-layout | 266 | 161 |
| css-paint | 373 | 225 |
| forms-media | 62 | 37 |
| animation | 46 | 28 |
| evidence | 3 | 2 |
| tab-bar | 15 | 9 |

`cas_tail_ms` (Target B, untouched this round): 5 / 72 / 184 / 238 / 20 / 15 /
0 / 1 = **535 ms** total, identical either side.

### Draw IR digests

All 24 bench runs, both sides, all 8 pages, byte-identical and equal to the
set round 8 recorded:

```
5cdf8386bad82f0c 85a685ca46fc3527 76c359e483e11e84 d9a0d2a7e71a2960
a16ea7c83d459a5a 616ad24659d7779e 4cf797f8c3a8f3a4 56097a5a1ce50dda
```

### Cold pipeline totals per page

Measured with `time_now_monotonic_ms` around
`simple_web_layout_render_html_draw_ir`, 2 pairs, on the busiest part of the
session:

| page | before p1 | after p1 | before p2 | after p2 |
|---|---|---|---|---|
| overview | 464 | 675 | 491 | 711 |
| html | 3203 | 3377 | 3292 | 3697 |
| css-layout | 3457 | 3772 | 3533 | 3590 |
| css-paint | 6127 | 4897 | 5326 | 5873 |
| forms-media | 1319 | 999 | 1111 | 1061 |
| animation | 1162 | 755 | 848 | 864 |
| evidence | 173 | 118 | 133 | 126 |
| tab-bar | 310 | 215 | 263 | 225 |

**These are noise-dominated and no claim is made from them.** The saving
(~400 ms across all 8 pages) is smaller than this host's own run-to-run swing
on a 3-6 s page, and the sign flips between pairs on the same page. Reported
because the contract asked for them, and withdrawn as evidence because the
controls say they cannot carry it. The load-robust claim is the
control-normalised `sel_match` ratio above.

Against the round-2 baseline (css-layout 6.1 s): css-layout now measures
3.46-3.77 s cold. That is the cumulative effect of rounds 2-9, not of this
change alone, and it was measured under different host load — treat it as an
order-of-magnitude marker, not an attribution.

## Gate verdicts

| gate | verdict |
|---|---|
| Draw IR sha256, 8/8 pages | byte-identical across all 24 runs, and equal to round 8's recorded set |
| `web_selector_parsed_equivalence_spec` (new) | **10/10 pass**, 177,949 catalog comparisons + adversarial fixture, 0 mismatches (3 real divergences caught and fixed first) |
| GPU boundary audit | `PASS — 2 frame(s) audited, host_pixel_iterations=0, readbacks_per_frame<=1, submits_per_frame<=1` |
| 26 `*selector*` / `*style*` / `*cascade*` / `*inherit*` specs + `web_cold_pipeline_memo_spec` | verdict lines **byte-identical before vs after** (19 OK, 7 pre-existing ERROR) |

The 7 ERRORs are identical on both sides, i.e. pre-existing at `origin/main`
and untouched by this change: `dom_query_selector_all_linear` (1/3),
`compound_attribute_selector` (1/4), `browser_session_html_stylesheet_sources`
(1/8), `simple_web_css_cascade` (2/10), `keyframe_selector_validation` (1/1),
`padding_shorthand_cascade` (1/1), `selector_color_subset` (8/60).

## Not done this round, and why

**Target B (`cas_tail`, ~535 ms / 8 pages) was not attempted.** It stayed a
clean control for all 12 A/B pairs, which is exactly what made the Target A
measurement trustworthy; touching it in the same change would have cost that.
It is the next round's target, and the sub-timing above localises it: 184 ms
on css-layout and 238 ms on css-paint carry 79% of it, so it is the same
two-page shape `sel_match` had. Round 8's note that `apply_decls` is already
once-per-node via string concat still stands — sub-time `decl_table_build` on
the merged string before assuming a per-(rule, property) value memo is the
right key.

**Residuals inside the parsed path**, deliberately left and named rather than
discovered later:

- `:not()` / `:is()` / `:where()` / `:has()` options are pre-SPLIT but not
  recursively pre-parsed; each option still runs the text `simple_match`. Rare
  in the catalogs, and recursive `ParsedSel` nesting is a larger change.
- the `:root[attr]` expression stays text and still runs
  `attr_selector_matches`; `:root` matches at most one node per document.
- `parse_selector_part` is re-run per node inside the debug oracle only; the
  render path parses once per style invalidation.
