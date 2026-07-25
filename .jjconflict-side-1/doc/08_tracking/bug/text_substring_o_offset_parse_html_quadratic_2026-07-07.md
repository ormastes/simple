# Bug: `text.substring()` cost scales with start offset → `parse_html` is quadratic

- **Date:** 2026-07-07
- **Area:** runtime `text` primitive (`text.substring`, UTF-8 char-indexed slicing) and
  `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl` (`parse_html`,
  tag/attribute extraction; and residually `compute_styles`).
- **Status:** partially fixed 2026-07-07 — `parse_html` leg **FIXED** (native-split event
  scanner, see "Update" below). `text.substring()` O(offset) itself remains **open** at the
  runtime level; `compute_styles`'s residual superlinearity is **still open** and is **not**
  attributable to parse-side lazy views (see correction below).
- **Related fix:** N1 dict-lookup fix (`style_rule_candidates` O(1) bucket lookup via
  `id_key_dict`/`class_key_dict`/`tag_key_dict` carried through `RuleBuckets`) landed the same day
  and removed the *previously measured* dominant cost in `compute_styles`'s candidate lookup. This
  record re-attributes the pipeline's actual dominant cost, discovered while verifying that fix.

## Summary

The N1 fix made `style_rule_candidates`'s per-node bucket lookup O(1) (dict-indexed instead of a
linear scan over `text_key_index`). Measuring the *whole* `compute_styles_ms` / `parse_html_ms`
pipeline before and after confirms the dict fix worked as intended (candidate-lookup component now
negligible, ~0.03–0.05 ms/node) but the end-to-end numbers did **not** improve, because a much
larger cost dominates elsewhere: `parse_html` itself is quadratic, and the root cause is the
runtime `text.substring()` primitive's cost scaling with **start offset**, not slice length.

This is the same class of bug as this file's own `:3640` comment for the CSS scanner
("`char_at`-based scanning was O(n^2) ... each `char_at` is O(index) on UTF-8 text") — but here it
is `text.substring()`, used pervasively by `parse_html`'s tag/attribute extraction on lazy
substring views of the HTML source, and it was never converted to the byte-array scanning pattern
that `parse_html`'s CSS-scanning sibling (`css_bytes_find` / `_css_scan_rules_simple`, ~`:3640`)
already uses.

## Measured evidence

All measurements: `SIMPLE_EXECUTION_MODE=interpret`, synthetic distinct-class CSS/HTML fixtures
at 700/1500/3000 rules (one node per class, viewport 320×240), deployed self-hosted `bin/simple`,
via the existing stage-trace hook (`simple_web_layout_render_html_software_pixels_traced`) — same
methodology as `web_compute_styles_residual_quadratic_2026-07-06.md`. Measured **post**-N1-fix.

### (a) Standalone `text.substring()` microbench — cost scales with start offset

A standalone probe calling `text.substring(offset, offset + k)` for a fixed small `k` on a long
text, varying only `offset`:

| start offset | wall time |
|---|---|
| 700  | ~28 ms |
| 1500 | ~101 ms |
| 3000 | ~413 ms |

~4x per 2x offset increase (700→1500 is ~2.1x offset → ~3.6x time; 1500→3000 is 2x offset → ~4.1x
time) — consistent with **O(offset)** per call, i.e. UTF-8 char indexing that walks from the start
of the string (or from a cursor) every call rather than O(1) byte-offset indexing or a cached
UTF-8 index. Slice length `k` was held fixed and did not materially affect the trend, ruling out
"cost scales with result length" as the explanation.

### (b) `parse_html` is quadratic as a consequence

| distinct rules (N) | `parse_html_ms` |
|---|---|
| 700  | 1573 |
| 1500 | 6972 |
| 3000 | 26641 |

700→1500 (2.1x N) → 4.4x time; 1500→3000 (2x N) → 3.8x time — quadratic, matching (a): each of the
O(N) tag/attribute extractions in `parse_html` calls `text.substring()` at a start offset that
grows with how far into the document the parser has advanced, so total cost is
`sum_{i=1..N} O(offset_i)` = O(N²).

At N=3000, `parse_html_ms` (26641) is now **larger than** `compute_styles_ms` (32995 total, see
(c)) minus its own residual — i.e. after the N1 fix, `parse_html`'s quadratic cost is comparable
to or exceeds the styles pipeline's, making it the new co-dominant (arguably now the single
largest) cost in the overall render.

### (c) `compute_styles` residual superlinearity persists post-N1-fix

| distinct rules (N) | `compute_styles_ms` (post-N1) | ratio vs N |
|---|---|---|
| 700  | 5417  | — |
| 1500 | 13241 | 2.44x time / 2.1x N |
| 3000 | 32995 | 2.49x time / 2x N |

The N1 fix removed the candidate-lookup component's own quadratic contribution (now negligible,
~0.03–0.05 ms/node — confirmed via the dict fix's own before/after in the N1 patch review), but
the ~2.5x-per-2x-N ratio persists. The residual is attributed to the selector-match chain
elsewhere in `compute_styles` (e.g. `nd.tag`, `nd.class_attr`, `nd.class_words` field reads) still
re-touching lazy `text.substring()`-backed views per node per candidate rule — i.e. this is the
*same* runtime root cause as (a)/(b), reached through a different call path, not a new bug.

## Repro sketch

```
# (a) Standalone text.substring offset microbench:
for offset in [700, 1500, 3000]:
    t0 = now()
    for _ in range(iterations):
        s.substring(offset, offset + k)   # k fixed, small
    record(now() - t0)

# (b)/(c) Synthetic distinct-class CSS + one node per class, N in {700, 1500, 3000}:
gen_css(n)  = join(["​.c{i} {{ color: #{hex(i)}; }}" for i in 0..n], "\n")
gen_html(n) = "<html><body>" + join(["<div class=\"c{i}\"></div>" for i in 0..n], "") + "</body></html>"

# Time parse_html_ms / compute_styles_ms via the existing stage-trace hook
# (simple_web_layout_render_html_software_pixels_traced), varying n = 700/1500/3000,
# same viewport, SIMPLE_EXECUTION_MODE=interpret, on the deployed self-hosted bin/simple.
```

No source files were modified to produce these measurements — read-only timing pass using the
existing traced entry point plus scratch synthetic fixtures, run while verifying the N1 dict fix.

## Fix direction

Two independent angles, either sufficient on its own, both eventually desirable:

1. **Local (this file):** convert `parse_html`'s tag/attribute extraction to the byte-array
   scanning pattern already used for CSS (`css_bytes_find` / `_css_scan_rules_simple`, ~`:3640`):
   scan the HTML source once into a byte array for O(1) indexed access, and materialize node
   fields (`tag`, `class_attr`, `id_attr`, etc.) as owned strings at parse time instead of lazy
   substring views re-sliced later. This directly fixes (b) and should substantially shrink (c)
   since the residual reads the same lazily-sliced fields.
2. **Global (runtime):** fix `text.substring()` itself — either memoize/cache a UTF-8
   byte-offset↔char-index mapping per string so repeated slicing is O(1) amortized, or special-case
   ASCII strings (byte offset == char offset, no UTF-8 walk needed at all). This is the bigger win:
   every caller of `text.substring()` across the codebase benefits, not just this file. Higher risk
   / larger blast radius — needs its own dedicated verification pass.

Recommend pursuing (1) first (scoped to this file, same pattern already proven safe by the CSS
scanner) and filing (2) as a follow-up runtime task once (1) is measured.

## Update 2026-07-07 — `parse_html` leg FIXED, fix-direction (1) corrected

**What landed.** `parse_html` was rewritten around a single native `_html_scan_events` event
stream (`html.split("<")` once, consumed by a two-pass `parse_html`) instead of repeated
per-position `text.substring(pos, ...)` calls. This removes the O(offset) runtime primitive from
the hot path entirely — no byte-array conversion needed. `count_html_nodes` plus two now-unused
helper functions were deleted (folded into the single-pass scanner). Opus-reviewed CLEAN: 23/23
semantic fixtures byte-identical pre/post, linearity re-confirmed to N=6000 (2.02–2.03x cost per
doubling, i.e. linear). Measured **27.3s → 1.1s at N=3000 (~24x)**.

**Important correction to fix-direction (1) above.** The byte-array (`[u8]`) scan approach this
record originally recommended (mirroring `css_bytes_find`/`_css_scan_rules_simple`) was
prototyped and **measured ~10x worse than baseline** under the interpreter — per-element `[u8]`
array reads/indexing dominate cost there, the same anti-pattern now documented in
`doc/08_tracking/bug/css_bytes_helpers_dead_code_2026-07-07.md` (whose byte-helper functions
turned out to have zero callers repo-wide). The idiom that actually wins under the interpreter is
one native `split()` call producing a small number of segments, each handled with small
`substring`/slice ops on short segments — not a per-byte array walk. Treat "byte-array scan" as a
**disproven** direction for interpreted Simple hot loops; prefer native `split`/`find`-based event
scanning.

**Still open.**
- `text.substring()`'s O(offset) runtime cost itself (fix-direction (2) above) is unchanged and
  still the right long-term fix for every caller, not just this file.
- `compute_styles`'s residual superlinearity (section (c) above) is **still open**. It is **not**
  resolved by the parse_html fix and should **not** be attributed to parse-side lazy views — the
  residual lives in the selector-match/candidate chain (`style_rule_candidates` and the per-node
  cascade matching loop), a separate cost center from `parse_html`'s own tag/attribute extraction.
