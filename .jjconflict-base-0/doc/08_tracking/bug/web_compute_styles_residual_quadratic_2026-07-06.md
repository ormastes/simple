# Bug: residual superlinear cost in compute_styles after WEB-2 dedup fix

- **Date:** 2026-07-06
- **Area:** web / browser_engine (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`)
- **Status:** partially addressed 2026-07-07 — the candidate-lookup scan named as a suspect below
  (`style_rule_candidates`, `:4924`) was fixed (N1: carried `id_key_dict`/`class_key_dict`/
  `tag_key_dict` through `RuleBuckets`, replacing the linear `text_key_index` scan with O(1) dict
  lookup; component cost now negligible, ~0.03–0.05 ms/node). **Root cause re-attributed**: the
  end-to-end `compute_styles_ms` / `parse_html_ms` numbers did not improve — the actual dominant
  cost is the runtime `text.substring()` primitive scaling with start offset (O(offset) per call),
  making `parse_html` quadratic and leaving a residual superlinearity in `compute_styles` via the
  same lazily-substring-backed node fields. See
  `doc/08_tracking/bug/text_substring_o_offset_parse_html_quadratic_2026-07-07.md` for the full
  measurement and fix direction.
- **Related fix:** `b65e52a909` "perf(web): build_rule_buckets dedup O(rules×keys) linear
  scan → dict insert-or-get (11.5s→linear at 3000 rules)" (WEB-2); N1 dict-lookup fix landed
  2026-07-07 (this commit).

## Summary

WEB-2 replaced `build_rule_buckets`'s linear-scan dedup (O(rules × distinct-keys)) with a
`Dict<text, i32>` insert-or-get lookup, fixing that function's own quadratic blowup. But
measuring the **whole** `compute_styles` pipeline (not just `build_rule_buckets` in isolation)
at increasing synthetic rule counts still shows superlinear growth — i.e. WEB-2 fixed one
quadratic contributor, not the only one.

## Measured evidence

Synthetic CSS with N distinct single-class rules (`.cN { color: #rrggbb; }` for N = 700,
1500, 3000), one HTML node per class so every rule has exactly one candidate match, timed via
`compute_styles`'s own call path (`simple_web_layout_render_html_software_pixels_traced`
stage print), `SIMPLE_EXECUTION_MODE=interpret`, `bin/simple` = deployed self-hosted binary:

| distinct rules | compute_styles wall time |
|---|---|
| 700  | ~1550ms (baseline point, sub-linear-extrapolated) |
| 1500 | ~3500ms |
| 3000 | **9328ms → 5899ms after WEB-2** (~1.6x speedup from the dedup fix) |

If the pipeline were linear in rule count, 700→3000 (4.3x rules) should show ~4.3x time; the
post-fix data still shows worse-than-linear growth (5899ms at 3000 vs. the ~1550ms/700-rules
baseline implies ~3.8x time for 4.3x rules purely from this one step, but the pre-fix-buckets
isolation test below shows `build_rule_buckets` itself is now linear — so the residual
superlinear cost is coming from elsewhere in `compute_styles`, most likely
`style_rule_candidates` (`:4924`) or the per-node matching loop in `compute_styles` (`:5259`)
that calls it once per node against the (now-linear) buckets.

**Isolation check performed:** `Dict<text, i32>` itself was verified linear in a standalone
probe (insert N distinct keys, O(N) wall time growth) — ruling out the dict implementation as
the residual cost. The residual must be in `compute_styles`/`style_rule_candidates`'s
per-node × per-bucket-list matching, or in candidate-list construction/sorting per node.

## Repro sketch

```
# Synthetic distinct-class CSS + one node per class, N in {700, 1500, 3000}:
gen_css(n)  = join(["​.c{i} {{ color: #{hex(i)}; }}" for i in 0..n], "\n")
gen_html(n) = "<html><body>" + join(["<div class=\"c{i}\"></div>" for i in 0..n], "") + "</body></html>"

# Time compute_styles alone via the existing stage-trace hook
# (simple_web_layout_render_html_software_pixels_traced), varying n = 700/1500/3000,
# same viewport, SIMPLE_EXECUTION_MODE=interpret, on the deployed self-hosted bin/simple.
```

No source files were modified to produce this measurement — read-only timing pass using the
existing traced entry point plus scratch synthetic fixtures.

## Next-step direction

Profile the remaining scans in the styles path with per-call counters (not just wall time):
1. `style_rule_candidates` (`:4924`) — check whether candidate-list construction re-scans a
   growing structure per node instead of doing an O(1)/O(log n) bucket lookup.
2. The per-node loop inside `compute_styles` (`:5259`) that invokes `style_rule_candidates`
   once per node — confirm bucket lookups are O(1) dict/array indexed, not a linear scan over
   all buckets or all rules per node.
3. Any specificity/cascade sort applied to the per-node candidate list — if it sorts using an
   O(k²) comparison sort per node and k (candidates per node) grows with total rule count
   (e.g. due to a shared/fallback bucket collecting all unmatched rules), that alone would
   reproduce this exact shape.

Once localized, apply the same fix pattern as WEB-2 (replace the offending linear/quadratic
scan with dict-indexed or pre-sorted access) and re-run this same three-point (700/1500/3000)
measurement to confirm linear scaling end-to-end, not just within `build_rule_buckets`.
