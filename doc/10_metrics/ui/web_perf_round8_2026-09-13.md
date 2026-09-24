# Web-rendering perf round 8 (2026-09-13)

Continuation of `doc/10_metrics/ui/web_perf_round7a_2026-09-13.md`. Task
contract: target `sel_match` (`selector_group_matches_node_parts` /
`_selector_group_matches_node_parts_inner` in
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:2220-2270`),
land at most one A/B-proven fix, sub-time inside `simple_match_ctx` first.

## Sub-timing / shape analysis (code inspection, confirming round 7a)

Round 7a already measured `selector_calls / candidates = 1.013` (the rule
bucket index already prunes almost 1:1) and named the remaining cost as
"repeated selector-string scanning ... that is node-independent but
re-executed on every call" inside `simple_match`/`simple_match_ctx`. Reading
`simple_match_ctx` (core.spl:1669) and `_pseudo_ctx_matches` (core.spl:1547)
confirms a concrete, previously-unnamed duplicate:

- `simple_match_ctx(sel, ...)` = `simple_match(sel, ...)` (base match +
  walks the pseudo-class chain from the first `:`, checking `:not/:is/:where`,
  interaction-state pseudos, and `:root`, treating `:empty/:first-child/
  :last-child/:only-child/:nth-child/:has` as a silent pass-through) **then**
  `_pseudo_ctx_matches(sel, ...)`, which re-walks the SAME pseudo chain from
  the SAME first `:`, re-parsing every pseudo name and functional argument a
  second time, this time to check exactly the positional pseudos the first
  pass skipped (treating `:not/:is/:where/:root/` and the interaction-state
  names as "already checked", i.e. a no-op there).
- `_selector_group_matches_node_parts_inner` calls `simple_match_ctx` exactly
  once per group-match attempt (for the rightmost part only); ancestor parts
  use plain `simple_match` (single pass, no double-walk). So the duplicate
  chain-walk affects only the rightmost-part evaluation, i.e. up to
  `selector_calls` ≈ 4078 times per bench run (round 7a's count), and only
  selector text with a `:` in it pays for the second walk (`colon < 0` short
  -circuits `_pseudo_ctx_matches` immediately, and `simple_match`'s own
  colon/attr scan is O(1) `text_index_of` calls, not a re-parse of the whole
  base compound).

This is a real, mechanically provable duplicate (two independent character
walks of one string per call), not a guess — but it only fires for
pseudo-bearing rightmost parts, which round 7a's bucket-index measurement did
not size, and the interpreter's per-character `sel[i:i+1]` slicing cost
(shared by both passes) dominates the walk itself more than the walk being
doubled.

## Fix attempted: fuse `simple_match_ctx` into one pseudo-chain pass

Added `_simple_match_ctx_fused` — a copy of `simple_match`'s base-match +
pseudo-chain-walk logic where the position-based pseudo branches
(`:empty/:first-child/:last-child/:only-child/:nth-child/:has`) call the same
context helpers `_pseudo_ctx_matches` used (`_node_is_empty`,
`_child_position`, `_sibling_count`, `_nth_child_matches`, and a new
`_has_ctx_matches` extracted from `_pseudo_ctx_matches`'s inline `:has()`
comma-split so both callers share one implementation) directly in place,
instead of deferring to a second pass. `simple_match_ctx` was changed to call
`_simple_match_ctx_fused` instead of `simple_match` + `_pseudo_ctx_matches`.
`simple_match` and `_pseudo_ctx_matches` themselves were left unchanged (both
are still used elsewhere: `simple_match` for ancestor-combinator parts and
nested `:not()/:is()/:where()` options, `_pseudo_ctx_matches` for its own
direct spec coverage in `core_coverage_closure_spec.spl`).

Equivalence: for a given pseudo name, exactly one branch in the fused walk
evaluates the real check the two-pass version computed as an AND of (a) what
`simple_match`'s chain checked for that name and (b) what
`_pseudo_ctx_matches`'s chain checked for that name — the two original passes
never both perform a *real* check for the same name (each name is either
"real" in pass 1 and a no-op in pass 2, or vice versa, or unknown -> `false`
in both). Verified by full digest parity below.

## A/B evidence (8-page catalog, `pipeline_bench.spl`, this host, `build/cargo-r2/release/simple`)

4 alternating BEFORE/AFTER pairs (file swapped in place between runs to keep
host-load exposure symmetric), `SIMPLE_WEB_STYLE_COUNTERS=1
SIMPLE_WEB_PHASE_TRACE=1`, summing `sel_match_ms` across the 8 pages:

| pair | before (ms) | after (ms) | delta |
|---|---|---|---|
| 1 | 1039 | 1040 | +0.1% |
| 2 | 1387 | 1426 | +2.8% |
| 3 | 1355 | 1218 | -10.1% |
| 4 | 1098 | 1085 | -1.2% |

Draw-IR digests: all 8 pages byte-identical between before/after on every
pair (`5cdf8386bad82f0c 85a685ca46fc3527 76c359e483e11e84 d9a0d2a7e71a2960
a16ea7c83d459a5a 616ad24659d7779e 4cf797f8c3a8f3a4 56097a5a1ce50dda`), and
identical to the baseline recorded at the start of this round (4 solo runs:
1032/1030/1052/1089 ms, same 8 digests) — confirming the fuse is a pure
mechanism change with no output drift.

**Verdict: mixed sign, mean delta within the host's own noise band** (round
6 recorded a ±100 ms swing on the *unmodified* baseline across runs on this
same shared box; pair 3's -10.1% and pair 2's +2.8% straddle that band). This
does not clear the bar for a landed fix — the duplicate-walk elimination is
real in the source but too small a fraction of `sel_match`'s total cost
(most rightmost parts in this catalog are plain tag/class/id compounds with
no `:`, which never paid the second pass at all) to separate from noise.

## Conclusion: no fix landed this round (honest negative, per round 6/7a precedent)

Per the task contract, landing zero fixes is allowed when no candidate
survives measurement. The working-tree edit was reverted; `git status` is
clean at `origin/main` tip `7c251c93b6c`. No PR was opened.

**For a future round:** the pseudo-chain double-walk fix is still correct and
harmless to land opportunistically (e.g. bundled with a larger `sel_match`
change), but is not worth its own round. The likelier dominant cost, per
round 7a's own conclusion, is still unexamined directly: per-character
`sel[i:i+1]` slicing (a length-1 `text` allocation per comparison) inside
`base_selector_matches` and the pseudo-name/attribute scanning loops, which
both passes (fused or not) still pay once per call. Sizing that would need
either interpreter-level string-compare instrumentation or a byte-array
rewrite of `base_selector_matches` analogous to round 7b's HTML-tokenizer
byte-array fix — out of scope here since the round 7b fix targeted a
different function family and this round's contract was `sel_match`-only.

## Gate verdicts

- Draw IR digests: 8/8 byte-identical across baseline and all 4 A/B pairs.
- No code change landed this round (reverted after measurement) — GPU
  boundary audit / style+cascade/selector spec parity are unaffected by
  construction.
