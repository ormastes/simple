# Web-rendering perf round 7a (2026-09-13)

Continuation of `doc/10_metrics/ui/web_perf_round6_2026-09-13.md`. Task
contract: target `sel_match` (the selector-group matcher,
`selector_group_matches_node_parts` / `_selector_group_matches_node_parts_inner`
in `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl:2220-2270`),
land at most one A/B-proven fix.

## Corrected premise: the rightmost-compound rule index already exists

The round-7a task brief assumed the matcher "tests every rule against every
element" and asked to build an id/class/tag/universal bucket index keyed by
each selector's rightmost compound. **That index is already implemented** and
has been on `main` since before this round:

- `build_rule_buckets` (core.spl:2052) walks every rule's comma-groups,
  extracts each group's rightmost compound (`selector_rightmost_part` +
  `selector_bucket_base`/`selector_bucket_kind_from_base`/
  `selector_bucket_value_from_base`), and files the RULE index into an `id`
  bucket, a `class` bucket (per class name), a `tag` bucket, or a `fallback`
  bucket (attribute-only/`*`/pseudo-only selectors) — exactly the bucket
  scheme this round was asked to add.
- `style_rule_candidates` (core.spl:2179) computes, per element, the union of
  `fallback_rules ∪ tag_rules[el.tag] ∪ id_rules[el.id] ∪ ⋃ class_rules[c]`
  via a sorted-merge-unique over `[i32]` rule-index lists (`merge_sorted_rule_lists_unique_count`),
  preserving original rule order — so cascade order and digests are
  unaffected by the indexing itself.
- The call site (core.spl:2997) already calls `style_rule_candidates(nd, rule_buckets)`
  to get `candidates_raw` before running any selector match, and `rule_buckets`
  is built once per style pass (core.spl:2844), not per node.

Re-implementing this would have been pure duplication. No index-construction
code was added this round.

## Where `sel_match` time actually goes: not rule fan-out

Hypothesis checked instead: does the *index* only narrow to the RULE level
while each candidate rule still tests **every** comma-group in a
multi-selector rule (`h1, h2, .card, #hero {…}`), even groups whose rightmost
compound didn't put the rule in this element's candidate set? If group
fan-out were large, per-candidate-rule group filtering (test only the
group(s) whose bucket key actually matched the element) would be a
digest-safe win, since `matched_specificity = max` over matching groups and a
non-candidate group can never match anyway.

Measured with `SIMPLE_WEB_STYLE_COUNTERS=1 SIMPLE_WEB_PHASE_TRACE=1` on the
8-page catalog bench (`test/05_perf/ui/web/pipeline_bench.spl`), 4 runs,
`build/cargo-r2/release/simple` @ `a8e72c3ddcf` (current `origin/main` tip):

| run | wall (`real`) | sel_match_ms (sum) | candidates (sum) | selector_calls (sum) | calls/candidate |
|---|---|---|---|---|---|
| 1 | 15.14 s | 1043 | 4024 | 4078 | 1.013 |
| 2 | 14.84 s | 1025 | 4024 | 4078 | 1.013 |
| 3 | 15.34 s | 1082 | 4024 | 4078 | 1.013 |
| 4 | 14.48 s | 1008 | 4024 | 4078 | 1.013 |

`digests=8` (8/8 byte-identical) on every run; `candidates`/`selector_calls`
are byte-identical across all 4 runs (deterministic — only the timing columns
vary), consistent with round 6's `sel_match` range (1036-1112 ms) on the same
bench.

**`selector_calls / candidates` = 1.013 — essentially 1:1, not the >1.5
fan-out this round hypothesized.** The rule index already prunes almost all
non-matching rules before any selector group is tested; the rare >1 cases are
rules with 2+ comma-groups where more than one group happens to share a
bucket key with the element (e.g. `.card, .card-header` both landing a
`.card`-tagged node in the same candidate rule). There is no meaningful
group-level fan-out to filter — a group-level index on top of the existing
rule-level index would touch a real code path for a gain in the single-digit
percent range at best, on already-noisy 15-40 ms/run timing.

## Conclusion: no fix landed this round (honest negative, per round-6 precedent)

Per the task contract ("implement AT MOST ONE fix, with A/B evidence"),
landing zero fixes is allowed when no candidate survives measurement. Round 6
already showed (candidate 1) that memoizing the selector-text-only parsing
inside `base_selector_matches` doesn't separate from noise because that
parsing is cheap relative to the node-dependent comparison work. This round's
own hypothesis (group-level fan-out) is now also ruled out by direct
measurement, for a different reason: there is no fan-out to eliminate — the
existing rule index already narrows almost 1:1.

**Where the remaining `sel_match` cost likely lives, for round 7b:** inside
`_selector_group_matches_node_parts_inner` and the `simple_match`/
`simple_match_ctx` chain it calls per surviving candidate — repeated
selector-string scanning (`text_index_of(sel, "::")`, first-colon split,
attribute-bracket scanning, pseudo-class chain walk) that is node-independent
but re-executed on every call, plus the ancestor-combinator walk for any
non-trivial (non-rightmost-only) selector group. Round 6 already showed a
naive per-selector-text memo doesn't help for `base_selector_matches`
specifically; a round 7b candidate should profile which of
`simple_match_ctx`'s sub-parses (not just `base_selector_matches`) actually
dominates before attempting another memo, since the round-6 failure mode was
choosing a memo target cheaper than the surrounding per-node work it wrapped.

## Gate verdicts

- Draw IR digests: 8/8 byte-identical across all 4 runs above (no source
  change was made, so this is confirmatory, not new evidence).
- No code change in this round — GPU boundary audit / style+cascade/selector
  spec parity are unaffected by construction.

No PR branch/code diff accompanies this round beyond this doc.
