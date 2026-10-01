# Web-rendering perf round 6 (2026-09-13)

Continuation of `doc/10_metrics/ui/web_perf_round5_2026-09-13.md`, whose
own PR (#881) landed only the round-5 write-up doc — the sub-timer
instrumentation itself (`14fa8034e90`, "sub-time the parse phase and the
sec_select/sec_cascade style buckets") was committed locally by the round-5
agent but **never pushed to `origin/main`**. This PR is therefore the one
that actually lands that instrumentation: the `sel_match`/`sel_sort`/`cas_*`
counters and the `parse` phase sub-timers (`pp_html_us`/`pp_css_us`/
`pp_childidx_us`), exposed via `SIMPLE_WEB_STYLE_COUNTERS=1` +
`SIMPLE_WEB_PHASE_TRACE=1` and printed as `[web-phase] style_counters ...` /
`[web-phase] phase=parse ...`. Both are level-gated and default-off — an
untraced render pays nothing for them, per the existing phase-trace
convention in that file.

**Outcome this round: the instrumentation lands; no optimization fix lands.**
Two candidate optimizations were measured with paired A/B evidence using that
instrumentation and both failed to move the needle (one made things slightly
worse). Per the task contract ("implement AT MOST ONE fix, with A/B
evidence"), a disproven candidate is not landed. This is an honest negative
result, recorded here so round 7 does not re-try either path without first
fixing the reason it failed.

## Sub-bucket tables (8-page catalog, this host, `before_*` runs 1-4)

Parse phase (`pp_html_us` = `parse_html`, `pp_css_us` = `extract_css_vw`,
`pp_childidx_us` = child-index build), summed across the 8 bench pages,
`SIMPLE_WEB_STYLE_COUNTERS=1 SIMPLE_WEB_PHASE_TRACE=1`:

| run | pp_html_us (ms) | pp_css_us (ms) | wall (8-page, `real`) |
|---|---|---|---|
| before_1 | 1427 | 927 | 14.73 s |
| before_2 | 1444 | 933 | 14.86 s |
| before_3 | 1525 | 953 | 15.88 s |
| before_4 | 1544 | 976 | 15.85 s |

Style-stage sub-buckets (`sec_select`'s `sel_match`, and `sec_cascade`'s
`cas_*`), summed across the 8 pages:

| run | sel_match | cas_accum | cas_merge | cas_pre | cas_key | cas_apply | cas_tail |
|---|---|---|---|---|---|---|---|
| before_1 | 1036 | 167 | 140 | 327 | 169 | 261 | 545 |
| before_2 | 1041 | 169 | 140 | 330 | 169 | 262 | 550 |
| before_3 | 1112 | 182 | 149 | 352 | 191 | 286 | 589 |
| before_4 | 1108 | 179 | 149 | 350 | 193 | 284 | 590 |

`pp_html_us` (`parse_html`) is the single largest bucket measured this round
(1427-1544 ms across the 8-page catalog). Inside the style stage, `sel_match`
(selector-group matching against a node's tag/class/id) is the largest single
leaf (1036-1112 ms) — ahead of `pp_css_us` and every `cas_*` sub-bucket.
`cas_tail` (the un-split remainder of the cascade after the other six `cas_*`
buckets) is the second largest style-stage sub-bucket.

## Candidate 1 (inherited from the dead round-5 agent): byte-compare tokenizer
scan + template-elide early return + base-selector shape memo — REVERTED

The prior agent's uncommitted edit (`html_tokenizer.spl` +
`simple_web_html_layout_renderer_core.spl`, discarded copy saved to the
session scratchpad as `round6_discarded_dirty.diff`) bundled three changes:

1. `_find_char`/`_find_substr` in the tokenizer rewritten to decode operands
   via `.bytes()` once instead of `s.slice(i, i+1) == ch` per probe offset.
2. `_html_without_inert_template_sources` given an early return when the
   document contains no `template` token at all (skips a full per-tag walk).
3. `base_selector_matches` given a shape memo (`_base_selector_shape_id`)
   caching the parsed kind/tag/id/class pieces of each distinct selector
   `base` string, keyed by the selector text.

It was complete and non-broken — draw-IR digests stayed 8/8 byte-identical
to the round-4/5 pinned values on every run — but 4 strict alternating A/B
pairs showed **no measurable win and a regression on the exact bucket it
targeted**:

| pair | pp_html_us before (ms) | pp_html_us after (ms) | wall before | wall after |
|---|---|---|---|---|
| 1 | 1427 | 1534 | 14.73 s | 14.87 s |
| 2 | 1444 | 1532 | 14.86 s | 14.90 s |
| 3 | 1525 | 1525 | 15.88 s | 14.97 s |
| 4 | 1544 | 1607 | 15.85 s | 15.64 s |

`pp_html_us` (which includes the tokenizer's `_find_char`/`_find_substr`
scans) went up in 3 of 4 pairs, not down. `sec_select` (which contains
`base_selector_matches`) was flat to slightly up across all 4 pairs
(1394-1523 ms range on both sides, no directional separation).

**Mechanism for the regression (not fixed this round, recorded for round 7):**
`_find_char`'s new body calls `s.bytes()` on every invocation, decoding the
*entire remaining string* to a byte array. `_find_char` is called once per
single-character scan target (`>`, `&`, etc.) while walking the document, so
on a long document this is O(document length) work repeated at every scan
call site — worse than the O(scan distance) the previous per-probe
`s.slice(i, i+1)` form did, even though the per-byte comparison itself got
cheaper. The existing `find_from` helper
(`simple_web_html_layout_renderer_foundation.spl:718`) has the identical
"decode both operands via `.bytes()` once, then compare integers" shape and
is already used elsewhere in the same file, so routing the tokenizer through
it is not expected to help either — it is structurally the same algorithm the
dirty diff already implemented, not a cheaper one. The real fix, if pursued,
is threading a document-wide byte array through the tokenizer's whole scan
loop so it is decoded once per document rather than once per `_find_char`
call — a larger restructuring than fits an "at most one fix" round.

The selector shape memo likewise produced no separation because its
overhead (a `Dict<text, i32>` lookup keyed by the selector-part text, itself
an O(selector length) hash) is in the same cost class as the three
`text_index_of`/`substring` calls it replaces — for the selector strings in
this catalog, the derivation it memoizes was already cheap relative to the
node-dependent comparison work in `base_selector_matches` that still runs on
every call regardless.

Diff discarded via `git checkout --`; a copy is kept at
`round6_discarded_dirty.diff` in this session's scratchpad for reference, not
committed to the tree.

## Candidate 2: whole-`html` CSS-parse memo on `extract_css_vw` — REVERTED

Hypothesis: `pp_css_us` (`extract_css_vw`, ~890-980 ms across the 8-page
catalog) re-parses CSS repeatedly, so memoizing the `Rules` result by
`(viewport_w, html)` should turn repeat calls into a dict lookup. `Rules`'
array fields are only ever read and concatenated by every call site
(`extra_rules.group_parts + own_rules.group_parts` etc.), never mutated in
place, so returning the same cached instance is safe (no aliasing hazard,
unlike the existing `Style` cascade memo which must deep-copy for exactly
that reason).

Implemented, verified digest-safe (8/8 byte-identical), then measured with 4
strict alternating pairs:

| pair | pp_css_us before (ms) | pp_css_us after (ms) | wall before | wall after |
|---|---|---|---|---|
| 1 | 887 | 899 | 14.52 s | 14.41 s |
| 2 | 897 | 933 | 14.67 s | 15.55 s |
| 3 | 886 | 891 | 14.57 s | 14.50 s |
| 4 | 910 | 971 | 14.75 s | 15.65 s |

`pp_css_us` did not drop in any pair — it went up in 3 of 4. **Root cause:**
the memo key is `"{viewport_w}\n{html}"`, i.e. the *entire* per-page document.
The bench's 8 pages are 8 distinct documents, so every call is a first-time
miss — the memo can never hit within this benchmark, and the only measurable
effect is the extra key-string allocation and dict insert paid on every miss.
The `pre_css_len=2038` value that looked identical across all 8
`[web-style-producer] css-props-stage1` log lines is a *different*,
downstream measurement (a shared boilerplate CSS block reported at a later
stage), not the `html` argument this memo keys on — the two are unrelated
strings, and conflating them was the planning error that led to implementing
this candidate. A content-hash memo on the *embedded CSS text itself*
(independent of the surrounding HTML) would need to isolate that shared block
before hashing it, which `extract_css_vw` does not do as structured today;
that is a real gap for round 7 to size, not this round's fix.

Reverted via `git checkout --`.

## Gates

Both optimization candidates were checked for correctness before being
measured and reverted; the sub-timer instrumentation that this PR actually
lands was checked separately, on HEAD:

- **Draw IR digests: 8 of 8 byte-identical** on every run of both candidates
  (dozens of runs across this round), matching the round-4/5 pinned values:
  `5cdf8386bad82f0c`, `85a685ca46fc3527`, `76c359e483e11e84`,
  `d9a0d2a7e71a2960`, `a16ea7c83d459a5a`, `616ad24659d7779e`,
  `4cf797f8c3a8f3a4`, `56097a5a1ce50dda`.
- **GPU boundary audit PASS on HEAD** —
  `SIMPLE_BIN=<interpreter> sh scripts/check/check-web-vulkan-gpu-boundary-audit.shs`,
  exit 0: `PASS — 2 frame(s) audited, host_pixel_iterations=0,
  readbacks_per_frame<=1, submits_per_frame<=1`.
- **The 19 `*style*`/`*cascade*`/`*inherit*` specs: identical before/after.**
  Run twice — once against HEAD (sub-timers present), once with the three
  changed lib files (`simple_web_html_layout_renderer.spl`,
  `..._core.spl`, `..._foundation.spl`) reverted to their `origin/main`
  content (sub-timers absent) — with everything else on the tree held fixed.
  Exit codes were byte-identical on both sides: the same **3 pre-existing
  RED** specs (`be_dom_event_path_and_style_serialize_spec`,
  `style_animation_spec`, `simple_web_css_cascade_spec` — matching round 5's
  record, unrelated to this change) and the same 16 GREEN. Since the counters
  are level-gated and default-off, and neither run set
  `SIMPLE_WEB_STYLE_COUNTERS`/`SIMPLE_WEB_PHASE_TRACE`, this isolates
  whether the new (dead-by-default) code paths disturb anything — they do
  not.
- **`web_cold_pipeline_memo_spec` GREEN on HEAD — 4 examples, 0 failures**,
  matching round 5's recorded state.

## Left for round 7

- **`sel_match` (selector-group matching) is now the largest single leaf**
  measured across two rounds of sub-timing (1036-1112 ms across the 8-page
  catalog). A shape-level memo does not touch it — the cost is in the
  node-dependent comparison (tag/class/id equality, `class_has_all`), not in
  parsing the selector text. A memo keyed on `(base, tag, cls_words, id)`
  (the full match, not just the parsed shape) would have to bound its key
  space against per-node class/id cardinality, which needs sizing before
  attempting it.
- **`pp_html_us` (parse_html) has no verified win yet.** The dead round-5
  agent's approach regressed it; the mechanism (per-call `s.bytes()` on the
  remaining document) is understood but the fix (thread one document-wide
  byte array through the whole tokenizer scan) is a bigger change than one
  round's budget here allowed.
- **A real CSS-parse memo needs the embedded-stylesheet text isolated from
  the surrounding HTML first** — keying on the full per-page `html` string
  cannot hit across distinct pages by construction, and this bench's 8 pages
  are all distinct. Worth sizing whether real caller usage (a page that
  re-renders itself, e.g. on resize or reflow) re-invokes `extract_css_vw` on
  literally-unchanged `html`, which is the only shape this memo could ever
  help.
- **`cas_tail`** (545-590 ms, second-largest bucket after `sel_match`) is
  still the un-split remainder of `sec_cascade` after the six named `cas_*`
  buckets landed in round 5 — splitting it further is the next
  sub-instrumentation step if `sec_cascade` becomes the round's target.
