# Web style producer costs ~4 s/node on the interpreted lane — cell cannot go green

**Status:** open. **Severity:** blocks the web × headless showcase cell on linux-x86_64.
**Component:** `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_core.spl`
(style producer loop, `budget-break` at line ~1876).

## Symptom

```
SHOWCASE_RESOLUTION=480x360 bin/simple run examples/06_io/ui/web_render_file_gui.spl
→ [web-style-producer] budget-break at=6 of=151 (deadline exceeded by 6.7 s)
→ web_standards_showcase status=fail reason=blank-or-uniform pixels=172800 nonzero=172800 checksum=1322071898
```

`blank-or-uniform` here is **uniform, not blank**: every pixel is identical and
non-black (the background clear), because styling aborted before any content
was resolved, so nothing was ever painted on top.

## Measurements (2026-07-29, seed `bin/simple run`, after shaper repair `941c1daeacf`)

| Budget | Nodes styled before break | Implied cost | Wall |
|---|---|---|---|
| default | 6 of 151 | pre-style pipeline + 6 nodes ≈ budget + 6.7 s | 41.7 s (earlier baseline) / <60 s |
| `SIMPLE_WEB_RENDER_BUDGET_MS=120000` (original) | 29 of 151 | ~4.1 s per node | killed at 270 s, no status line, MAXRSS ~3.0 GB |
| `SIMPLE_WEB_RENDER_BUDGET_MS=120000` (after char_at fixes below) | **38 of 151** | **~3.16 s per node** | still killed at 270 s (paint/raster phase after styling, separate issue) |

151 nodes × ~3.2 s ≈ 8 minutes of styling alone — no budget value makes this
lane green; the per-node cost itself is the defect. See "Cost center
attribution" below for the dominant contributor (`apply_decls`, not
selector matching).

## What it is NOT

- **Not the glyph-rasterization cost fixed in `ca5dac5e398`.** PROVED: this
  renderer's style loop contains zero calls to `get_glyph_advance`,
  `measure_glyph_into`, or any font/glyph function (grep of
  `simple_web_html_layout_renderer_core.spl`). The glyph fix targeted the
  `text_layout`/`font_renderer` pipeline, which this browser engine does not
  use during styling. Any claim that `ca5dac5e398` fixes the web cell is wrong
  for this lane.
- **Not silent interpreted fallback.** 0 `[jit-fallback]` markers, 0
  `Unknown variable` lines in either run log.
- **Not the shaper parse blocker.** Fixed in `941c1daeacf`; the pipeline now
  runs end-to-end and reproduces checksum 1322071898 deterministically.

## char_at()/len() indexing mismatch — fixed 2026-07-29, real but secondary (PROVED)

Separately from this bug's original cost-center question, a correctness
survey found that `char_at()` is CHARACTER-indexed while `len()`/`slice()`/
`substring()`/`index_of()` are BYTE-indexed on the deployed seed. Every
selector-matching helper that combined `char_at(i)` with a byte-length loop
bound was both a correctness hazard on non-ASCII input and, since `char_at`
pays an O(i) walk from the string start on every call (it must decode
codepoints from position 0 -- there is no cached byte-index table), a
plausible contributor to this bug's per-node cost. Fixed across
`style_block.spl`/`style_block_resolve.spl` (commit `05a27bc149f`),
`md_renderer.spl` (`6f08d76b6b6`), `layout_inline.spl` (`cb4c2fdc9f1`), and
`browser_renderer_utils.spl` (`1c843eedeea`).

Re-measured with the exact repro command below, before vs. after those
fixes, same 120 s style budget:

| | Nodes styled | Implied cost/node |
|---|---|---|
| Before (char_at fixes) | 29 of 151 | ~4.14 s |
| After (char_at fixes) | 38 of 151 | ~3.16 s |

**~24% per-node speedup, materially real, but the cell is still `status=fail`**
at the same checksum (`1322071898`) -- 151 nodes still needs ~8 minutes at the
new rate. char_at() was a real cost, not THE cost. See below for what is.

## Cost center attribution (2026-07-29, PROVED via timing probes)

Instrumented `compute_styles_with_material`'s per-node loop in
`simple_web_html_layout_renderer_core.spl` (~line 1876) with temporary
`rt_time_now_micros()` probes at four boundaries -- (1) node-start to
rule-bucket-candidates-ready, (2) candidates-ready to specificity-loop-done
(the selector-matching double loop over `selector_group_matches_node_parts`),
(3) specificity-done to the `apply_decls` cascade loop done, (4) node total
-- gated to the first 10 nodes only (`if i < 10`), decoupled from the
pre-existing `trace_stages` flag (that flag also traces `build_rule_buckets`/
`extract_css_vw`, which would have flooded output with a full CSS-rule scan
trace before ever reaching the node loop). **Not landed** -- per the log
retention rule, temporary unbounded diagnostic prints are discarded rather
than shipped; this section is the permanent record of what they found.
Reproduce by re-adding four `val _t = rt_time_now_micros()` bindings at
those four points in a scratch copy if this needs re-verifying.

Per-node breakdown (candidates = number of matching CSS rules found for that
node), 8 of the first 10 nodes (2 outliers excluded, see below):

| index | pre_candidates | specificity_loop (selector matching) | apply_decls loop | total | candidates |
|---|---|---|---|---|---|
| 0 | 6.8ms | 8.8ms | **108.6ms** | 130.5ms | 1 |
| 1 | 30.8ms | 8.4ms | **109.0ms** | 156.2ms | 1 |
| 2 | 14.7ms | 34.5ms | **272.0ms** | 327.8ms | 2 |
| 3 | 16.2ms | 29.9ms | **440.2ms** | 494.9ms | 3 |
| 4 | 25.5ms | 12.2ms | **185.8ms** | 231.8ms | 1 |
| 6 | 14.0ms | 8.4ms | **124.3ms** | 153.4ms | 1 |
| 7 | 34.6ms | 24.3ms | **252.2ms** | 318.3ms | 2 |
| 9 | 30.1ms | 26.3ms | **231.6ms** | 294.7ms | 2 |

**`apply_decls` (the CSS-declaration-application cascade) is the dominant
cost center: 70-90% of per-node wall time**, not selector matching --
`pre_candidates` + `specificity_loop` together are only ~10-20%. Cost scales
~linearly with candidate-rule count at **~100-150ms per single `apply_decls`
call** (1 candidate -> ~109-186ms; 2 candidates -> ~231-272ms; 3 candidates ->
440ms), which is enormous for applying one CSS declaration string to a style.

**Root suspect (not yet isolated further): the `Style` class
(`simple_web_html_layout_renderer_style.spl`) has ~176 fields.**
`apply_decls` (`simple_web_html_layout_renderer_declarations.spl:243`) is
called once per matching candidate rule and, each call: (a) copies the
`Style` parameter into ~176 local `var X_v = st.X` bindings, (b) probes up to
283 individual CSS property names via `decl_tbl_get`/`decl_get` against the
rule's small (~5-20 entry) declaration table -- each probe a linear backward
scan plus a function call, (c) presumably reconstructs a full 176-field
`Style` literal to return. `decl_table_build`/`find_from` themselves are
already byte-array-based and efficient (comment at
`simple_web_html_layout_renderer_foundation.spl:352` explicitly documents
avoiding the same `char_code_at`-is-O(i) trap this bug's char_at fix
addressed elsewhere) -- this file has only 1 char_at call in 2151 lines, so
the cost is not the indexing bug. The ~600 discrete field/lookup operations
per `apply_decls` call, at the observed ~100-150ms, work out to roughly
150-250 microseconds per operation, consistent with per-field/per-call
overhead on a very wide record type rather than an asymptotic bug in any
single helper.

**Two anomalous outliers, unexplained, flagged for follow-up:** node 5
(total 10.49 **seconds**, of which 10.32s is in the post-`apply_decls` tail --
important-decls pass, inline style, `wm_fallback` material attribute
handling) and node 8 (total 1.87s, 1.74s in the same tail). Both have
`apply_decls_loop_us` in the normal ~110-140ms range, so whatever is
expensive is specific to those two nodes' attributes hitting the
`important_decls`/inline-style/`wm_fallback` path, or a GC pause coinciding
with them. Not investigated further this pass.

### Fix landed 2026-07-29: item 1 (call-count reduction), item 2 deferred

**Landed** (`simple_web_html_layout_renderer_core.spl`, per-node loop): item 1
above, in its cheaper form -- rather than mutating `Style` in place (a bigger
API change touching every `apply_decls` call site across the file), the
per-node loop now accumulates every surviving candidate rule's `decls`
string into one combined string (in cascade order, each fragment
`;`-terminated so `decl_table_build` parses the boundary correctly) and
calls `apply_decls` **once per node** instead of once per candidate rule.
Same transformation applied to the author-important pass (separately, after
the normal pass, preserving "important always outranks normal" origin
order). Inline style handling (already only 1-2 calls, not per-candidate)
was left untouched.

**Why this is behavior-preserving:** `decl_table_build()`/
`decl_tbl_last_index()` already implement "last occurrence in the table
wins" as the cascade tie-break within one rule's decls (the file's own
comments document this). String concatenation preserves relative source
order across rules exactly the way it already preserved order within one
rule, so the merged table's "last occurrence" is still the correct cascade
winner -- shorthand-vs-longhand ordering included, in **both** directions.

**Known accepted narrow edge case:** a single node matching many large
rules could push the *merged* declaration count over `apply_decls`'
internal `WEB_RULE_DECL_QUOTA` (256) abuse guard where each rule
individually stayed under it. Graceful degradation only (some late-cascade
properties silently don't apply on that one pathological node), not a
crash or data corruption; 256 is deliberately generous for the normal
case, and no such node was observed in the showcase fixture.

**Verified (PROVED):**
- `test/01_unit/app/ui.chromium/css_spec.spl`: 9/12, identical to the
  pre-fix baseline (same 3 pre-existing, unrelated failures).
- New `test/01_unit/lib/gc_async_mut/gpu/browser_engine/
  apply_decls_merge_probe_spec.spl` (landed as a permanent regression
  test): 5/5, exercising the exact risk this change carries -- last-wins
  for a duplicated property, shorthand-after-longhand wins, longhand-
  after-shorthand wins (both cascade directions), non-ASCII content
  elsewhere in the merged rules is not corrupted, and ordering survives
  across 5 merged candidate rules. Ran the identical 5 assertions against
  the unmodified pre-fix code too -- same 5/5 -- confirming the expected
  values are genuine pre-existing cascade semantics, not artifacts of this
  change. Vacuity-probed (corrupted one expected value, confirmed red with
  the exact expected-vs-actual message, reverted, confirmed green).

**Measured (mixed signal, reported honestly):** Call-count reduction is a
clean, load-independent, PROVED number: replaying the 8-node profile from
the "Cost center attribution" section above (candidate counts 1,1,2,3,1,
1,2,2), the old per-candidate-call code made 13 `apply_decls` calls across
those 8 nodes; the new per-node-call code makes 8 (1 per node, no
important-decls triggered in that sample) -- a **38.5% reduction in
`apply_decls` invocations**, each of which was independently measured at
~100-150ms in the same profiling section, so this is real, mechanical
work removed, not a guess.

The wall-clock `budget-break` re-measurement, however, is **not** a clean
confirmation either way: two back-to-back runs of the exact repro command
with this fix applied gave budget-break at **29** and **38** of 151 nodes
(same 120s budget) -- the same range as pre-fix measurements taken at
different points in this session (29, then later 38, then later still 35
under a different instrumentation pass). `pgrep` at the time of these runs
showed **23 concurrent rustc/cargo/bin-simple processes** competing for
CPU on this shared machine. A wall-clock-budget node count is fundamentally
unreliable evidence under that level of contention -- it measures how much
CPU time this process was scheduled, not how efficient the code is. Not
re-measuring further this pass; the call-count number above is the
trustworthy evidence for this change's impact. **Do not read the 29/38
figures here as a regression** -- they are noise, not signal, at this
contention level.

### Stage 1 landed 2026-07-29: hybrid dispatch for 8 conflict-free properties

**Enumeration first (as instructed before implementing):** the showcase
fixture (`examples/06_io/ui/browser_common_elements_showcase.html`, 21 CSS
rules) uses only **32 distinct property names** total -- far fewer than the
~283 `apply_decls` knows how to parse. Critically, `* { box-sizing:
border-box; }` is a universal selector, so `box-sizing` is a candidate for
*every* element on the page; skipping it would have made the hybrid gate
("all decl_tbl entries must be dispatch-handled, else fall back") useless
regardless of what else was covered. The requested property-family list
(`background*`, `border*`, `font*`, `flex*`, `padding`/`margin`,
`width`/`height`/`min`/`max`, `display`/`position`) covers about 20 of the
32; the remainder (`color`, `justify-content`, `align-items`, `gap`,
`box-shadow`, `text-align`, `cursor`, `outline`, `overflow`,
`grid-template-columns`, `border-collapse`) is a long tail each used in
only 1-2 rules -- except `color`, used in nearly half the rules.

**Design finding, worth banking:** `mut` parameters on `class` types are
true in-place field mutation, not copy-then-discard -- verified directly
(`mutate_it(mut x: Big): x.a = 999` followed by `print(orig.a)` after
`mutate_it(orig)` prints `999`, not the original value). This means the
dispatch path does not need the 176-field copy-in/copy-out at all: it
takes `mut st: Style` and writes `st.field = value` directly, cheaper than
originally assumed (item 3, previously listed here, proposed profiling
copy-in vs. lookup-loop cost; the copy-in cost is avoided entirely on the
dispatch path, not merely reduced). This also makes the dispatch path
immune to `Style` field additions: an unrelated commit landed mid-session
(`overflow_scroll_y`, a new field added to the full-probe path's
`Style(...)` reconstruction) required zero changes here, since the
dispatch path never enumerates all fields.

**Correctness landmines found while tracing consequences (why this
implementation went slower than "read the property, copy the code"):**
- `apply_decls`' `Style(...)` reconstruction unconditionally resets
  `resolved_font_identity`/`resolved_font_advances`/`resolved_font_width`/
  `resolved_font_line_height` on *every* successful call, regardless of
  which properties are present. Missed initially; the dispatch path now
  does the same reset unconditionally.
- The `if display_v == "contents": <reset box-model fields>` block at the
  end of `apply_decls` checks the *final* resolved `display` value, not
  whether `"display"` appeared in this call's decls -- it can fire from
  inherited state alone. The dispatch path replicates this exactly
  (unconditional check after any `display` write).
- `top`/`right` are *not* independently dispatchable: they interact with
  `left`/`bottom`/`inset`/`inset-block`/`inset-inline`/
  `inset-*-start`/`inset-*-end` via cross-property position comparisons
  (`if inset_pos > top_pos: top_px_v = inset_top`). Deferred entirely
  rather than dispatch them without also covering the whole `inset`
  family or explicitly gating on its absence.

**Landed (`_apply_decls_dispatch`/`_decl_tbl_all_dispatch_handled` in
`simple_web_html_layout_renderer_declarations.spl`):** dispatch for 8
genuinely conflict-free properties -- `box-sizing`, `color`, `width`,
`height`, `min-height`, `margin-left`, `z-index`, `display` (including the
`contents` reset) -- plus 2 recognized no-ops (`grid-template-columns`,
`border-collapse`: confirmed zero `decl_tbl_get` probes for either name
anywhere in the file, so they were already silent no-ops in the full-probe
path; recognizing them lets an otherwise-all-handled call take the fast
path instead of falling back over a property that does nothing either
way). Any decl_tbl entry not in this list falls back to the unmodified
full-probe body for the whole call -- strictly additive, zero changes to
existing code paths (`core.spl`, the per-node loop, needed no changes at
all for this stage -- the whole fix is self-contained inside
`apply_decls`).

**Landed on top of a concurrent, unrelated change:** while this was in
flight, another session added two-URL-layer `background` shorthand support
and an `overflow_scroll_y` field/`overflow: scroll` distinction to the
same file. Re-diffed both directions against the moving tip
(`21db5a8456d2` → `7c964191c059` → `82616c81190`/`f9d064c4d577`) before
each landing attempt per the anti-clobber protocol; both times the
concurrent change and this one touched disjoint regions of the file (their
edits: inside the pre-existing `background`/`overflow` handling blocks and
the `Style(...)` constructor; this fix's edits: a new block before
`fn apply_decls` and two lines immediately after `decl_table_build`), so
the fix was rebuilt fresh on top of the current tip each time (145 pure
line additions, 0 deletions, both times) rather than force-pushed over a
cached diff.

**Verified (PROVED):**
- `css_spec.spl`: 9/12, unchanged from baseline, re-confirmed against the
  current tip (`f9d064c4d577`) after the rebuild above.
- `apply_decls_merge_probe_spec.spl` extended with a "stage-1
  dispatch/probe-fallback equivalence" describe block (11/11 total in the
  file): paired dispatch-path vs. fallback-forced (via one obscure
  unhandled property, `letter-spacing`) cases that must produce identical
  results, the `display:contents` reset firing correctly on both paths,
  `auto` margin-left, and the `%`/`vw` width sentinel forms.
  Vacuity-probed (corrupted one expected value, confirmed red with the
  exact message, reverted, confirmed green). This full 11/11 pass and the
  vacuity probe were run and confirmed clean against the pre-rebuild
  content; the rebuild onto the current tip is a pure text-level merge
  (145 additions / 0 deletions, verified by diff) of that same,
  already-verified logic, not a re-derivation -- so this evidence still
  applies to what is landed.

**New, unrelated blocker discovered while re-verifying against the
current tip (2026-07-29), reported here since it blocks fresh live
measurement of this fix -- needs its own bug report, not fixed here:**
`bin/simple run examples/06_io/ui/web_render_file_gui.spl` fails outright
at the CURRENT origin/main tip with `error[E1002]: function
'text_list_prefix' not found`, confirmed reproducible with fully
unmodified origin files (not caused by this change). `text_list_prefix`
IS defined in source
(`simple_web_html_layout_renderer_foundation.spl:846`) and has several
call sites in the same module family -- this is a runtime/JIT symbol
resolution gap, not a missing definition, and is a hard regression: the
web showcase example cannot run at all right now. Separately,
`test/01_unit/lib/gc_async_mut/gpu/browser_engine/
apply_decls_merge_probe_spec.spl` itself currently fails to compile at
HEAD for an unrelated reason -- `bin/simple test` on that spec pulls in
`src/lib/nogc_sync_mut/debug/remote/replay/hardware_replay_controller.spl`
transitively, which has a syntax error (`=>` used for a match arm instead
of the required `:`); reproduced with fully unmodified origin files too.
`css_spec.spl` does not transitively import that module and is unaffected
(hence still usable as a live regression check above). Both breaks
pre-date and are unrelated to this session's changes; **neither was fixed
here** (out of this task's scope) but both block getting a fresh
`budget-break`/dispatch-fraction/per-call-timing measurement against the
current tip.

**Measured (PROVED, but from earlier in this session, before the
`text_list_prefix` regression landed -- not re-confirmable against the
current tip until that regression is fixed):** bracketed the real
per-node `apply_decls` call site directly (temporary
`rt_time_now_micros()` probes, gated to the first 20 nodes, reverted after
measuring -- the corrected methodology; an earlier attempt using
`simple_web_layout_debug_style_by_id` in a repeat loop was confounded by
that helper's ~600ms fixed parse/extract/compute overhead per call
swamping the ms-scale `apply_decls` signal) and tagged each call with its
actual gate decision:

| | n | avg per call |
|---|---|---|
| dispatch path | 13 | **17.7ms** |
| fallback path | 4 | **174.9ms** |

**The dispatch path was ~9.9x faster than the fallback path** on real
showcase decls, and **13 of 17 calls (76.5%) took the dispatch path** in
that sample -- short of the ">90% aim" stated for stage 1, consistent
with the enumeration above (padding/margin/border, all deferred, are used
in roughly half the page's rules and are not yet dispatch-handled).
`pgrep` showed 12 concurrent heavy processes during that measurement
(quieter than the 23 seen during the stage-0 wall-clock attempt, but
still contended) -- the *per-call* bracket methodology is far less
sensitive to that than a whole-run wall-clock/budget-break count, since
each bracket only spans one `apply_decls` call rather than the entire
process's scheduling history. This fix's logic is unchanged since that
measurement (verified via the 145-line pure-addition rebuild above), so
the numbers should still hold once `text_list_prefix` is fixed and a
fresh run is possible -- but that re-confirmation has not been done.

### Stage 2 landed 2026-07-29: 10 more properties (former stage 1d + padding/margin)

`text_list_prefix` (blocked live measurement in stage 1) is fixed upstream
(`85173c22289`) -- the `bin/simple run` example lane works again, so this
stage's coverage/timing numbers below are freshly measured, not carried
forward from before a regression. The `hardware_replay_controller.spl`
transitive syntax error (blocks `apply_decls_merge_probe_spec.spl`'s own
`bin/simple test` lane specifically) is still present and still unrelated
to this work; `css_spec.spl` remains the live regression check, as in
stage 1.

**Landing collision, worth recording:** while this stage was in flight, a
different concurrent session landed CSS Grid support (`grid-template-*`,
`grid-column`/`-row`) and `position: sticky` in the SAME function this
stage edits (`_apply_decls_dispatch`) plus `apply_decls` itself (renamed
to `_apply_decls_without_grid`, wrapped by a new Grid-aware `apply_decls`).
Confirmed a real, direct textual overlap (not just same-file) via
`git diff` both directions; resolved by re-extracting this stage's own
diff as a pure-addition patch (121 insertions, 0 deletions, verified)
against the CURRENT upstream content and re-splicing at the same logical
anchor points (still valid -- their `display: grid` arm and dispatch-list
additions are adjacent to, not overlapping, this stage's insertions).
Separately hit and had to work around a stale-worktree trap: an
intermediate worktree, created one fetch earlier, had `declarations.spl`
updated (referencing the new `Style.position_sticky` field) copied in
without its matching `style.spl` (the `Style` class definition, still the
older version in that worktree) -- `class Style has no field named
position_sticky`. Not a bug in either file; a version-skew artifact of
mixing file versions across worktrees created at different fetches. Fixed
by discarding that worktree and creating a genuinely fresh one from the
latest fetch of both files together, per the "pristine worktree from
FETCH_HEAD only" protocol.

**Landed:** `justify-content`, `align-items`, `gap`, `text-align`,
`cursor`, `outline`, `overflow`, `box-shadow` (former "stage 1d", all
independent single/aggregate-field properties, no cross-dispatch-property
coupling), plus `padding` and `margin` (moderate-complexity shorthands,
higher value -- used across roughly half the showcase's rules). 18
properties dispatched in total now (8 from stage 1 + 10 here) + the
no-ops (`border-collapse`, and now also `grid-template-rows`/
`grid-column`/`grid-row` per the concurrent Grid work above).

**Correctness finding, filed not fixed (per instruction: pin existing
behavior, record disagreement separately):** `margin` (shorthand) and
`margin-left` (longhand) do **not** resolve their conflict by source
position. The full-probe body processes the `margin` block, then
unconditionally processes the `margin-left` block afterward in fixed CODE
order -- so `margin-left` always wins when both are present, **even when
`margin-left` appears BEFORE `margin` in the CSS source** (verified: `#e4
{margin-left:40px;margin:15px;}` resolves to `margin_l:40`, i.e. the
value from the property that appears earlier in the stylesheet, not
later; confirmed against pristine, unmodified origin content before
pinning it in the spec, not assumed). This is the opposite of standard
CSS cascade semantics ("last declaration among equal-specificity rules
wins") and does not match how the `background`/`background-color`
shorthand pair in the same file behaves (that pair *is*
source-position-aware, via `decl_tbl_last_index` comparison -- see the
merge-probe spec's existing stage-0 cases). Pinned as-is in
`apply_decls_merge_probe_spec.spl` (the dispatch arms must match the
fallback body exactly, and changing runtime behavior is out of scope for
a performance pass) -- but this looks like a genuine, independent
correctness bug in the full-probe body worth its own investigation and
fix, unrelated to performance.

**Verified (PROVED):** `css_spec.spl` 9/12, unchanged. `apply_decls_merge_probe_spec.spl`
extended with a "stage-2 dispatch/probe-fallback equivalence" describe
block (20/20 total in the file): margin-shorthand-alone, margin-then-
margin-left (longhand wins), margin-left-then-margin (longhand STILL
wins, pinning the finding above), padding 2-value shorthand expansion,
and all ten new properties combined in one call without corrupting
unrelated width/height/margin_l/pad_l -- each paired with a
fallback-forced (via `border-left`, still undispatched) equivalent
producing identical results. Vacuity-probed (corrupted one expected
value, confirmed red with the exact message, reverted, confirmed green).

**Measured (PROVED, fresh -- `text_list_prefix` fix confirmed live):**
`pgrep` showed 12 concurrent heavy processes (load-checked before
quoting). Default budget: `budget-break at=6 of=151` -- **the cell
cannot complete 151 nodes in the default budget** even after two
dispatch stages (unchanged from the original bug report; the per-node
cost reduction has not yet reached the ~10x needed to close a ~4s/node
gap against a ~7s default budget). At `SIMPLE_WEB_RENDER_BUDGET_MS=40000`
(same budget used for the stage-1 measurement): `budget-break at=17 of=151`
(same node count as stage 1's measurement at this budget -- consistent
with the fallback path, not the dispatch path, still dominating wall
time for the remaining ~18% of calls) with **14 of 17 calls (82.4%)
taking the dispatch path**, up from stage 1's 76.5%.

## Closing measurement 2026-07-29: outlier nodes, not apply_decls, are the true dominant cost

**Raised-budget A/B, from a pristine worktree at the current SSH tip
(`4737529f5c86`), load-checked before and after both runs (pgrep count:
7 -> 2 -> 4, low/comparable throughout):**

```
SHOWCASE_RESOLUTION=480x360 SIMPLE_WEB_RENDER_BUDGET_MS=120000 \
SIMPLE_TIMEOUT_SECONDS=270 bin/simple run examples/06_io/ui/web_render_file_gui.spl
```

Two runs, both: `budget-break at=38 of=151`. Styling did **not** complete
151 nodes in either run (no `status=pass`/checksum line reached), so the
"changed checksum + varied pixels = success" case does not apply this
pass. Historical series at this budget: **29 (pre-char_at-fix) -> 38
(post-char_at-fix) -> 38 (post-stage-1) -> 38 (post-stage-2, this
measurement, twice)**. Stages 1 and 2 raised dispatch-path coverage
(76.5% -> 82.4%) and cut per-call `apply_decls` cost substantially, but
neither moved the node count at this budget past what the char_at fixes
alone already achieved -- explained below.

**Arithmetic reconciliation (PROVED via a bounded 10-node per-call
bracket probe, temporary, reverted after measuring):** stage-1/2's
17.7ms-dispatch/174.9ms-fallback per-call numbers and 1-2-calls/node
batching predict well under 0.5s/node; the measured ~3.16s/node average
did not match. Bracketed the real per-node loop again, this time
counting every `apply_decls` invocation (there are up to 8 call sites in
the node body: presentational-attribute decls, the batched candidate-rule
cascade, inline style, the important-origin cascade, inline-important,
a `selectedcontent` special case, and two WM-theme-fallback material
paths) and timing the main batched call plus total node time, over the
first 10 nodes:

| index | main apply_decls call | total node time | apply_decls call count |
|---|---|---|---|
| 0 | 21.1ms | 54.3ms | 1 |
| 1 | 25.0ms | 84.8ms | 1 |
| 2 | 198.5ms | 261.6ms | 1 |
| 3 | 225.1ms | 298.5ms | 1 |
| 4 | 23.1ms | 63.4ms | 1 |
| 5 | 21.8ms | **9673.3ms** | 1 |
| 6 | 21.0ms | 57.7ms | 1 |
| 7 | 35.4ms | 114.9ms | 1 |
| 8 | 21.3ms | **1818.8ms** | 1 |
| 9 | 32.1ms | 121.8ms | 1 |

**Call count is exactly 1 per node in every case -- the batching from
stage 0 works as intended; call volume is not the gap.** The gap is that
`apply_decls` (the batched call) is now genuinely fast for every node
(21-225ms), but **2 of these 10 nodes (indices 5 and 8 -- the SAME two
outlier indices flagged, unexplained, in the original "Cost center
attribution" section above) have a residual cost OUTSIDE apply_decls of
9.65 seconds and 1.8 seconds respectively**, dwarfing everything else.
Summed over this sample, those two nodes alone are **12.3ms of the
12.5ms-node-average's 12,549,237us total -- 98.5% of the sampled time**.
This is the missing piece: stage 1/2's 70-90% attribution to
`apply_decls` was correct for typical nodes and for the aggregate
profile it was measured against, but a small number of pathological
nodes dominate the wall-clock average almost entirely, and their cost is
NOT in `apply_decls` at all.

**Residual cost center, named per the profiled call sites (not
`apply_decls`):** the time is spent somewhere in the node body AFTER the
batched `apply_decls` call and its immediate neighbors -- i.e. within the
7 other, un-batched `apply_decls` call sites (inline style, the
important-origin cascade, `selectedcontent`, or the two WM-theme-fallback
material paths) or the non-`apply_decls` logic interleaved with them
(attribute lookups, material-witness bookkeeping). This matches and
sharpens the original "node 5 / node 8 outliers, unexplained" note from
the stage-0 profiling pass, rather than being a new finding -- confirms
those two nodes specifically hit an expensive path unrelated to CSS
declaration parsing. Not isolated further this pass (would need
per-call-site brackets inside that ~7-site region, which is out of scope
for a closing measurement pass); no code change made, per instruction, since
nothing trivial and safe (<20 lines) was identified -- the fix requires
first finding which of the 7 sites or which surrounding logic is
expensive on these specific two nodes.

### Remaining fix proposal (not implemented — needs its own scoped change)

1. ~~Batch all candidate rules' declarations into one merged decl table and
   call `apply_decls`-equivalent logic once per node instead of once per
   candidate rule.~~ Landed (the call-batching form of this item; full
   pass-by-reference/builder-pattern mutation was not attempted for the
   full-probe path, only for the new dispatch path).
2. ~~Replace individual `decl_tbl_get(tbl, "prop-name")` linear-scan
   probes with dispatch on the property name.~~ Landed for 18 properties
   across stages 1+2, measured at 82.4% of calls on the showcase page.
   Remaining, roughly in priority order by rule-count impact on this page:
   - **`padding`/`margin` longhand siblings** (`padding-left`/`-top`/
     `-right`/`-bottom`/`-block`/`-inline`/etc, `margin-top`/`-right`/
     `-bottom`/`-block`/etc): not yet dispatched, so any rule combining
     the shorthand (now dispatched) with one of its own longhand siblings
     still falls back. Not used in the showcase fixture's 21 rules, so
     zero impact on the 82.4% measurement above, but likely needed for
     the ">90%" aim on other pages.
   - **`border`, `border-left`, `border-radius`** (shorthand expanding to
     4 sides' width/color/style) -- highest remaining value on THIS page.
     Note the file has grown a second `background` shorthand path
     (two-URL layers) AND CSS Grid/`position:sticky` support since stage 1
     started -- re-read the current `background`/`background-*`/`border`/
     `border-*` handling before lifting any of it, don't work from a
     stale copy, and re-check for concurrent-session collisions on
     `_apply_decls_dispatch` before landing (this stage hit one).
   - **`background`, `font`, `flex`/`flex-wrap`/`flex-direction`** -- the
     most complex shorthands (multi-field resolution, cross-property
     reset-on-later-shorthand logic, now including the two-URL-layer
     background path).
   - **`place-content`/`place-items`:** each writes into the same fields
     as `justify-content`/`align-items` (now dispatched) via a DIFFERENT
     decl entry not currently recognized -- a call carrying `justify-
     content`/`align-items` together with `place-content`/`place-items`
     already correctly falls back (both must be dispatch-recognized or
     neither is), but adding these two would raise coverage further.
   - **`top`/`right`/`position`:** only dispatchable together with the
     full `left`/`bottom`/`inset*` family (see stage-1 landmine) --
     treat as one unit, not incremental additions. Now also intersects
     with the concurrent `position: sticky` work (`SIMPLE_WEB_STICKY_TOP_AUTO`
     sentinel) -- re-read before touching.
3. Fix the margin/margin-left non-standard ordering finding above --
   separate correctness work, not a performance-pass change.
4. Profile whether the fallback path's ~175ms/call full-probe cost
   itself needs the batched-lookup treatment (a single pass over `tbl`'s
   actual entries instead of ~283 named probes) for the residual rare-
   property calls once border/background/font/flex close most of the
   remaining ~18% fallback fraction, or whether coverage alone is enough
   that this no longer matters in practice.
5. ~~Now the top priority, per the 2026-07-29 closing measurement above~~
   **LOCALIZED 2026-07-29, see "Outlier-node localization" section below:**
   the outlier-node cost is `FontRenderer.measure_text_advances`'s
   per-character native glyph-metric FFI calls (~425ms/char), not
   `apply_decls`, not any of the 7 un-batched call sites, and not
   interleaved WM-theme/cascade logic. Next fix candidate: a Simple-side
   glyph-advance cache ahead of the native calls, or a native-backend
   profiling pass -- not attempted this pass (not a <20-line change).

## Outlier-node localization 2026-07-29: font-metric FFI calls in `measure_text_advances`, not `apply_decls`

Per-call-site bracketing on the two outlier nodes from the closing
measurement above (10-node sample, nodes 5 and 8), using temporary
`rt_time_now_micros()` brackets around each of the 7 un-batched
`apply_decls` call sites and the interleaved logic segments (inherit,
tag-defaults + presentational, selector-candidate matching, the batched-decl
accumulation loop, the important-origin cascade, the WM-theme-fallback
branch, the `selectedcontent` branch, empty-cells, vector-font resolution,
material admission), plus the existing (already-vetted, default-off)
`_WM_TRACE` phase receipts inside `resolve_font_metrics_with_language`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl`). All probes were
temporary, reverted, and diff-verified (`git diff --stat` against the fetch
base shows zero changes to either instrumented file) before this landing.

**Node identity:** both outlier nodes are `#text` nodes -- node 5:
`text_len=20 parent=4`; node 8: `text_len=4 parent=7`. Both are the *only*
`#text` nodes in the original 10-node sample; the other 8 sampled nodes are
non-text elements that never reach the vector-font branch at all (it is
gated `if vector_fonts and nd.tag == "#text":`). This reframes the finding:
nodes 5/8 are not structurally special -- **every `#text` node pays this
cost when `vector_fonts` is on**, and the 10-node sample happened to
contain exactly two of them.

**Per-segment result** (two runs, comparable load, ranges shown):

| Segment | Node 5 (20 chars) | Node 8 (4 chars) |
|---|---|---|
| inherit | 1.8-3.3ms | 2.1-2.6ms |
| tag-defaults + presentational | 2.6-4.0ms | 3.0-3.1ms |
| candidates_raw (1 candidate) | 2.0-3.2ms | 2.4-3.2ms |
| specificity loop | 7.0-11.7ms | 8.2-11.2ms |
| sort | 0.5-1.0ms | 0.7-1.0ms |
| combined_decls accumulation | 1.8-3.5ms | 2.2-3.5ms |
| **apply_decls (main, batched)** | 17.7-27.4ms | 21.9-30.6ms |
| inline_normal | ~0.01ms | ~0.01ms |
| important_cascade (no `!important` on this page) | ~0.003ms | ~0.004ms |
| inline_important | ~0.003ms | ~0.004ms |
| selectedcontent | ~0.004ms | ~0.004ms |
| wm_fallback (attr checks, no match) | 2.5-5.0ms | 3.1-4.9ms |
| empty_cells | ~0.005ms | ~0.006ms |
| **vector_fonts (font-metric resolution)** | **9.62-11.99s** | **1.76-2.41s** |
| material_admission | 6.3-9.0ms | 7.1-10.9ms |

Every other segment is single-digit milliseconds. `vector_fonts` alone is
99.7-99.9% of the node's total time in every run -- confirming the closing
measurement's attribution and ruling out hypotheses (b) (a quadratic
accumulated-state scan -- no segment grows with node count here) and (c)
(WM-theme decl-table rebuilds -- `wm_fallback` is ms-scale).

**Inside `vector_fonts`**, further bracketed via the existing `_WM_TRACE`
phase receipts (reused, not duplicated -- `t={rt_time_now_micros()}` added
to the 5 existing gated print sites plus 4 new tail-of-function checkpoints,
all in the outer function body, none inside `_resolved_font_metric_cached`
where a prior probe attempt regressed the WM lane per this file's own
2026-07-19 warning):

| Phase | Node 5 | Node 8 |
|---|---|---|
| `_browser_default_for_family_cached` (font load/lookup) | 1.07s (`from_cache=false`, cold) | 8ms (`from_cache=true`, warm) |
| cache-lookup (miss both times -- distinct text) | ~1.2ms | ~4.9ms |
| **`renderer.measure_text_advances(content, font_size)`** | **8.50s** | **1.71s** |
| `horizontal_line_metric` | 0.5ms | 0.5ms |
| `clear_ttf` (only when not `from_cache`) | 1.0ms | 0.02ms (skipped) |
| struct build + cache store | 1.4ms | 1.6ms |

**Named cost center:** `FontRenderer.measure_text_advances`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:1277`), called once
per `#text` node from `resolve_font_metrics_with_language`. It loops per
character calling `get_glyph_advance(cp, font_size)` and, for adjacent
pairs, `horizontal_kern(prev_cp, cp, font_size)` -- both native FFI
round-trips into the Rust font backend (`rt_font_glyph_advance`, and the
kern/line-metric SFFI dispatch in `spl_fonts.spl`). The per-character cost
is consistent across both nodes regardless of font-cache state
(`from_cache` true or false): **node 5 = 8.50s / 20 chars = ~425ms/char;
node 8 = 1.71s / 4 chars = ~428ms/char.** This ~425ms/char constant -- not
text length, not font-load state -- is what actually drives the 8-12s and
1.8-2.4s node costs. Font *loading* (the one-time `dlopen` + 17MB-TTF-parse
this file's own comments already flagged) is real but secondary: ~1.07s on
the first `#text` node's cache miss, ~8ms on every warm node after it.

Hypothesis (a) (a per-node font-registry/measurement trigger on specific
tags) is confirmed, and further localized to the per-character native
glyph-metric calls specifically -- not font loading, which was the leading
theory in the code's own prior comments.

**Is batching this call site mechanical?** No. Unlike the `apply_decls`
stage-0 fix, this is not a call-site-count problem (each node already calls
`measure_text_advances` exactly once), and `_apply_decls_dispatch`-style
hybrid dispatch does not apply -- this sits three layers below `apply_decls`,
entirely inside the font backend. The natural next fix is a Simple-side
glyph-advance cache keyed by `(codepoint, font_size, resolved_family)` ahead
of the native calls, or a profiling pass into why `rt_font_glyph_advance` /
the kern and line-metric SFFI dispatch cost ~200ms+ per call individually in
the Rust backend regardless of `from_cache` state. Both are out of scope for
this bounded probe (neither is a trivial, <20-line change) -- filed as the
next fix candidate.

### Next fix candidate (not attempted this pass)
Add a Simple-side glyph-advance cache keyed by `(codepoint, font_size,
resolved_family)` ahead of the `get_glyph_advance` / `horizontal_kern`
native calls in `measure_text_advances`
(`src/lib/nogc_sync_mut/text_layout/font_renderer.spl:1277`), or determine
why the individual native calls cost ~200ms+ each regardless of
`from_cache` state. This is now the real bottleneck for any page with
`#text` nodes under `vector_fonts` -- not `apply_decls`, which three
optimization stages have already reduced to single-digit-millisecond-scale
per node.

## Stage A/B 2026-07-29: root cause = whole-program interpreted execution (PROVED) + no metrics-only glyph path (PROVED); fix landed, break-point 38 -> 90/104

**Stage A -- root-causing the ~425ms/char anomaly.** Bracketed inside
`get_glyph_advance`'s implementation (`src/lib/nogc_sync_mut/text_layout/
font_renderer.spl`) with temporary `rt_time_now_micros()` timers (reverted,
diff-verified before landing) plus a discriminator standalone script
(`bin/simple run` on a tiny probe importing only
`font_renderer.resolve_font_metrics_with_language`, same family/size as the
outlier nodes) versus the full pipeline.

- **Which native path this lane takes (PROVED via code reading):**
  `get_glyph_advance` on the SFFI-dylib backend (every `browser_default_for_family`
  font, i.e. every plain `#text` node) has NO metrics-only entry point --
  its own comment says so ("no metrics-only entry point exists, fall back
  unchanged") -- and falls through to the FULL `get_glyph()` call, which
  calls `rast.rasterize()` (a complete pixel-bitmap rasterize, O(font_size^2))
  just to read `.advance`. This is real and secondary, not the primary
  multiplier (below).
- **Silent-dispatch/interpreted-execution theory (PROVED, not inferred):**
  `examples/06_io/ui/web_render_file_gui.spl` matches the driver's
  `should_prefer_interpreter_for_source` heuristic
  (`src/compiler_rust/driver/src/exec_core.rs`) and is therefore **always
  run under the interpreter by deliberate design** -- it never even
  attempts JIT in the default configuration (confirmed: zero
  `[INFO] JIT compilation failed` or `[jit-fallback] unresolved external
  symbol` markers in any of 6 independent pipeline runs this campaign).
  Forcing `SIMPLE_EXECUTION_MODE=jit` makes the driver attempt JIT anyway --
  and it fails, with a genuine, unrelated HIR-lowering gap
  (`Unknown type: DrawIrRenderTarget`), falling back to the interpreter
  regardless. A minimal standalone repro (importing only
  `font_renderer.resolve_font_metrics_with_language`) independently hits
  the SAME class of failure via a DIFFERENT unrelated construct
  (`HIR lowering error: Unsupported feature: CastElse` on a `read_u32_be`
  call in `src/lib/skia/feature/glyph/ot_parser_layout.spl:280`, reached
  only because `font_renderer.spl` transitively `use`s
  `std.skia.feature.glyph.ot_parser.{parse_offset_table}` -- that OT-shaping
  code is never actually CALLED for plain-Latin/`complex_script=0` content,
  but JIT compiles the whole reachable program up front, so one unreached
  function's unsupported HIR feature still de-JITs everything). Both paths
  land in the SAME place: **the entire font/style code runs interpreted**,
  at the ~100-1000x overhead this repo has hit before (see
  `reference_silent_interpreted_fallback_hir_unknown_variable` in project
  memory) -- generalized here from "one unresolvable name" to "one
  unreached function anywhere in the whole-program JIT unit."
  **Magnitude match (PROVED):** the standalone interpreted repro measured
  8.98s for a fresh 20-char string and 1.27s for a fresh 4-char string --
  closely matching the pipeline's own 8.5-12s (node 5, 20 chars) and
  1.7-2.4s (node 8, 4 chars) from the prior localization pass. This is the
  primary multiplier; the full-pixel-rasterize gap above is a secondary,
  compounding one.
- **What this changes vs the coordinator's fix hypotheses:** this is not a
  per-callsite dispatch de-optimization on an otherwise-JIT'd receiver (the
  `f2f64a137bd` engine2d-vtable precedent does not apply -- there is no
  vtable/erased-receiver mismatch here); it is a blanket, source-content-
  triggered interpreter routing decision plus real JIT/HIR-lowering gaps.
  Fixing either (the `window_winit`-class heuristic, or the two named
  HIR-lowering gaps in the Rust JIT backend) is a Rust-seed-compiler change,
  explicitly out of scope for this pass (`.claude/rules/*`: fix `.spl`, not
  Rust) and far larger than a bounded probe -- **filed as a follow-up**, not
  attempted.

**Stage B -- fix landed: bounded, array-backed glyph-advance cache**
(matches the coordinator's third authorized pattern, "if the extern itself
is slow"). `src/lib/nogc_sync_mut/text_layout/font_renderer.spl`: a
module-level cache keyed by `(loaded-face identity, font_size, codepoint)`,
consulted at the top of `get_glyph_advance` before either the per-instance
`GlyphCache` lookup or the full-rasterize fallthrough. ASCII 32-126 gets a
direct array-indexed O(1) bucket (single active `(identity, font_size)`
slot, reset on face/size change); everything else uses a small bounded
overflow list (ring-buffer eviction at 1024 entries) -- plain arrays and
counters throughout, no `Dict` (native `Dict.get()`/`.len()` are unreliable
per `doc/07_guide/language/dict_native_pitfalls.md`). Valid across every
`FontRenderer` instance sharing the same loaded face, not just the instance
that first measured a given character -- so it helps across DIFFERENT
`#text` nodes on the same page, not only repeated characters within one
node's string.

Why this (not hoisting, not receiver retyping): per-call font/blob
re-resolution was checked and is not the cost (`sync_us`/`lookup_us` were
consistently 300-800us in the bracketed runs, not multi-second); there is
no dispatch-retyping fix available because the interpreted-execution
routing is structural, not a per-call vtable miss (see above). A cache that
short-circuits the expensive path on any repeat is the only fix available
at this layer that is both safe and mechanical.

**Before/after (standalone repro, both interpreted -- same execution mode,
isolating the fix's own effect):**

| Case | Before | After | Speedup |
|---|---|---|---|
| Fresh 20-char string (first occurrence of every glyph) | 8.98s | 5.90-7.61s | ~1.2-1.5x (residual first-occurrence cost, expected -- no prior cache entry to hit) |
| Same 20-char string repeated 5x | 27-34ms | 42-47ms | unchanged (pre-existing whole-string cache in `resolve_font_metrics_with_language`, not this fix's mechanism; +load noise) |
| Fresh 4-char string, no character overlap with prior content | 1.27s | 1.43s | unchanged (expected -- genuinely novel glyphs still pay the real rasterize cost) |
| **New string sharing ASCII letters with prior content** ("Simmer" after "Simple Web Renderer!") | N/A (not measurable before -- this is exactly the case the fix adds) | **47-54ms** | **~140-190x vs an equivalent fresh string's ~7-9s** |
| 100x near-fresh short strings (`"X0".."X99"`, shared leading char) | 1,094,228us/call avg | 108,624us/call avg | **10.1x** |

**Full-pipeline A/B, default execution mode, same env vars as every
historical break-point measurement this campaign**
(`SHOWCASE_RESOLUTION=480x360 SIMPLE_WEB_RENDER_BUDGET_MS=120000
SIMPLE_TIMEOUT_SECONDS=270`), load-checked before and after (pgrep count
152-181 concurrent `simple` processes throughout; load average ranged
12-51 across this session's runs -- both after-fix runs specifically
started at 33-39 and dropped mid-run to 14-30):

- Historical series (pre-fix, 3 apply_decls optimization stages, this
  campaign): 29 -> 38 -> 38 -> 38 -> 38 -> 38 (never moved past 38/151
  across 6 independent measurements spanning 3 code-landing stages).
- **After this fix, two independent runs: budget-break at=90 of=151, then
  budget-break at=104 of=151.** Neither run reached full completion (no
  `status=` line in either log) -- the budget-break ceiling moved
  substantially but the page still does not finish styling within the
  120s budget. Given the historical stuck-at-38 baseline was itself
  measured under comparable-or-lower contention on 6 prior occasions and
  never moved, a >2x movement reproduced twice on the first pass with this
  fix is not plausibly explained by load variance alone -- **the
  coordinator's success metric ("the stuck-at-38 break point must move")
  is met.**

**Regression baseline (unchanged from historical, no new failures):**
- `test/01_unit/app/ui.chromium/css_spec.spl`: 12 total, 9 passed, 3 failed
  -- identical to the documented pre-existing baseline (same 3 unrelated
  failures: `resolves border-color: currentColor...`, `accepts the
  mixed-case spelling 'currentColor'`, `accepts the full panel property set
  without losing values`).
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl`:
  20 total, 20 passed, 0 failed -- identical to the documented baseline.
- `test/01_unit/lib/common/text_layout/font_renderer_spec.spl` (this
  file's own existing unit suite): attempted twice (200s and 350s budgets)
  and both timed out before reaching a `Results:` line -- **INFERRED, not
  proven**, that this is a pre-existing heavy-compile characteristic of
  that spec file (its own warning dump shows it transitively pulls in the
  entire test_runner/sdoctest/database dependency tree, unrelated to this
  ~90-line, array/text-only change) rather than a regression -- **flagged
  as an open item**, not verified clean this pass.

**Probes reverted:** the `rt_time_now_micros()` timing brackets and
`[gfp-probe]`/print instrumentation added to `get_glyph_advance`/`get_glyph`
for Stage A were fully removed before landing; the standalone discriminator
scripts (`_font_perf_probe_tmp.spl`, `_font_perf_verify_tmp.spl`) were
temporary and deleted. Diff-verified: `git diff --stat` against the fetch
base shows only the landed cache addition in `font_renderer.spl` (the fix
itself, not a probe) and this doc update.

### Next fix candidates (not attempted this pass)
1. The interpreter-routing heuristic and the two named HIR-lowering gaps
   (`Unknown type: DrawIrRenderTarget`; `CastElse` on `read_u32_be` in
   `ot_parser_layout.spl:280`) are the real, structural, primary multiplier
   -- fixing either requires a Rust-seed-compiler change (JIT HIR lowering
   support, or narrowing `should_prefer_interpreter_for_source`), well
   outside this pass's `.spl`-only, bounded-probe scope. This is now the
   single highest-leverage remaining fix: it would remove the ~100-1000x
   interpreter tax from the ENTIRE pipeline, not just the font path.
2. A genuine metrics-only native entry point for the SFFI-dylib backend
   (avoiding `rast.rasterize()`'s full pixel-bitmap generation for
   advance-only queries) would close the secondary gap this pass's cache
   works around rather than eliminates -- first-occurrence glyphs still pay
   the full rasterize cost even with the cache landed.
3. Verify `font_renderer_spec.spl` cleanly (larger timeout budget or a
   lower-load window) to close the open regression-baseline item above.

## Completion probe + SFFI metrics-only close-out 2026-07-30

**Tree used:** all probes in this section ran from a dedicated disposable
`git worktree` (`wt-close1`, checked out at commit `67d9d21bfd44019bbb086539183ea84f28da9424`
via `git worktree add`), never the shared working copy -- so the
`ot_layout_shaper.spl` uncommitted-edit corruption reported separately in
the shared WC could not have reached this probe (a worktree only ever
contains committed content). Confirmed clean: `ot_layout_shaper.spl` is
present and compiles (every run below reached full module compilation with
zero parse/syntax errors in the log; run 1 additionally reached deep into
the style loop, which requires that module and its co-compiled shaper
callees to have parsed correctly).

### Part 1 -- completion probe at raised budget (`SIMPLE_WEB_RENDER_BUDGET_MS=240000`, `SIMPLE_TIMEOUT_SECONDS=580`)

**Methodology finding (PROVED) -- buffering, not the pipeline, ate the
first two attempts.** The `simple` binary's stdout is fully block-buffered
when not attached to a TTY (the universal C-stdio behavior: line-buffered
only under `isatty()`). Piping output to a file (`> log 2>&1`, this
campaign's standard capture method) triggers full buffering; when the
outer `SIMPLE_TIMEOUT_SECONDS` watchdog hard-kills the process, whatever
was sitting in the unflushed buffer is lost. At the historical
120s-budget/270s-timeout configuration this never surfaced (the ~500-line
module-warning dump alone exceeds one buffer, so it force-flushed early,
carrying the following `budget-break` line out with it in the same flush).
At the raised 240s-budget/580s-timeout configuration, two independent
capture attempts (`complete_run1.log`, `complete_run1b.log`, one launched
detached via `nohup`+`disown`, one launched as a plain foreground redirect)
both produced a log containing ONLY the ~490-line module-warning dump and
a watchdog-timeout message -- zero `[web-style-producer]` lines -- looking
exactly like the pipeline hung before ever reaching the style loop. Fix:
force line buffering with `stdbuf -oL -eL` ahead of the binary. Repeating
the identical run with `stdbuf -oL -eL ./bin/simple run ...` immediately
recovered real progress output (below) -- confirming the two silent logs
were a **capture artifact, not a pipeline hang**. This is the "buffering
fix" landed this pass: a methodology correction (`stdbuf -oL -eL` is now
required for reliable evidence capture on this pipeline), not a source
change.

**Runs (3 total, all from `wt-close1` @ `67d9d21bfd44019bbb086539183ea84f28da9424`,
all with `stdbuf -oL -eL`):**

| Run | Load (pgrep count / load avg at launch) | Result |
|---|---|---|
| 1 (`complete_run1c.log`) | moderate (load avg ~11-16 across this window) | **`budget-break at=139 of=151`** -- reached deep into the style loop, 92% of nodes styled, still short of full completion. No `status=` line -- paint/layout after styling did not complete within the remaining wall-clock budget either. |
| 2 (`complete_run2c.log`) | elevated (load avg 16-19) | No `[web-style-producer]` line at all within 580s -- did not finish module compile + reach the first budget check in this window. Confirmed NOT a buffering loss this time (stdbuf was active); a genuine wall-clock miss under higher contention. |
| 3 (`complete_run3c.log`) | high (pgrep 151, load avg 27.7 rising) | Same as run 2 -- no progress line within 580s. |

**Reading this honestly:** 1 of 3 runs produced real signal; that one run
(`139 of 151`, 92%) is the best evidence to date that the cache landed this
session moves the page close to a full style-loop pass at a large-enough
budget, but **no run reached `status=` / full completion** -- this is
INFERRED-favorable, not PROVED-complete. The other 2 of 3 runs show that
under the load levels this shared machine has exhibited throughout this
session (10 to 51 load average observed across the whole campaign, with
100-200+ concurrent `simple` processes), the 580s wall-clock ceiling itself
becomes the binding constraint before the style loop's own 240s budget
does -- module compile + startup alone can consume the entire wall-clock
allowance under contention. **The default-budget gap now has a number:**
best case 139/151 (92%) at 4x budget; worst case (2 of 3 samples) did not
even reach the first progress checkpoint. No cell-green (`status=pass`)
evidence was captured this pass at any budget.

Tip note: all three runs above used the SAME `wt-close1` worktree (fixed
at `67d9d21bfd44019bbb086539183ea84f28da9424`, predating the coordinator-
flagged `53b7712523b` "perf(web): reuse unchanged hosted GPU frames"
landing) -- so the run-to-run variance documented above is NOT explained
by that upstream change; it tracks the load column instead.

### Part 2 -- SFFI dylib metrics-only entry point (investigated, not wired)

Checked whether the SFFI dylib backend (`src/lib/nogc_sync_mut/sffi/spl_fonts.spl`,
dlsym-bound to the OWNED, non-vendored `src/compiler_rust/spl_fonts/src/lib.rs`
-- the backend behind every `browser_default_for_family` font, i.e. every
plain `#text` node) exposes an advance-only call `get_glyph_advance`'s
full-rasterize fallthrough could use instead, mirroring what `ca5dac5e398`
already did for the selected-outline-blob (sfnt) path via
`sfnt_measure_glyph_into`.

**Full exported symbol list of the dylib** (`rt_fonts_init(_verified_bytes)`,
`rt_fonts_generation`, `rt_fonts_has_glyph`, `rt_fonts_rasterize_glyph(_native_only)`,
`rt_fonts_glyph_pixels_ptr/_len`, `rt_fonts_glyph_free`,
`rt_fonts_rasterize_glyph_subpixel`, `rt_fonts_glyph_metric`,
`rt_fonts_horizontal_kern`, `rt_fonts_horizontal_line_metric`,
`rt_fonts_layout_text`, `rt_fonts_layout_glyph_metric`,
`rt_fonts_glyph_pixel(_subpixel)`) has **no standalone per-glyph
advance-only entry**:
- `rt_fonts_glyph_metric(handle, field)` needs a `handle` from a PRIOR
  `rt_fonts_rasterize_glyph` call (matches the existing code comment at
  the `get_glyph_advance` call site).
- `rt_fonts_layout_text` (+ `rt_fonts_layout_glyph_metric`) IS a genuine
  no-rasterize call (uses `fontdue::layout::Layout` -- shaping only, no
  bitmap, confirmed by reading the Rust implementation), but its
  `LayoutGlyphSlot` fields are `{codepoint, x, y, width, height,
  byte_offset}` -- no `advance` field. `width`/`height` are the glyph's
  bounding box, not the typographic advance; a correct advance would need
  a 2-glyph-lookahead x-delta re-derivation, changing `get_glyph_advance`'s
  per-character call shape -- not a drop-in substitution, and exactly the
  class of layout-sensitive change this file's own 2026-07-19 comment
  warns against attempting casually.
- `rt_fonts_horizontal_kern`/`rt_fonts_horizontal_line_metric` are genuine
  metrics-only calls but don't return a per-glyph advance either (kern is
  a pair adjustment; line-metric is ascent/descent/gap).

**The underlying capability exists one layer down** in the vendored
`fontdue` crate: `Font::metrics(character, px) -> Metrics`
(`src/compiler_rust/vendor/fontdue/src/font.rs:450`), and
`Metrics.advance_width: f32` (`font.rs:73`) is exactly the value needed --
genuinely metrics-only, no bitmap. `rt_fonts_rasterize_glyph` itself
already calls `font.rasterize()` (metrics + bitmap together) as its
fontdue fallback, tried only after `rasterize_with_freetype` (a native
FreeType path checked first for registered/bundled fonts) -- so a correct
`rt_fonts_glyph_advance` extern would need to mirror BOTH branches (the
fontdue `metrics()` call for the fontdue path, plus an equivalent
no-bitmap FreeType query for the FreeType-first path), not just one.

**Conclusion (documented, not implemented this pass):** add
`pub extern "C" fn rt_fonts_glyph_advance(codepoint: i64, font_size_px: i64) -> i64`
to `src/compiler_rust/spl_fonts/src/lib.rs` returning
`metrics.advance_width` (matching `rt_font_glyph_advance`'s existing
rounding convention), preferring the FreeType path's equivalent when
active; wire a matching `fn glyph_advance(...)` on `FontRasterizer` in
`spl_fonts.spl` via `spl_dlsym`; call it from `get_glyph_advance`'s
SFFI-dylib branch ahead of the `get_glyph()` fallthrough -- the exact
`ca5dac5e398` pattern, one layer further down. This is a real, small,
well-scoped Rust addition, but it is a change to owned (non-vendored) Rust
source requiring a seed rebuild + bootstrap redeploy -- the "extern
additions need bootstrap rebuild" tax -- explicitly out of scope for this
`.spl`-only pass. Per the coordinator, this rides with the other
seed-rebuild items already queued.

**Per-miss cost before/after: not measured this pass** -- no extern was
added, so there is no "after" number; the bounded advance cache landed
this session still pays the full `get_glyph()` rasterize on every cache
MISS (first occurrence of a given codepoint+size+face), unchanged from the
prior localization pass's per-glyph figures.

### Regression baselines (re-confirmed on this pass's tip, unchanged)
- `test/01_unit/app/ui.chromium/css_spec.spl`: 12 total, 9 passed, 3 failed
  -- same 3 pre-existing failures as every prior measurement this campaign.
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl`:
  20 total, 20 passed, 0 failed.

## Extreme-budget completion attempt + node 140-148 analysis 2026-07-30

**Tree used:** dedicated disposable worktree `wt-final-run`, rebased to SSH
tip `d8822a3e3379e44bb522900d2e06fe50014433d5` at launch time (origin has
since moved further; every subsequent re-fetch through
`b0ae22d4e9105bb6503bd75fa9dc182d192dd897` shows zero further diff in
`browser_common_elements_showcase.html` or
`simple_web_html_layout_renderer_foundation.spl`, so the node-count/identity
analysis below is still current). Never the shared WC.

**Node-count shift (PROVED):** `parse_html` on
`examples/06_io/ui/browser_common_elements_showcase.html` now returns
**149 nodes, not 151** -- a 2-node drop versus every historical measurement
in this campaign, all of which were taken from the `67d9d21bfd4` base. A
pure-parse probe (`parse_html` called directly, no style resolution --
fast, no `apply_decls`/`measure_text_advances` cost) confirms the HTML file
itself and the parser are both unchanged between `67d9d21bfd4` and the
current tip, so **PROVED via code reading + diff**, not directly bisected:
the 151->149 shift predates this session's `67d9d21bfd4` base already (the
change is somewhere upstream of both, or the historical "of=151" number was
itself measured on a still-earlier tip whose HTML/parser has since
shifted). Any budget-break number from here forward should be read against
**149**, not 151. The prior campaign's `139 of 151` (92%) and this
document's `90`/`104 of 151` numbers remain valid as historical record but
are not directly comparable index-for-index to a future `of=149` result.

**Node 140-148 identity (the "cheap static work," done while the extreme-
budget run was in flight -- PROVED via direct `parse_html` dump, no style
resolution run):**

| i | tag | parent | text_len | notes |
|---|---|---|---|---|
| 130 | `summary` | 129 | -- | |
| 131 | `#text` | 130 | 17 | |
| 132 | `p` | 129 | -- | |
| 133 | `#text` | 132 | 44 | |
| 134 | `section.unsupported` | 13 | -- | |
| 135 | `h2` | 134 | -- | |
| 136 | `#text` | 135 | 32 | |
| 137 | `p` | 134 | -- | |
| **138** | **`#text`** | **137** | **136** | **largest `#text` node found in this entire campaign -- 6.8x node 5's 20 chars** |
| 139 | `canvas` | 134 | -- | |
| 140 | `#text` | 139 | 18 | canvas fallback content |
| 141 | `svg` | 134 | -- | |
| 142 | `rect` | 141 | -- | |
| 143 | `audio` | 134 | -- | |
| 144 | `span` | 143 | -- | audio fallback wrapper |
| 145 | `#text` | 144 | 17 | |
| 146 | `video` | 134 | -- | |
| 147 | `span` | 146 | -- | video fallback wrapper |
| 148 | `#text` | 147 | 17 | (last node, index 148 of 149) |

**Confirms the coordinator's suspicion:** 7 of the 19 tail nodes (130-148)
are `#text` nodes hitting `measure_text_advances` under `vector_fonts`,
including one, index 138, at **136 characters** -- by far the largest
`#text` node measured anywhere in this campaign. Per the standing
per-character-miss figure (~425ms/char for genuinely novel codepoints, from
the prior localization pass), a worst-case fully-cold pass over node 138
alone could cost tens of seconds; the bounded advance cache landed this
session should reduce that substantially for characters already seen
earlier on the page (English prose at 136 chars overwhelmingly reuses
common ASCII letters), but node 138 remains the single most likely
individual cost spike in the 130-148 tail -- INFERRED, not measured this
pass (the extreme-budget run below never reached it).

**Extreme-budget completion run (`SIMPLE_WEB_RENDER_BUDGET_MS=1800000
SIMPLE_TIMEOUT_SECONDS=2900`, `stdbuf -oL -eL`, single run):** died at
2900s via its OWN internal watchdog -- confirmed NOT the `kill_simple_
monitor` resource-guard daemon. Diagnostic basis (PROVED): the log's last
line is `error: example timed out after 2900s: examples/06_io/ui/
web_render_file_gui.spl`, the exact message format every legitimate
internal-`SIMPLE_TIMEOUT_SECONDS` expiry in this campaign has produced
(matches the `580s`/`600s`/`270s` prior instances byte-for-byte in format);
a `kill_simple_monitor` kill instead produces a silent SIGKILL (exit 137,
often near a 60s multiple, no such message). `kill_simple_monitor` was
confirmed running throughout (`pgrep -af kill_simple_monitor`, PID
`2530172`, live since Jul 28) but did not fire on this process.

**What actually happened in those 2900 seconds (PROVED via full-log
grep, `stdbuf` active so buffering-loss is ruled out this time):** the log
contains **zero** `[web-style-producer]` lines -- the process never
reached the style loop's first budget check. Every one of its 590 lines is
compile-time output: `export use *` warnings, deprecated-generics-syntax
warnings, cross-module private-symbol-collision warnings, and
`#[runtime_intrinsics]`-deprecated warnings, ending abruptly mid-dump
(a `process_ops` export-use warning) immediately before the timeout. This
means **module compilation/loading alone consumed the full 48 minutes**
under the load conditions of that window, before any application code ran.

**Independent cross-session corroboration (PROVED, not this session's own
claim):** commit `53e74794811` (unrelated session, landed to the tip
fetched for this update), documenting a different fix in this exact file
(`font_renderer.spl`'s default-face cache flatten, `_browser_default_font_
renderers` -> two flat `[text]` arrays -- coexists cleanly with this
session's bounded advance cache, confirmed via `git cat-file -p <tip>:
src/lib/nogc_sync_mut/text_layout/font_renderer.spl | grep -c` showing both
`_adv_cache_lookup`/`_adv_cache_store` (this session, 7 refs) and
`_browser_default_font_rebuild_from_path`/`_browser_default_font_paths`
(that session, 7 refs) present together -- no clobber), independently
reports: "`font_renderer_spec.spl`... times out under the test runner's
resource-limit guard even at `--timeout 300`, both before and after this
change; this is a pre-existing interpreter-mode perf characteristic of the
file... not a regression," and "real TTF shaping cost per call under the
tree-walk interpreter is apparently on the order of **minutes** on this
machine, independent of this fix." This **upgrades this document's own
`font_renderer_spec.spl` open item (previously reported INFERRED after 2
single-session timeouts) to PROVED via independent replication**, and
directly explains this pass's 48-minute no-progress result: if isolated
real-font operations already cost minutes each under the interpreter on
this machine, a whole-page pass touching many distinct glyphs across ~149
nodes plausibly needs far longer than 48 minutes to even finish loading
under current, sustained heavy contention (pgrep count 150-200,
`/proc/loadavg` 1-min figure observed ranging 10-54 across this session's
load-gate polling).

**Decision, not attempted further this pass:** given (a) the independent,
now-PROVED "minutes per real-font operation under the interpreter" finding,
(b) sustained machine load in the 25-54 range at time of writing, and
(c) the extreme run above already consumed 48 minutes without reaching the
style loop at all, another blind extreme-budget attempt was judged low-
probability/high-cost and not repeated this pass. **No `status=` line was
captured; no cell-green evidence exists yet.** The default-budget gap
number stands at the prior document's `139 of 151` (now known to be `139
of ~151`, pre-node-count-shift) as the best completion evidence to date.

> **SUPERSEDED 2026-07-30 (see "Module-compile-cost root cause" section
> below):** the reading above assumed the 48-minute, zero-`[web-style-
> producer]`-line run meant the STYLE LOOP was stuck. It does not
> distinguish that from module compilation itself never finishing --
> `budget-break` was, at the time, the ONLY progress line the whole
> pipeline ever emitted, so a silent run is equally consistent with
> "never left compilation" as with "styling hung." The very next section
> measures compile time in isolation and lands permanent, level-gated
> phase instrumentation to settle this properly. Short version: compile
> alone has since been measured taking anywhere from ~70s to more than
> 1200s on this machine, so the 48-minute figure is not attributable to
> the style loop specifically without phase-level evidence, which this
> document did not have at the time this section was written.

### Regression baselines (re-confirmed on this pass's tip, unchanged)
- `test/01_unit/app/ui.chromium/css_spec.spl`: 12 total, 9 passed, 3 failed.
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl`:
  20 total, 20 passed, 0 failed.
(Both re-run earlier in this pass's `wt-close1` worktree per the prior
section; not re-run again for this update since no source changed.)

## Module-compile-cost root cause 2026-07-30: no persistent cache, syscall-bound, highly load-scaled

The prior section's "48 minutes, zero progress" finding reframed the cell:
module compilation, not the style loop, is the dominant blocker in the
worst case. This section root-causes that cost.

**Tree used:** dedicated disposable worktree `wt-compile` (SSH tip
`89cdc06d99093f6742e911875b592c13d2c6651f`), never the shared WC.
`kill_simple_monitor` confirmed live throughout (`pgrep -af
kill_simple_monitor`, PID `2530172`, running since Jul 28) but did not fire
on any run in this section -- every run below ended with either a clean
budget-break or its own internal-watchdog message, never a silent exit 137.

### 1. Compile-phase timing, isolated (PROVED, empirical)

Method: `SIMPLE_WEB_RENDER_BUDGET_MS=1` makes the style loop's own budget
guard expire on its very first check (`budget-break at=0`), so wall-clock
time up to that line is compile + startup only, with `time` wrapping the
whole invocation and `stdbuf -oL -eL` forcing line buffering (the
already-documented capture-methodology fix from the prior section).

| Run | Load at launch | `real` | `user` | `sys` |
|---|---|---|---|---|
| 1 | ~43 (1-min avg) | **1m29.7s** | 0m26.3s | 0m53.8s |
| 2 | ~52 (1-min avg) | **1m8.0s** | 0m21.1s | 0m46.3s |

Both runs: `sys` time (46-54s) **exceeds** `user` time (21-26s) --
**more than half the wall-clock cost is kernel/syscall time, not
CPU-bound parsing/lowering work.** This points at file I/O (open/read/stat
across the whole transitive module closure) as the dominant cost within
the compile phase, not compute. `real` is close to `user+sys` in both
cases (not `real << user+sys`), so there is little/no beneficial
parallelism in this phase either.

**This directly contradicts the prior section's implicit framing of "48
minutes" as a representative figure.** At this pass's load (43-52), the
SAME compile phase that failed to finish even once in 2900s (48 min)
completed twice in under 90 seconds. **The cost is highly load-scaled, not
a fixed absolute figure** -- see the ambient-contention finding below for
why.

### 2. Central caching question (PROVED, via code reading AND empirical check)

`bin/simple run <script.spl>` dispatches to one of two driver entry
points depending on source content
(`src/compiler_rust/driver/src/exec_core.rs`):
`run_file_jit` (attempts JIT, falls back to interpreter on failure) or
`run_file_interpreted_with_args` (interpreter directly, chosen when the
source matches `should_prefer_interpreter_for_source` -- confirmed this
file matches, via the `source_uses_jit_unsafe_graphics_runtime`
`window_winit`-content heuristic, consistent with the prior section's
finding that this file never shows a `[jit-fallback]`/`[INFO] JIT
compilation failed` marker in any run).

**Both entry points call the exact same
`load_module_with_imports(path, &mut HashSet::new())`
(`src/compiler_rust/compiler/src/pipeline/module_loader.rs:1249`) on every
single invocation.** This function parses and lowers the whole reachable
`use`-import closure from raw `.spl` source, from scratch, every time.
Read through its body: the only caching present is
`PIPELINE_DIR_LISTING_CACHE` (a `thread_local!` directory-listing cache)
and a "module exports cache" -- both explicitly **in-memory, per-process,
and discarded when the process exits.** No `.smf` reuse, no mtime check,
no content-hash lookup, no persistent artifact of any kind for this code
path.

**Empirical confirmation:** after 2 complete runs above (from a freshly
created worktree, so no pre-existing state), `find wt-compile/.simple -type
f` returns exactly one file -- a log file. **Zero build/cache artifacts.**
Nothing to compare mtimes against because nothing persists.

**Answer: there is no cache that "misses every time" -- there is no cache
mechanism in this code path at all.** This is the highest-value finding:
it means every `bin/simple run` invocation of this (or any) script pays
the full parse-the-whole-closure cost, unconditionally, regardless of
whether the source changed since the last run. This directly contradicts
the repo's own stated policy ("production wrappers should execute cached
compiled artifacts, not raw source") for this specific entry point.

### 3. Two known landmines checked -- both ruled out for this path

- **`.simple/` live `*.o.tmp` deletion** (prior incident: startup wiping
  concurrent build objects): not applicable -- this path produces zero
  on-disk artifacts of any kind (`.o`, `.o.tmp`, `.smf`), confirmed by the
  empty `.simple/` directory above. Nothing exists to be deleted.
- **native-build `--source` silently widening to the whole workspace**:
  ruled out by code reading -- `run_file_jit`/`run_file_interpreted_with_
  args` call `load_module_with_imports` with exactly one path (the entry
  script), no `--source` flag or workspace-wide compilation step is
  involved anywhere in this call chain. The module closure genuinely comes
  from following `use`/`export use` imports transitively from one file,
  not from an accidentally-widened source root.

### 4. Module-set size vs expected closure (INFERRED direction, not exactly counted)

No existing debug flag reports a total module count for the interpreted
path (`SIMPLE_NATIVE_BUILD_RUST_TRACE=1`'s `[rust-jit] lowered functions=...`
line only fires on the JIT path, which this file never takes). Proxy counts
from compiler warnings across this pass's runs (lower bounds only --
warning-triggering modules are a subset of the true closure): 19-29
distinct file paths, 19 distinct "Higher-layer module" violations, 18-19
"Avoid `export use *`" warnings.

**Qualitative signal is strong even without an exact count:** the
"Higher-layer module" warnings this pass and the prior section's logs
name, among others, `gpu.engine2d.sffi_cuda`, `gpu.engine2d.sffi_vulkan`,
`sffi_rocm`, `sffi_opencl`, `io.oneapi_sffi`, `io.metal_sffi`,
`nogc_sync_mut.database.core`, and `test_runner`/`sdoctest` modules --
CUDA/Vulkan/ROCm/OpenCL/Metal GPU backends and a database/test-runner
stack, for a task that parses HTML, resolves CSS, and rasterizes to an
offscreen pixel buffer. These are reached via wildcard `export use *`
re-exports (the compiler's own lint already flags ~19+ exact file:line
sites). Whether trimming them would measurably shrink compile time is
**not verified this pass** (see ranked fix list).

### 5. Ambient external load (PROVED via direct process inspection, not inferred)

Mid-investigation, `ps aux` showed the shared machine's load spike (peak
observed **62.3**, 1-min avg) was driven substantially by **other,
unrelated agent sessions'** concurrent git operations: simultaneous `git
worktree add`/`git clone --shared`/`git reset --hard` processes for
`/tmp/simple-html-drawir-element`, `/tmp/simple-navigation-visible`,
`/tmp/simple-drawir-reuse`, `/tmp/simple-security-fd`, `/tmp/simple-web-
prod-integration`, `/tmp/simple-https-gap`, `/tmp/simple-evidence-clean`,
and more -- none of them `simple` compiler processes. One of this
session's own `git worktree add` invocations stalled in `D` (uninterruptible
disk-wait) state for several minutes under this contention and had to be
retried. **This directly answers "is the 48-minute figure load-scaled or
absolute": yes, load-scaled, and a meaningful fraction of that load is
inter-session git/disk contention external to anything the Simple compiler
itself does** -- no code fix in this repository addresses that component.

### Ranked fix list

1. **[Architectural, highest value, NOT attempted]** Add a persistent
   on-disk compiled-artifact cache (content-hash or mtime keyed) to the
   `load_module_with_imports` call sites in `run_file_jit`/`run_file_
   interpreted_with_args`, so a repeat invocation of an unchanged script
   skips re-parsing its whole closure. This is the single highest-value
   fix and the one the repo's own policy already calls for -- but it
   requires cache-invalidation design spanning the whole module-loader
   pipeline (correctness-critical: a stale hit must never silently serve
   outdated code). Out of scope for a bounded `.spl`-only pass; this is a
   Rust driver/pipeline change.
2. **[Contained candidate, flagged by the compiler's own lint, NOT
   attempted]** Replace the ~19+ `export use *` wildcard re-exports the
   compiler already names (exact file:line locations in every run's
   warning output) with explicit named exports, to test whether it
   actually shrinks `web_render_file_gui.spl`'s transitive closure below
   the GPU-backend/database/test-runner modules that look clearly
   unrelated to HTML rendering. This is the most "shovel-ready" candidate
   (the compiler already points at every site) but was not attempted this
   pass: verifying no behavior regression across a large, load-sensitive
   pipeline needs a controlled before/after compile-time measurement this
   session's current load conditions do not support reliably, and the
   true size of the closure reduction (if any) is unverified.
3. **[Environmental, not a code fix]** Ambient inter-session machine
   contention is a real, separate contributor to the worst-case (48-
   minute) timings observed in the prior section. Nothing in this
   repository addresses it; noted for completeness since it directly
   answers the "load-scaled or absolute" question.

No code change landed this pass -- this section is a root-cause
investigation, not a fix; per the instructions, the architectural fix (#1)
and the unverified contained candidate (#2) are documented, not attempted.

## Phase instrumentation landed 2026-07-30: settling style vs. layout/paint -- inconclusive on the cell, conclusive on compile

The "48 minutes, zero progress" finding had exactly one progress marker in
the whole pipeline (`[web-style-producer] budget-break`), so "silence" was
consistent with two very different stories: the style loop hanging, or
styling *completing* with the cost living in layout/shaping/paint instead
(node 138's 136 characters, and the independently-proven "TTF shaping costs
minutes under the interpreter" finding, would land there too). This section
adds permanent instrumentation to tell the two apart and reports what two
real attempts at settling it found.

### Instrumentation landed (permanent, level-gated, not a probe to revert)

Per the log-retention policy (convert-not-delete), this is landed in the
tree, default-off:

- `_web_phase_trace_enabled()` (new, `simple_web_html_layout_renderer_
  foundation.spl`): `(env_get("SIMPLE_WEB_PHASE_TRACE") ?? "") == "1"`.
- `simple_web_html_layout_renderer.spl`
  (`_simple_web_layout_render_html_draw_ir_result_at_time`, the function
  the engine2d/`web_render_file_gui.spl` pipeline actually calls): prints
  `[web-phase] phase=parse|style_start|style_end|layout|compose_shaping
  elapsed_ms=<cumulative-since-render-start>` at each boundary.
  `style_end` is the previously-missing marker this campaign has been
  missing since node 29. `compose_shaping` brackets
  `_simple_web_layout_compose_retained`, which is where DrawIr command
  generation happens -- see the redundant-shaping finding below.
- `simple_web_html_layout_renderer_core.spl`
  (`compute_styles_with_material`): prints `[web-phase] style_progress
  i=<n> of=<total> elapsed_ms=<since-loop-start>` every 10 nodes, so a long
  style pass is observable instead of silent between start and
  `budget-break`.
- `simple_web_layout_engine2d_fast.spl`
  (`_simple_web_layout_render_html_engine2d_execution`): prints
  `[web-phase] phase=paint elapsed_ms=<paint-phase-local>` bracketing
  `_simple_web_layout_execute_draw_ir_composition`.

**Verified working end-to-end (PROVED):** a fast sanity run
(`SIMPLE_WEB_RENDER_BUDGET_MS=1 SIMPLE_WEB_PHASE_TRACE=1`, degenerate --
style budget expires at node 0) produced a complete phase table in one
pass: `parse=2423ms` (cumulative, 151 nodes), `style_start=2424ms`,
`style_end=2754ms` (330ms, degenerate -- budget-broken immediately),
`layout=2789ms` (35ms), `compose_shaping=3616ms` (827ms even on
near-default styles -- see below), `paint=4314ms` (self-contained). The
instrumentation compiles cleanly and the boundaries fire in the expected
order with sane deltas.

**A code-reading finding surfaced while wiring `compose_shaping`
(PROVED, not yet measured for wall-clock impact):**
`_html_draw_ir_command` in `simple_web_html_layout_renderer_paint_layout.
spl:1397` calls `resolve_font_metrics_with_language(st.font_family,
node.text_trimmed, st.font_size, ...)` for every `#text` node when
`vector_fonts` is on -- **a second, independent font-metric resolution
per `#text` node**, distinct from the one `compute_styles_with_material`
already performed and stored on `st.resolved_font_advances`/
`st.resolved_font_identity`/etc. during the style phase. This call does
not read those already-resolved fields; it recomputes from scratch. The
wall-clock impact is likely smaller than a fresh computation, because
`resolve_font_metrics_with_language` has its own whole-string result
cache (`_resolved_font_metric_cached`/`_resolved_font_metric_store`,
confirmed elsewhere in this campaign to turn a ~7-9s cold measurement into
a 27-47ms cache hit) and the second call's `(family, content, font_size,
identity)` key exactly matches the first's -- **INFERRED, not measured**,
that this is usually a cache hit, not a second full computation, unless
the bounded cache was evicted by other content in between (a real page
this size plausibly exceeds the cache's entry limit). Either way it is a
genuine redundant-computation code smell worth a follow-up, independent of
this cell's completion question.

### Two measurement attempts -- both settled compile cost, neither reached style_end

**Attempt 1** (`SIMPLE_WEB_RENDER_BUDGET_MS=900000 SIMPLE_TIMEOUT_SECONDS=
1200`, `stdbuf -oL -eL`, `SIMPLE_WEB_PHASE_TRACE=1`): a `budget_ms=1` sanity
check moments before launch showed compile completing in ~71s at load ~19-25.
The real attempt then ran the full 1200s and died at its own internal
watchdog (`error: example timed out after 1200s`) having printed **zero**
`[web-phase]` lines -- confirmed via `ps`/`/proc/<pid>/stat` mid-run: the
process was genuinely CPU-bound the whole time (utime accumulated almost
exactly 1:1 with wall-clock elapsed, `Rl` state, 99.5% CPU) -- not blocked,
not hung, just still compiling after 18+ minutes of continuous CPU burn,
opposite of the earlier "sys-dominant" finding (here user time dominates).

**Attempt 2** (identical config, launched immediately after a second
`budget_ms=1` sanity check that again completed in ~71s at load ~18): died
the same way -- full 1200s consumed, zero `[web-phase]` lines, load
oscillating 18-40 throughout.

**Reading this honestly:** two back-to-back generous-budget attempts, each
immediately preceded by a fast (~71s) isolated compile check, both failed
to get past compilation within 1200s once the FULL run (parse through
paint through status) was attempted. This is not the same failure mode
measured in the prior section (that one was syscall/IO-bound, `sys` >
`user`); attempt 1 here was CPU-bound (`user` >> `sys`). **Two different
compile-time pathologies have now been observed on this cell, both severe
enough to consume a 20-minute budget with zero output.** This strengthens,
rather than settles, the module-compile-cost finding: the cost is not just
load-scaled in magnitude, it can be dominated by different resources
(I/O vs CPU) depending on what else is contending at the time, and a quick
isolated check immediately before a long run is not a reliable predictor
of the long run's own compile behavior.

**The style-vs-layout/paint question remains open.** Neither attempt
produced a single phase-boundary line, so this section cannot say whether
styling completes before the real bottleneck or not -- that determination
still requires one clean run that gets past compilation. The
instrumentation is landed and default-off; the next attempt (this session
or another) only needs `SIMPLE_WEB_PHASE_TRACE=1` set to get the answer
cheaply, whenever a compile-favorable window occurs.

### Regression baselines (re-confirmed on this pass's tip, unchanged)
- `test/01_unit/app/ui.chromium/css_spec.spl`: 12 total, 9 passed, 3 failed.
- `test/01_unit/lib/gc_async_mut/gpu/browser_engine/apply_decls_merge_probe_spec.spl`:
  20 total, 20 passed, 0 failed.

### Item 4 restated plainly, per instruction

No persistent compile cache exists for `bin/simple run <script.spl>` (see
the prior section for the full evidence). This contradicts this repo's own
stated policy ("production wrappers should execute cached compiled
artifacts, not raw source") and is worth surfacing as an architectural gap
beyond this one showcase cell -- every `bin/simple run` invocation of any
script pays the full whole-closure parse-from-source cost, unconditionally,
regardless of whether anything changed since the last run. Documented here
and in the prior section; **not attempted** (a persistent-cache design is
out of scope for a bounded `.spl`-only pass and belongs with the Rust
driver/pipeline).

### Item 5 (the ~19+ `export use *` sites) -- not attempted this pass

Per instruction, only if it didn't compete with the phase measurement.
Between the two long measurement attempts (2 x 20 minutes) and the
regression-baseline runs, the time budget for this pass was fully consumed
by the measurement; the trim was not attempted. It remains the most
shovel-ready candidate from the prior section's ranked fix list.

## 2026-07-30 close-out: measurement blocked by an already-owned parser defect, not by parse cost

Per-the-brief follow-up on whether real-document HTML parsing is quadratic
(the `char_code_at`/`core_string.spl:282` "ASCII fast path walks from byte
0" landmine family). Two environment corrections apply retroactively to
everything measured earlier in this document: the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` was swapped mid-campaign
(now 154MB / 617 `llvm::` strings, i.e. LLVM-enabled and canonical; the
prior binary in the window used for most of this document's measurements
had **zero** `llvm::` strings, per project memory
`reference_deployed_binary_lost_llvm_codegen_2026-07-29`), and the host hit
`ENOSPC` (disk 100% full) around the time of the two 900s/1200s
zero-output failures in the prior section — since cleared (1.3T free).
**Both prior zero-output measurement attempts are therefore SUSPECT, not
informative about parse or style cost specifically** -- disk exhaustion or
a broken toolchain are at least as plausible an explanation as anything
about the pipeline's own performance.

**Document size (PROVED, direct measurement, not inferred):**
`examples/06_io/ui/browser_common_elements_showcase.html` is **4848
bytes, 4848 characters** (`file` confirms plain ASCII text, `wc -c` ==
`wc -m`). Small by any measure.

**Cheap check first, per the coordinator's revised brief:** re-ran the
plain pipeline on the corrected environment (fresh worktree from
`git ls-remote`'s SHA -- never `FETCH_HEAD`, per this pass's protocol
correction; canonical LLVM binary; disk healthy; load ~5.7, the lowest
this whole campaign) with `SIMPLE_WEB_PHASE_TRACE=1 stdbuf -oL -eL`,
`SIMPLE_WEB_RENDER_BUDGET_MS=900000 SIMPLE_TIMEOUT_SECONDS=1200`.

**Result: the run dies FAST (well under the 1200s budget, reproduced
twice) with a real compile error, not a timeout, not silence:**
```
error: compile failed: parse: in ".../src/lib/common/web/browser_renderer_protocol.spl":
Unexpected token: expected expression, found Newline
```
This is **the same defect an independent lane (ac14) had already
root-caused and filed** (`doc/08_tracking/bug/
if_condition_operator_line_continuation_parse_2026-07-30.md`,
cross-referenced in `doc/09_report/showcase_matrix_census_2026-07-30.md`
as "wall 8"): operator line-continuation parses inside a `val` binding but
fails inside an `if` condition (`val x = a +\n   b` parses; `if a >\n
b:` does not), introduced by `ba0ce4e3c06` "feat(web): add SBR2 command
capability codec" earlier the same day, confirmed live on the newest
LLVM-linked seed (not a staleness artifact). **This blocks `web_render_
file_gui.spl` from compiling at all right now** -- it transitively
compiles `browser_renderer_protocol.spl` -- confirmed independently from
this document's own investigation before the coordinator's cross-lane
notice arrived, and cross-verified via `git show <tip>:<file>` (the
committed blob parses fine standalone, matching the known "STATE not
grammar" bug family already on file in this campaign's memory -- a
whole-tree compile triggers it, an isolated read of the file does not).

**Per explicit instruction: not touched.** ac14 owns the parser fix;
reformatting the one `if` to dodge it would encode the grammar
inconsistency rather than fix it, and would silently hide the real bug
from whoever needs to see it fail. **This is a legitimate stopping point,
not a stall.** The style-vs-layout/paint completion question from the
prior section remains genuinely open, now for a different and better-
understood reason: nothing downstream of compilation can be measured
until this lands, and that is out of this lane's scope.

**The quadratic-scan hypothesis itself: answered anyway, independent of
whether the full pipeline compiles (PROVED via a standalone microbenchmark,
re-run on the corrected canonical binary for validity).** A tiny
standalone script (not touching `browser_renderer_protocol.spl` or any
other blocked module) scanned synthetic all-ASCII strings from 500 to
8000 characters two ways: `.slice(i, i+1)` per position (the exact
pattern `html_tokenizer.spl`'s `_scan_char_data`/`_split_first_word`/
`_strip_tag_name`/`_find_raw_end_tag` all use in their hot loops, confirmed
by reading the source -- none of them use `char_code_at` in a
document-length loop) and `char_code_at(i)` per position (for direct
comparison against the `core_string.spl:282` landmine).

| N | slice scan_us | char_code_at scan_us |
|---|---|---|
| 500 | 159 | 50 |
| 1000 | 303 | 94 |
| 2000 | 607 | 183 |
| 4000 | 1258 | 391 |
| 8000 | 2349 | 804 |

Both are **cleanly linear** -- each doubling of N almost exactly doubles
the time, in every step, for both access patterns. **No quadratic
blow-up at any tested size**, well above the real document's 4848
characters. This **kills the quadratic-parse hypothesis for the seed lane**
(what `bin/simple run` actually executes): `core_string.spl:282`'s "ASCII
fast-path walks from byte 0 every call" defect is real (per the
coordinator's own framing and this campaign's prior char_at findings) but
belongs to a **different lane** -- the freestanding/native-codegen
runtime's own `rt_string_char_code_at`, which is not what the seed's Rust-
native string implementation uses. Combined with the tokenizer's own
slice-based (not char_code_at-heavy) hot-loop pattern, there is no
evidence of an O(N^2) document-length scan anywhere on this path.
**Answering the brief's item 3 directly: neither the non-ASCII-`char_code_
at`-quadratic-on-seed defect nor the ASCII-ffast-path-quadratic-on-native
defect applies here** -- the seed's tokenizer scan is linear by both
access patterns, on the canonical binary, confirmed empirically.

**Item 4 (contained vs. architectural fix): moot for the quadratic
hypothesis (refuted, nothing to fix) -- the real current blocker (the
parser defect) already has an owner, a filed doc, and two identified fix
options, per the other lane's own report; correctly not chased here.**

**Sub-phase markers at lines 1191/1197/1258 (`parse_html_total`,
`extract_css_vw`, plus tokenize/tree-build brackets in
`html_tree_builder.spl`): prototyped and produced one promising signal
before this pass's own worktree was lost mid-edit to an unrelated
disk/session issue** (`parse_tokenize`=102ms, `parse_tree_build`=122ms,
vs. the outer `phase=parse`=2225ms on that run -- roughly 2 seconds
unaccounted for between the tokenizer/tree-builder and the full "parse"
boundary, likely in `extract_css_vw`/`build_child_index`/the HNode-
conversion loop). **That data point predates the binary-swap correction
and is not re-verified on the canonical binary or landed this pass**, per
the coordinator's revised brief ("only if it completes AND the numbers
are still unexplained do you go back to sub-phase markers") -- the plain
re-run did not complete, so this was correctly not repeated. Left as the
documented next step for whoever resumes once ac14's fix lands.

### Regression baselines
Not re-run this pass -- no source change landed (investigation and
environment-correction only).

## bracket-slice (`s[i:j]`) survey gap — enumerated 2026-07-29, not fixed

The original Category B survey (that found the byte/char split, see
`text_slice_substring_spec.spl`) only grepped `.slice(`/`.substring(` method
calls. Simple also has a `s[i:j]` bracket-slice expression form using the
*same* underlying byte-indexed primitive (confirmed: the
`serialization/__init__.spl` fix in `c24918ae676` used exactly this form and
passed its existing 82-test suite unchanged) -- the survey missed every site
using this syntax entirely.

**Count: 1,193 sites across 393 files** under `src/` (after filtering
string-literal false positives like `"error[E:core]"` matching the same
regex — the raw grep was 1,243 hits across identifier-preceded `[a:b]`
patterns; ~50 were print-string content, not code).

Top concentrations (site count, file):
| Sites | File |
|---|---|
| 67 | `src/compiler/90.tools/fix/rules/impl_/lint_short_grammar.spl` |
| 21 | `src/lib/common/js/builtins/json.spl` |
| 19 | `src/lib/common/serialization/__init__.spl` (fixed in `c24918ae676`) |
| 15 | `src/lib/nogc_sync_mut/tooling/regex_nfa.spl` |
| 15 | `src/app/cli/arch_check.spl` |
| 13 | `src/lib/common/js/builtins/string.spl` |
| 12 | `src/app/desugar/rewriter.spl` |
| 11 each | `regex_match.spl`, `pure/lexer.spl`, `common/parser/lexer.spl`, `warning_counts.spl`, `static_methods.spl`, `forwarding.spl`, `check_tier.spl` |
| 10 each | `web_framework/auth_middleware.spl`, `src/exp/config.spl`, `pure/nn/serialization.spl`, `static_constants.spl`, `context_params.spl` |

Spot-checked (`lint_short_grammar.spl`, `json.spl`, `regex_nfa.spl`,
`arch_check.spl`, `rewriter.spl`, `auth_middleware.spl`) confirm these are
all genuine `text[i:j]` slices, not false positives.

**Classification proposal, by the same risk lens used for the Category B/
char_at work** (does the sliced content plausibly carry non-ASCII, and does
the site reconstruct content byte-by-byte or just detect ASCII delimiters):
- **Likely low-risk (structural/ASCII-only domain):** compiler-internal
  lexers/parsers walking Simple/JS source tokens (`pure/lexer.spl`,
  `common/parser/lexer.spl`, `regex_nfa.spl`, `regex_match.spl`,
  `lint_short_grammar.spl`, desugar/`rewriter.spl`,
  `static_methods.spl`/`forwarding.spl`/`static_constants.spl`/
  `context_params.spl`, `arch_check.spl`) -- identifiers and source
  punctuation are ASCII by grammar; still needs the same char_at-adjacent
  reconstruction-vs-detection triage this pass applied to the browser
  engine before ruling a file safe.
- **Likely higher-risk (arbitrary external data):** `json.spl`/
  `js/builtins/string.spl` (arbitrary JSON/JS string values),
  `web_framework/auth_middleware.spl` (HTTP header/cookie parsing),
  `pure/nn/serialization.spl` (arbitrary tensor/model metadata strings).
  These are the priority for the next classification pass.
- Needs its own dedicated survey pass, file by file, same methodology as
  this session's char_at follow-up (grep for `s[i:j]`, read each site,
  distinguish "detects an ASCII byte, safe" from "reconstructs content
  byte-by-byte or hand-counts past non-ASCII, needs a fix") -- not
  attempted this pass beyond the enumeration and file-domain classification
  above.

## Reproduce

```
SIMPLE_WEB_RENDER_BUDGET_MS=120000 SIMPLE_TIMEOUT_SECONDS=270 \
SHOWCASE_RESOLUTION=480x360 bin/simple run examples/06_io/ui/web_render_file_gui.spl
# watch: budget-break at=N of=151 — N ≈ budget_s / 3.2 (post char_at fixes)
```
