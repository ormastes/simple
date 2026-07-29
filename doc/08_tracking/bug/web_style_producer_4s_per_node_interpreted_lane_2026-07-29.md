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
5. Investigate the node 5 / node 8 outliers separately -- they are not
   explained by anything in this section and could be a second, unrelated
   defect (GC pressure or a `wm_fallback` code path cost).

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
