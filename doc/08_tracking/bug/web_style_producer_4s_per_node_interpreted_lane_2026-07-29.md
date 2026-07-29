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

### Fix proposal (not implemented — needs its own scoped change, not a <50-line drive-by)

1. Stop doing 176-field struct copy-in/copy-out per `apply_decls` call:
   either mutate `Style` in place (pass by reference / builder pattern) or
   batch all candidate rules' declarations into one merged decl table and
   call `apply_decls`-equivalent logic once per node instead of once per
   candidate rule.
2. Replace the ~283 individual `decl_tbl_get(tbl, "prop-name")` linear-scan
   probes with a single pass over `tbl`'s actual entries (typically 5-20)
   dispatching on the property name once, instead of the property list
   scanning the table up to 283 times.
3. Profile whether (1) or (2) dominates before committing to a large
   refactor -- add the same four-point timing probe used here, but INSIDE
   `apply_decls` itself (copy-in boundary, lookup-loop boundary,
   construct-out boundary), to split the ~100-150ms further.
4. Investigate the node 5 / node 8 outliers separately -- they are not
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
