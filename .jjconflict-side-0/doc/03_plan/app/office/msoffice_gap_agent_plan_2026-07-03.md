# MS-Office Gap — Remaining Work, Agent-Based Execution Plan

**Date:** 2026-07-03 (reviewed & updated post-round-13, same date)

## Execution status at review

| Card | Status | Evidence |
|------|--------|----------|
| 1 Alias pack | **DONE** (round 11, pushed c4855c5) | dotted-name lexing + `_canonical_name`; RANK.AVG/CEILING.MATH/PRECISE real semantics; AVERAGEA-family correctly refused |
| 2 Distribution core | **DONE** (round 13, pushed 355f4e2) | `_betainc`/`_gammainc_p` + inverses; ~30 fns; 2 plan ground-truth typos caught & corrected; tests → CARD 14 |
| 3 Securities | **OPEN — next priority** | day-count engine not started |
| 4 Engineering | **DONE** (round 12, pushed b6245d3) | ERF/ERFC, 18 IM*, BESSELJ/I, CONVERT; BESSELY/K → CARD 14 |
| 5 Text/misc | **OPEN** | serialize on formula.spl |
| 6 Deploy swap | **REOPENED** — lane died (credit outage); probe 2026-07-03 12:5x: production binary still errors `unknown extern` on raw-mode; fix remains seed-only | re-run CARD 6 protocol from step 3 |
| 7 ODS styles | **DONE** (round 10) | sheet_to_fods_formatted, xmllint-validated |
| 8 Matrix batch | **DONE** (pushed 87661f0) | fully-inline flat arrays (interp array-param bugs) |
| 9 Audit consumption | **DONE 2026-07-04** | exact census: **330 callable** (296 distinct impls + 34 pure aliases), 10/10 sanity checks; missing vs Excel-365 concretely **enumerated 152** (nominal ~175 incl. catalog fuzz); top buckets: securities 30 (CARD 3 in flight), info/dynamic-array 19, stat A-variants 18; census file in session scratchpad `function_census_2026-07-04.md` |
| 10 Desktop render | **HEADLESS PASSED** (round 12, pushed b6245d3) | all 4 formats → PDF in real LibreOffice via docker; check script committed; residual = GUI fidelity (CARD 15) |
| 11 CLI/macro catch-up | **DONE** (round 11) | --styles flag + macro format API; md5-identical no-flag path |
| 12 Cube/web exclusion | **DECIDED** | out of offline scope, recorded |
| — Find/replace (uncarded) | **DONE** (round 13, pushed 355f4e2) | sheet_find/sheet_replace + find-sheet CLI; shipped during credit-death recovery |

Suite state at review: **330 callable Calc functions** (296 distinct
implementations + 34 dotted aliases; census 2026-07-04, 10/10 sanity checks),
**55 office spec files**, all green per-file; all shipped rounds pushed and
content-verified on origin. Missing vs Excel 365: **152 enumerated** —
securities 30 (CARD 3 in flight), info/dynamic-array 19, stat A-variants 18,
tests/regression 16, text 13, lookup/ref 12, LAMBDA-family 11, date/time 9,
math 9, cube 7 + web 3 (excluded, CARD 12), BESSELY/K 2.
**Audit (Explore lane, this date):** **231 implemented** vs Excel 365's ~505
→ **~274 missing**, of which: 21 pure dotted-name aliases of functions we
HAVE (STDEV→STDEV.S, RANK→RANK.EQ, GAMMALN→GAMMALN.PRECISE, …), ~73 stats
(34 blocked only on incomplete beta/gamma + inverse root-finder), ~34
financial securities (blocked only on a day-count-basis engine + solver),
~33 engineering (18 IM* mechanical), ~23 text/misc, ~82 general mechanical
(OFFSET/INDIRECT/date-time/math fill-ins), 7 cube + 3 web (out of scope —
CARD 12). Recommended order: aliasing pack (~40, near-zero math) →
IM*+ERF (~26) → incomplete beta/gamma core (~34). Full detail:
session scratchpad `function_gap_audit.md`.
**Status snapshot:** pure-Simple office suite at **231 verified Calc functions**,
46 spec files, all green. Shipped this campaign: dynamic arrays w/ spill,
SUMIFS family, XLOOKUP/XMATCH + array manipulation, financial solvers
(RATE/IRR Newton), engineering/date/text/logic tails, DEFLATE zip writer,
xlsx styles.xml round-trip, conditional formatting (engine + render), per-cell
number formats, charts (bar/line/pie/scatter/area + axes/legends), mail merge,
TOC, table editing, find/replace/stats, Impress notes+transitions, raw-mode
termios fix (seed-verified), CLI surfacing (toc/merge/sort-sheet/find/stats/chart),
Simple-as-macro-language (`office_api.spl`).
**Honest position:** NOT equal to MS Office. Remaining distance is enumerated
below as self-contained agent task cards.

**Execution model (proven over 10 rounds):** parallel model lanes
(opus = algorithmic batches, sonnet = infra/containers/root-cause,
haiku = mechanical/new-file features) with **disjoint file ownership**;
the coordinating session (fable) independently re-runs every spec, repairs
sub-green deliveries at root cause, then verifies durability by
**symbol-grep against HEAD** (parallel jj sessions sweep the working copy
continuously — pathspec commits often no-op; the HEAD grep IS the check).

---

## Cross-cutting protocol (include in EVERY agent brief)

### Simple interpreter quirk ledger (violations cost hours)
- NO inheritance; generics `<>`; `val`/`var`; docstrings on public functions.
- String interpolation is `"{expr}"` — literal braces in string literals ARE
  interpolation. Build XML/CSS/`{{placeholders}}` by concatenation.
- Chained method calls FAIL at runtime (`x.f().g()`) — intermediate `val`s.
- Aggregates pass by copy — mutating functions RETURN the object; callers
  reassign (`sheet = recalculate_formula_cells(sheet)`).
- match-binding an `f64?` does NOT unwrap it — use the `.to_f64()` idiom
  (see `_criteria_matches` in formula.spl).
- **Dict-in-struct under copy-return corrupts values 8×** (bug doc
  `interp_dict_in_struct_copy_corruption_2026-07-03.md`) — use parallel
  arrays (`keys: [text]`, `specs: [T]`); `class` fields are safe (reference
  semantics).
- Struct default-field omission is broken in interpreter mode — always pass
  every field.
- Reserved/broken identifiers: `grid`, `unit` (plus keyword list in
  `.claude/rules/language.md`).
- Formula empty-string results display as raw `={expr}` — make emptiness
  observable via `="["&F(x)&"]"` in specs.
- `examples/`-dir scripts zero f64 payloads + no-op writes (bug doc) —
  probes go in the session scratchpad.
- Test runner: directory BATCH runs hang (daemon issue) — run spec files
  individually. Confirm assertions execute once per new spec via a
  deliberate-fail probe, then remove it.
- Array PARAMETERS are broken in the interpreter: `[[text]]` params misparse;
  variable-indexing any array param reads 0 (bug doc
  interp_array_param_indexing_2026-07-03.md) — matrix-style code must inline
  with LOCAL flat arrays; only scalars cross call boundaries.
- Dotted function names now lex correctly (fixed rounds 11+13 inside
  formula.spl's tokenize_formula: name continues across `.` followed by
  alpha OR digit) — new dotted functions need no lexer work.
- `File.write` (std.fs) fails under the interpreter — use rt_file_write_text
  (see fods_styles_spec.spl precedent).

### Failure-mode protocol (added post-round-13)
- **Agent death mid-edit** (credit outage, API error) can leave the tree
  BROKEN — half-wired imports/dispatches. After ANY lane failure: grep the
  files it owned for dangling references and load the entry module
  (`bin/simple run src/app/office/mod.spl stats <f>`-style smoke) before
  committing anything that includes those files.
- **Do not trust agent-reported function totals** — agents count deltas off
  whatever baseline they read (often the stale audit). The only honest count
  is a fresh CARD 9 dispatch-extraction audit.
- **mod.spl is clobber-prone** (parallel reconciles dropped committed-looking
  edits twice in round 13): after committing it, immediately
  `git show HEAD:src/app/office/mod.spl | grep <new-dispatch>` and re-commit
  the delta if dropped.

### VCS discipline
- NEVER bare `git commit` — always pathspec form
  `git commit -m msg -- <paths>` (a bare commit once swept a parallel
  session's staged 13k-file tree).
- Back up every touched file to the scratchpad BEFORE any VCS op.
- After commit: `git show HEAD:<file> | grep <new-symbol>` — nonzero or the
  work is NOT durable.
- Fresh `.git/index.lock` with queued sessions → join the queue with a
  bounded retry loop; delete only if >5 min old with no live holder.
- Agents: no jj/git commands; leave changes uncommitted for the coordinator.

### Per-batch verification loop (formula work)
1. Probe every function against hand-computed / Excel-documented values in
   the scratchpad FIRST. 2. Spec file modeled on the nearest sibling spec.
3. Per-file spec run + per-file neighbor regressions. 4. Coordinator re-runs,
   commits pathspec, HEAD-greps. 5. Memory file update.

---

## Task cards — remaining work

### CARD 1 (opus lane) — Compatibility-alias batch  [DONE round 11, pushed c4855c5]
**Objective:** Excel's modern dotted names for functions we already have:
RANK.EQ, RANK.AVG, STDEV.S/STDEV.P, VAR.S/VAR.P, MODE.SNGL, QUARTILE.INC,
PERCENTILE.INC, PERCENTRANK.INC, NORM.DIST/NORM.S.DIST/NORM.INV/NORM.S.INV,
BINOM.DIST, POISSON.DIST, EXPON.DIST, WEIBULL.DIST, LOGNORM.DIST, T.INV?,
CONFIDENCE.NORM, COVARIANCE.P, FORECAST.LINEAR, CEILING.MATH/FLOOR.MATH
(Excel-2013 semantics: negative handling differs from classic — implement,
don't alias blindly), ISO.CEILING, plus TEXT-family aliases. Exact list:
take from `scratchpad/function_gap_audit.md` (Explore audit, round 10).
**Design:** the formula tokenizer must accept `.` inside function names —
check `_tokenize`/name-lexing FIRST; if dots already lex as part of names,
aliasing = one dispatch line per name delegating to the existing case
(normalize name → strip/translate dots at dispatch entry:
`val fname = raw_name.replace(".", "_DOT_")`-style mapping table or a
`_canonical_name(name)` translation function — pick the smallest diff).
If the lexer splits on `.`, fix the lexer for function-name context only and
spec that separately. RANK.AVG needs real averaging of tied ranks (small new
logic). CEILING.MATH/FLOOR.MATH: real new semantics — ground truths
CEILING.MATH(-5.5)=-5, FLOOR.MATH(-5.5)=-6, CEILING.MATH(-5.5,2,1)=-6.
**Files:** formula.spl + `formula_compat_alias_spec.spl`.
**Spec musts:** every alias returns the same value as its base on one shared
input; the genuinely-new semantics (RANK.AVG ties, CEILING.MATH negatives)
hand-computed; dot-name tokenization proven by a formula mixing dotted and
plain calls.

### CARD 2 (opus lane) — Continuous-distribution machinery  [DONE round 13, pushed 355f4e2; tests → CARD 14]
**Objective:** BETA.DIST/BETA.INV, GAMMA.DIST/GAMMA.INV, CHISQ.DIST/
CHISQ.DIST.RT/CHISQ.INV/CHISQ.TEST, T.DIST/T.DIST.2T/T.DIST.RT/T.INV/T.TEST,
F.DIST/F.DIST.RT/F.INV/F.TEST, GAMMA, GAUSS, PHI.
**Design:** one new primitive pays for the whole card: the **regularized
incomplete beta function** `I_x(a,b)` via Lentz continued fractions
(Numerical Recipes §6.4; symmetry `I_x(a,b)=1-I_{1-x}(b,a)` when
x>(a+1)/(a+b+2)), plus **regularized incomplete gamma** `P(a,x)` (series for
x<a+1, continued fraction otherwise, NR §6.2). Existing primitives:
`_gammaln` (Lanczos), `_exp_f64`, `_ln_f64`, `_powf`, `_norm_cdf`,
`_norm_inv_std` (Acklam). Then: T CDF = incomplete-beta with
a=df/2,b=1/2,x=df/(df+t²); F CDF likewise; chi-square = P(df/2, x/2).
Inverses: bisection on the CDF (50 iters, [lo,hi] expanded until bracketed) —
do NOT chase Newton stability. Fail closed #ERR on domain violations
(a,b≤0; df<1; x outside [0,1] for inverses).
**Ground truths:** BETA.DIST(0.5,2,3,TRUE)=0.6875; GAMMA.DIST(10.00001131,9,2,TRUE)=0.068094;
CHISQ.DIST(0.5,1,TRUE)=0.520500; T.DIST(1.96,60,TRUE)≈0.972716;
F.DIST(15.2069,6,4,TRUE)≈0.99; GAMMA(2.5)=1.329340; GAUSS(2)=0.477250;
PHI(0.75)=0.301137. Verify each against a second source in the probe.
**Files:** formula.spl + `formula_dist2_spec.spl`.

### CARD 3 (opus lane) — Financial securities batch  [OPEN — NEXT PRIORITY]
**Objective:** ACCRINT/ACCRINTM, COUPDAYBS/COUPDAYS/COUPDAYSNC/COUPNCD/
COUPNUM/COUPPCD, PRICE/PRICEDISC/PRICEMAT, YIELD/YIELDDISC/YIELDMAT,
DISC, INTRATE, RECEIVED, DURATION/MDURATION, TBILLEQ/TBILLPRICE/TBILLYIELD,
DOLLARDE/DOLLARFR, AMORDEGRC/AMORLINC (French — optional, mark if skipped).
**Design:** the machinery is **day-count basis** (arg `basis` 0..4):
implement `_daycount(start_serial, end_serial, basis)` and
`_coup_dates(settle, maturity, freq)` (roll back from maturity by 12/freq
months using the existing `_serial_from_civil`/`_civil_from_serial` +
EOMONTH-style month clamp). US 30/360 (basis 0) day rule: d1=min(d1,30);
if d1==30 then d2=min(d2,30). YIELD: bisection on PRICE (no closed form).
DURATION = Macaulay via the standard weighted-PV sum; MDURATION =
DURATION/(1+yld/freq).
**Ground truths (Excel docs):** PRICE(DATE(2008,2,15),DATE(2017,11,15),
0.0575,0.065,100,2,0)=94.634362; YIELD same instrument at price 95.04287
=0.065; DURATION(DATE(2008,1,1),DATE(2016,1,1),0.08,0.09,2,1)=5.993775;
DISC(DATE(2007,1,25),DATE(2007,6,15),97.975,100,1)=0.052420;
TBILLYIELD(DATE(2008,3,31),DATE(2008,6,1),98.45)=0.091417;
DOLLARDE(1.02,16)=1.125; DOLLARFR(1.125,16)=1.02.
**Files:** formula.spl + `formula_securities_spec.spl`. Congruence of
settle<maturity, basis 0..4, freq∈{1,2,4} → else #ERR.

### CARD 4 (opus lane) — Engineering remainder  [DONE round 12, pushed b6245d3; BESSELY/K → CARD 14]
**Objective:** ERF/ERFC (we have `_norm_cdf`'s A-S erf — expose + add
complementary w/ 2-arg ERF(lo,hi)), BESSELJ/BESSELY/BESSELI/BESSELK
(series for small x, asymptotic/recurrence for large — NR §6.5-6.7; integer
order only is acceptable Excel-wise for a first pass, document it),
CONVERT(n, from_unit, to_unit) (unit table: mass g/lbm/kg…, distance
m/mi/in/ft/yd, time, pressure, force, energy, power, temperature —
affine!, liquid; implement as a parallel-array table of (name, category,
to_SI_factor) + special-case temperature offsets), DELTA/GESTEP (exist —
check), IMSUM/IMSUB/IMPRODUCT/IMDIV/IMPOWER/IMSQRT (extend the existing
`_parse_complex`/`_format_complex` text path — check which IM* exist first).
**Ground truths:** ERF(1)=0.842701; ERFC(1)=0.157299; BESSELJ(1.9,2)=0.329926;
BESSELI(1.5,1)=0.981666; CONVERT(1,"lbm","kg")=0.453592;
CONVERT(68,"F","C")=20; CONVERT(2.5,"ft","sec")=#ERR (category mismatch);
IMSUM("3+4i","5-3i")="8+i"; IMPRODUCT("3+4i","5-3i")="27+11i";
IMSQRT("1+i")≈"1.09868411346781+0.455089860562227i" (prefix-assert).
**Files:** formula.spl + `formula_eng2_spec.spl`.

### CARD 5 (haiku lane) — Text/misc remainder  [OPEN — serialize on formula.spl after CARD 3]
**Objective:** TEXTBEFORE/TEXTAFTER/TEXTSPLIT (TEXTSPLIT is ARRAY-returning —
row delim + col delim → spill via evaluate_formula_array), NUMBERSTRING?,
LEN variants done; ARRAYTOTEXT/VALUETOTEXT, LET (defer — needs evaluator
scoping, mark blocked), LAMBDA (defer — same), FORMULATEXT (needs origin-cell
formula access — read recalc driver, it caches formula text on the origin
cell: expose it), ISFORMULA, SHEET/SHEETS (single-sheet model: SHEET()=1,
SHEETS()=1 — honest stubs are CORRECT here, they match our model),
ADDRESS(row,col,[abs],[a1]) / ROW([ref]) / COLUMN([ref]) / ROWS(range) /
COLUMNS(range) — ROW/COLUMN with no arg need the origin cell: the recalc
driver knows the origin A1 — thread it as an optional context arg to the
evaluator IF cheap; else implement only the with-arg forms and #ERR bare
forms with a docstring note (do not fake it).
**Ground truths:** TEXTBEFORE("red-blue-green","-")="red";
TEXTAFTER("red-blue-green","-",2)="green" (check Excel: instance 2 →
after 2nd delim); TEXTSPLIT("a,b;c,d",",",";") spills [[a,b],[c,d]];
ADDRESS(2,3)="$C$2"; ROWS(A1:B3)=3; COLUMNS(A1:B3)=2.
**Files:** formula.spl + `formula_text2_spec.spl`. NOTE: this card touches
formula.spl — serialize AFTER whichever opus card is running, or give it the
card only when formula.spl is free.

### CARD 6 (sonnet lane) — Deploy swap completion  [REOPENED — lane died in credit outage]
**Status 2026-07-03:** the round-9 lane's background build died with the
Fable credit outage. A parallel session deployed an UNRELATED binary at 12:40;
probe confirms production `bin/simple` still errors
`unknown extern function: rt_terminal_enable_raw_mode` on `edit-sheet --tui`.
The raw-mode fix exists ONLY in the bootstrap seed
(src/compiler_rust/target/bootstrap/simple). Re-run from step 3 below; the
acceptance probe above IS the reopen/close test.
**Objective:** production `bin/simple` carries the raw-mode termios +
interpreter-dispatch fixes.
**Design:** canonical path `bin/simple build bootstrap` (or
`bootstrap-from-scratch.sh --pure-simple --deploy`); background build with
log polling; `.bak-rawmode` before swap; atomic `.new`+`mv` to BOTH release
paths (`bin/release/x86_64-unknown-linux-gnu/` build target AND
`bin/release/linux-x86_64/` mcp launch path per code-style.md).
**Acceptance:** (a) interactive_spec passes on new binary; (b)
`printf 'q' | bin/simple run src/app/office/mod.spl edit-sheet --tui <csv>`
exits WITHOUT "unknown extern function"; (c) 3 formula specs green on the
new binary. ANY failure → rollback + re-verify + honest report.
**If the build fails twice on parallel-session churn:** stop, log tail,
leave binaries untouched, report — do not force.

### CARD 7 (haiku lane) — ODS styles  [DONE round 10]
As briefed: `sheet_to_fods_formatted` in odf_export.spl mirroring xlsx
styles (automatic-styles, number/percentage/date styles, bold/bg/fg),
`fods_styles_spec.spl`, old writer byte-identical, ceiling = structural
(no LibreOffice locally).

### CARD 8 (opus lane) — Matrix batch  [DONE, pushed 87661f0]
As briefed: MMULT/MINVERSE(Gauss-Jordan)/MDETERM(LU)/MUNIT spill +
SUMX2MY2/SUMX2PY2/SUMXMY2 + FACTDOUBLE/MULTINOMIAL/SERIESSUM +
ROMAN/ARABIC. `formula_matrix_spec.spl`.

### CARD 9 (any lane) — Function-gap audit  [PARTIAL — exact recount OPEN]
**Re-run required:** extract the exact dispatchable-name set from formula.spl
(all dispatch paths + `_canonical_name` table + array-function names), dedupe,
publish the number. Agents have been reporting totals off stale baselines;
loose grep upper bound is 349, honest working claim ~330. Original brief:
When `scratchpad/function_gap_audit.md` lands: copy it into
`doc/09_report/office_function_gap_audit_2026-07-03.md`, re-derive CARD 1's
exact alias list and CARD 2-5 exact membership from it, update THIS plan's
counts, and re-order remaining cards by coverage-per-effort.

### CARD 10 (sonnet lane) — Desktop render verification  [HEADLESS PASSED round 12; residual → CARD 15]
**Objective:** prove .docx/.xlsx/.pptx/.fods open correctly in real
Office/LibreOffice. **Blocked:** neither installed on this host.
**Plan:** (a) container route — check `scripts/local-container-test.shs`
infra for an image with `libreoffice --headless --convert-to pdf` available;
acceptance = conversion exit 0 + nonzero-page PDF for one file of each
format; (b) if no container capability, produce a one-command user-side
check script (`.shs`) + doc, and record the ceiling in
`doc/08_tracking/test/` as an environment-blocked verification item.
NEVER claim desktop-verified until (a) or user confirmation.

### CARD 11 (haiku lane) — CLI + macro API catch-up  [DONE round 11]
After CARDs 1-5 land: extend `office_api.spl` wrappers + mod.spl help for
any new user-facing surface (formatted xlsx/fods export flags on `convert`:
`--styles <fmt-spec-file>`? design the smallest flag that exposes
`sheet_to_xlsx_bytes_formatted`), one E2E grep proof per addition,
regression on existing dispatch.

### CARD 12 — Cube/OLAP + web functions  [DECLINED, record honestly]
CUBEVALUE etc. require an OLAP data source; WEBSERVICE/FILTERXML require
network access inside formulas — both violate the suite's offline pure-Simple
model. Decision: implement as fail-closed #N/A stubs ONLY if the audit shows
compatibility value; otherwise document exclusion in the audit report.
These are excluded from the parity count with rationale, not silently.

### CARD 13 (opus lane) — Pivot tables  [NEW, OPEN]
**Objective:** the marquee Excel analysis feature we lack entirely: group a
data range by one or two key columns, aggregate a value column
(SUM/COUNT/AVERAGE/MIN/MAX), emit a result grid.
**Design:** NEW FILE `src/app/office/sheets/pivot.spl` (disjoint — can run
parallel to any formula.spl card). Model: `pivot_build(sheet, range_a1,
row_key_col, col_key_col_or_neg1, value_col, agg) -> [[text]]` returning a
2D grid (row keys sorted first-seen or lexicographic — pick one, document it;
col_key -1 = one-dimensional pivot with a single value column; grand-total
row and column). Reuse the range-iteration idiom from data_ops.spl
(parse_range + min/max normalization + get_cell/cell_display_text); numeric
extraction via the CellValue.NumberVal match idiom. Then:
`pivot_to_sheet(grid_result, name) -> Sheet` for CSV/render output, a
`pivot` CLI subcommand (`pivot <in.csv> <range> <row_col> <val_col> <agg>
[--col <col>]` — remember mod.spl's clobber protocol), and
`macro_pivot(...)` in office_api.spl.
**Ground truth:** hand-compute a 6-row dataset with 2 regions × 2 products:
SUM/COUNT/AVERAGE per group, grand totals. Fail-closed on non-numeric value
cells (skip, like Excel), empty range, bad agg name.
**Spec:** `test/01_unit/app/office/sheets/pivot_spec.spl` — the hand-computed
table asserted cell-exact, 1D and 2D forms, each agg, error cases.

### CARD 14 (opus lane) — Deferred-math remainder  [NEW, OPEN]
Collected honest skips, each needing dedicated ground truth work:
- CHISQ.TEST / T.TEST / F.TEST (two-range statistical tests; T.TEST types
  1/2/3 + tails; verify against published worked examples, not self-derived)
- BESSELY / BESSELK (need Y/K-specific series with log + Euler–Mascheroni
  terms; verify to 6 digits against tables before shipping)
- LET / LAMBDA (need evaluator variable-scoping machinery — largest item)
- Bare ROW()/COLUMN() (need origin-cell context threaded into the evaluator;
  CARD 5 ships the with-arg forms first)
Rule stands: no unverified math ships; a skipped function stays on this card
with its blocker named.

### CARD 15 — GUI-interactive fidelity  [NEW, BLOCKED by environment]
CARD 10 proved headless import+PDF-render in real LibreOffice for all 4
container formats. Remaining tier: interactive fidelity (formatting seen in
the GUI, formula recalc inside LibreOffice/Excel, edit round-trips).
Requires a display server + real desktop app or user-side verification.
Deliverable when unblocked: a checklist doc + per-format screenshots or
user confirmation. Until then this is the honestly-stated verification
ceiling, recorded in spec docstrings.

### CARD 16 — Office onto the Simple-UI-GUI + web-renderer stack  [NEW, user directive 2026-07-04]
**Directive:** office should be based on the IDE/UI-GUI/web-renderer stack;
if not, refactor — validating similar examples first.
**Recon findings (Explore, 2026-07-04):**
- Office is NOT on the stack today: every `*App.build_ui()` builds a
  `common.ui` UITree that is then DISCARDED (mod.spl prints root_id only);
  the real output is render_adapter.spl's direct document→HTML path, which
  bypasses widgets AND the browser engine.
- `examples/10_tooling/simple_ide` is a DAP/LSP backend + test runner
  (submodule, .smf), NOT a GUI layer — the literal "base on simple ide"
  premise doesn't map; the correct base is the chain that DOES exist:
  `common.ui` (UITree/builder/draw_ir/html_window) → `app.ui` backends
  (`src/app/ui.browser/app.spl` renders in-process via browser engine) →
  `browser_engine` (`WebRenderBackend.render_html_to_pixels(html)→[u32]`).
- **Example validation PASSED** (user gate, 2026-07-04):
  browser_backend_pixel_paths_spec + html_window_spec green in this
  environment. The full native-GUI system spec
  (gui_entry_engine2d_wm_simple_web_spec) requires an LLVM-flavored driver
  build — environment ceiling; use unit+pixel-level proofs here.
**Refactor steps (smallest-first):**
1. DONE — validate examples (above).
2. **Pilot**: route `CounterApp.build_ui()` through the ui.browser backend
   (`render_frame(tree, …)` — study src/app/ui.browser/app.spl and follow
   its structure exactly) to a real frame; spec asserts frame/pixel output
   nonzero and a known widget's pixels differ from background. New CLI:
   `office counter --gui`.
3. Generalize: word/sheets/slides/mail/planner/launcher `--gui` through the
   same path; audit each app's build_ui() actually reflects document state
   (some are stubs today) and fix per app.
4. Demote render_adapter.spl to file-export only (docstring note); the GUI
   path becomes canonical for screen output.
5. Stretch: interactivity via the browser_host_event_roundtrip pattern
   (test/01_unit/app/ui/) — click/keyboard into office UITrees (sheet cell
   click → edit → recalc frame).
**Ownership when laned:** pilot agent owns the counter app file + one new
gui glue file + spec; formula.spl/render_adapter.spl untouched in the pilot.

### Post-round-15 status addendum (2026-07-04)
CARD 3 DONE (24 securities fns, pushed a314a99, 3 more ground-truth
corrections); CARD 13 DONE (pivot tables, same push); CARD 5 DONE (18
text/reference fns, pushed 02d4a01; bare ROW/COLUMN → CARD 14 with cost
documented); Word lane DONE (hyperlinks/images/headers-footers, full docx
round-trip, desktop check PASS; _DocxRels mutable-class builder silently
dropped state under test-tree runs — copy-return struct idiom fixed it,
NEW QUIRK for the ledger); PPT lane DONE (bullet levels + @layout variants,
pushed 7a856ed; NEW RUNNER BUG: spec file killed at ~60s budget still
prints PASS — bug doc test_runner_60s_silent_kill_greenwash_2026-07-04.md).
**~372 callable functions.** Open: CARDs 6 (deploy, build in flight),
14, 15, 16 (pilot next).

### CARD 16 pilot status (2026-07-04, honest blocker)
Wiring SHIPPED (gui.spl: office_gui_frame → BrowserBackend.create 96x64
"software" → render_frame(state.tree, state) → pixels_argb_u32; `office
counter --gui` CLI; pilot recovered from a full clobber-delete via swept
commit 33e635bc). Pivot '<name[' generics-ambiguity parse errors fixed
(3 sites — `v < arr[i]` misparses as generic application under `run`; use
an intermediate val; NEW LEDGER ENTRY). **E2E proof BLOCKED:** the run
enters office_gui_frame and does not return within 500s, while
browser_backend_pixel_paths_spec passes in ~61s under identical load — the
hang/slowness is specific to BrowserBackend.render_frame on a UITree (vs
the spec's direct-HTML path), not machine contention. The pilot spec is
HELD OUT of the tree (scratchpad backup/round3/office_gui_pilot_spec.spl.held)
because committing it would hang the test daemon (see the 60s silent-kill
bug — it would greenwash anyway). Do NOT claim GUI works until the proof
line prints.

### CARD 16 blocker DIAGNOSED (2026-07-04, measured)
The pixel stage of render_frame scales ~QUADRATICALLY with `<style>` CSS
size under the interpreter: empty ~4.7s, 10KB ~6.9s, 40KB >60s, full
generate_css("dark") 292,724B never completes. Routing:
simple_web_engine2d_renderer.spl:887 (any class/id selector disables the
fast heuristic) → :892 simple_web_layout_render_html_pixels (the quadratic
stage). **AUDIT: browser_backend_pixel_paths_spec is GREENWASHED — the
renderer HARD-CODES that spec's widget ids (:775-784) and paints fixed
rectangles (:786); the step-1 example validation never exercised the real
pixel path.** Bug doc:
doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md.
Unblock path: fix the quadratic stage or add a cached/minimal-CSS knob
(~10KB budget measured feasible at 96x64); REMOVE the hard-coded fast path
and make the framework spec pass on the real path; then re-run the pilot
acceptance. gui.spl + mod.spl wiring is committed and correct against the
real API — it goes green the moment the renderer fix lands.

---

## Definition of done per card
Spec green under the COORDINATOR's own run (not just the agent's report) →
pathspec commit → `git show HEAD:<file> | grep <symbol>` nonzero → memory
file line appended → honest gap-count decrement in this doc.
