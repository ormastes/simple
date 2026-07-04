# Writing Calc (Excel) Functions — Developer Guide

Everything needed to add Excel-compatible functions to
`src/app/office/sheets/formula.spl` (~396 callable functions as of
2026-07-04). Written for implementation agents; battle-tested over 18
multi-agent rounds. Follow it exactly — every rule here was paid for.

## 1. Pick the right dispatch path

A function's ARGUMENT SEMANTICS decide where it lives. Adding to the wrong
path is the #1 failure mode (the numeric path coerces everything to f64 and
destroys type information).

| Path (find these fns in formula.spl) | Arg semantics | Examples living there |
|---|---|---|
| `_dispatch_function(name, args: [[f64]], sheet)` | pure numeric; ranges flattened to f64 lists | SUM, PMT, MMULT-scalar helpers, BESSELJ |
| `_is_text_function` + `_dispatch_text_function` | display STRINGS of args | UPPER, TEXT, DEC2BIN, ROMAN, DATEDIF (text unit arg!) |
| `_is_info_function` + `_eval_info_function` | raw typed CellValue per arg | ISTEXT, ISBLANK, TYPE, NA |
| `_is_a_variant_function` + `_eval_a_variant_function` | raw cells; text=0, TRUE=1 | AVERAGEA, STDEVA |
| `_is_criteria_function` + `_eval_criteria_function` | range + criteria string | COUNTIF, SUMIF |
| `_is_ifs_function` + `_eval_ifs_function` | value range FIRST + range/criteria pairs | SUMIFS, MAXIFS |
| `_eval_lookup_function` / `_is_x_lookup_function` + `_eval_x_lookup` | raw range TEXT + needle | VLOOKUP, XLOOKUP, MATCH |
| `_eval_db_function` | database + field + criteria ranges | DSUM, DGET |
| `_is_count_range_function` + `_eval_count_range_function` | cell-level display access | COUNTA, COUNTBLANK |
| `_is_ref_function` + `_eval_ref_function` | reference itself (not its value) | ROW, COLUMN, ADDRESS, FORMULATEXT |
| `evaluate_formula_array` (array registry) | returns [[text]] 2D grid → SPILLS | SEQUENCE, TEXTSPLIT, MMULT, SORTBY |
| `_canonical_name` match table | pure alias → base name | STDEV.S→STDEV, RANK.EQ→RANK |

Dotted names lex correctly (dots between alpha/digit runs) — no lexer work
needed for new `X.Y` names.

## 2. Reusable numeric machinery (NEVER reimplement)

- `_exp_f64`, `_ln_f64`, `_powf(base, exp)` (fractional powers — `_pow_f64`
  TRUNCATES the exponent to int; never use it for non-integer exponents)
- `_sqrt_f64`, `_fabs`, `_sin_f64`/`_cos_f64`/`_atan_f64`, `_atan2_f64`,
  `_sinh_f64`/`_cosh_f64`
- `_gammaln` (Lanczos), `_erf`, `_norm_cdf`, `_norm_inv_std` (Acklam)
- `_betainc(x,a,b)` + `_betainc_inv`, `_gammainc_p(a,x)` + `_gammainc_inv`
  (T/F/chi-square/beta/gamma distributions are all thin wrappers over these)
- `_binom_pmf`, `_fact_i64`, combinatorics near COMBIN
- Dates: `_serial_from_civil`/`_civil_from_serial` (Hinnant, Excel 1900
  system), `_is_weekday`, EOMONTH-style month clamp helpers
- Complex: `_parse_complex`/`_format_complex` (format omits unit coefficient:
  "8+i" not "8+1i"), `_c_div`
- Securities: `_daycount_frac` (bases 0-4), `_coup_pcd`/`_coup_ncd`
- Criteria: `_criteria_matches(display, value, criteria)` — the `.to_f64()`
  idiom lives here; copy its shape for any new criteria matching
- Solvers: bisection preferred over Newton (50-100 iters, bracket, converge
  or #ERR) — see `_fin_rate`, `_betainc_inv`
- Origin cell: `_formula_origin_key` module var (set by the recalc driver)
  — how bare ROW()/COLUMN() know their cell

## 3. The interpreter quirk ledger (violations cost hours)

1. Chained method calls FAIL at runtime: `x.f().g()` → intermediate `val`s.
2. Aggregates pass by copy: mutating helpers RETURN the object; callers
   reassign. Arrays too.
3. `f64?` match-binding does NOT unwrap. Use the `.to_f64()` idiom.
4. NO array parameters into helpers — `[[text]]` params misparse and
   variable-indexing an array param reads 0. Inline the logic over LOCAL
   flat arrays (row-major `r*cols+c`); only scalars cross call boundaries.
5. `v < arr[i]` misparses as a GENERIC under `bin/simple run` (warning-only
   under `test`): hoist `val cur = arr[i]` then compare.
6. Reserved/broken identifiers: `grid` and `unit` — as locals AND parameters.
7. Dict-in-struct under copy-return corrupts values — parallel arrays.
8. String interpolation is `"{expr}"` — literal braces in string literals
   are interpolation. Build strings by concatenation when in doubt.
9. Empty-string formula results display as raw `={expr}` — make emptiness
   observable in specs via `="["&F(x)&"]"`.
10. f64-returning user functions return 0.0 under standalone
    `bin/simple run` (i64 fine) — verify numerics ONLY through the spec
    harness path.
11. Probes go in the session scratchpad, never under `examples/`.

## 4. Ground truth discipline

- Every function is verified against an EXTERNAL reference BEFORE the spec:
  Excel's documented function examples (support.microsoft.com wording),
  textbook values, or hand computation shown in the probe.
- Task-brief reference values have been wrong 4 times in this campaign
  (PPMT, F.INV, GAMMA(-3.75), F.TEST data). When your recomputation
  disagrees with the brief, TRUST YOUR RECOMPUTATION, assert the true value,
  and flag the correction in your report. Never loosen an assertion to make
  a wrong reference pass.
- No unverified math ships. A function you cannot verify to 6 significant
  digits gets SKIPPED with the numbers you got and the reason.

## 5. Spec pattern

File: `test/01_unit/app/office/sheets/formula_<batch>_spec.spl`. Model on
`formula_card14_spec.spl` (scalar) or `formula_xlookup_arrays_spec.spl`
(spill). Skeleton:

```
use std.spec
use app.office.sheets.spreadsheet.{Sheet}
use app.office.sheets.cell.{cell_display_text}
use app.office.file_formats.{recalculate_formula_cells}

fn _eval(formula: text) -> text:
    var sh = Sheet.new("f")
    sh.set_value("B1", formula)
    sh = recalculate_formula_cells(sh)      # MUST reassign (copy semantics)
    cell_display_text(sh.get_cell("B1"))
```

- Float asserts: `to_start_with("0.145918")` — 6+ significant digits.
- Spill asserts: set the formula, recalc, then read NEIGHBOR cells.
- Cover #ERR domains for every function (bad domain, wrong arity behavior).
- Keep the FILE under 45 seconds total: the runner KILLS a spec file at
  ~60s and still prints PASS (greenwash bug) — a slow file proves nothing.
- Run a deliberate-fail probe once (add a wrong assertion, see it fail,
  remove it) to prove the tail of the file executes. Then run per-file:
  `bin/simple test test/01_unit/app/office/sheets/formula_<batch>_spec.spl`
  (directory batch runs hang — always per-file).
- Regressions: run 3-4 neighboring formula specs per-file; all green.

## 6. Working in this repo (agents)

- Parallel sessions sweep the working copy every 10-30s. Back up owned
  files (.pre-<batch> suffix) to the session scratchpad BEFORE editing and
  maintain AUTHORITATIVE FINISHED COPIES in scratchpad/work-<batch>/
  continuously. Re-grep your symbols after any pause; restore and continue
  if wiped. The coordinator commits — do NOT run jj/git.
- Report format: functions shipped + verified values (+corrections flagged),
  skipped-with-reason, spec path + count, regression results, new total
  estimate (the coordinator recounts — don't inflate).

## 7. Review checklist (for reviewer agents)

1. Recompute 3+ reported ground-truth values independently — do they match
   the spec's assertions exactly?
2. Is each function on the RIGHT dispatch path for its argument semantics
   (§1)? Text/type-sensitive functions on the numeric path = wrong results.
3. Grep the diff for quirk violations: chained calls, `< arr[`/`< name[`,
   `grid`/`unit` identifiers, array params into helpers, Dict-in-struct.
4. Does the spec cover #ERR domains and use 6-digit prefixes? Is the file
   fast (<45s)? Did the lane show a deliberate-fail probe?
5. Reused machinery (§2) instead of reimplementing? Flag duplicates.
6. Run the spec + 2 regressions yourself; paste results.

## Quirk-ledger addendum (2026-07-04, batch waves 10-14)

- **`grid` local corrupts the parser** — not a clean reserved-word error: declaring a local `grid` then using `grid.len()`/`grid[i]` derails the parse with a no-line-number `Unexpected token: expected Colon, found Dot` (or a segfault). Same family: `unit`. Name spill grids `rgrid`/`out_rows`. Bug: parser_grid_identifier_corrupts_parse_2026-07-04.md
- **`//` is not a comment** — its words parse as code and the error surfaces on the NEXT line as `variable X not found`. Only `#`. Bug: parser_double_slash_comment_misparse_2026-07-04.md
- **Top-level `it` outside `describe` is silently ignored** — deliberate-fail probes MUST be nested in a describe. Bug: test_runner_orphan_it_silently_ignored_2026-07-04.md
- **Bare-boolean assertions are no-ops** — `"x" == y` alone in an it-block is silently ignored; always `expect(...)` / `assert_*` matchers.
- **Function-evaluator cursor contract** — every `_eval_*` must return `next_pos` PAST its closing paren; returning the paren's own index corrupts the caller's parse (symptom: enclosing function reports wrong arity).
- **Numeric fns never go in `_is_text_function`** — a name listed there is hijacked to the text dispatcher before `_dispatch_function` sees it ("unknown text function").
- **Bare trailing `me` misparses** — a method ending in `me` (fluent-return intent) dies with `expected identifier, found Newline` (parser wants `.` after `me`). Sheet-style classes use in-place void mutators instead; no `return me` precedent exists in the codebase.
