# LaTeX renderer: range upper bound fixed at two call sites, root cause unfixed

- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).
- **Severity:** Medium
- **Found by:** adversarial review of `464cb52500c9` ("LaTeX sum/int renderer dropped range upper bound")
- **File:** `src/lib/common/math_repr.spl`

## What the commit fixed (verified)

Both halves work: `sum(i,1..n) i` -> `\sum_{i=1}^{n} i` and `int(x,0..1) x` ->
`\int_{0}^{1} x`. Expression bounds (`a+1..b*2`) and decimal bounds (`0.5..1.5`)
render correctly — the tokeniser emits `..` as one token and guards decimals
(`math_repr.spl:194,213`). The pretty/text/debug renderers were already correct.

## MED — the root cause is unfixed; siblings still drop the upper bound

`_expr_latex` has **no `..` production** (`math_repr.spl:459-497`). The commit
patched the two `sum`/`int` call sites, not the range handling, so any *other*
function argument containing a range still truncates silently:

- `lim(x, 0..1) x` -> `\lim(x, 0) x`   (upper bound gone)
- `f(1..n)`        -> `\operatorname{f}(1)`

The family is exactly two remaining sites: the generic known-fn path
(`:462-473`) and the generic `\operatorname{}` path (`:487-497`). There is no
`prod`/`bigcup`/`bigcap`/`union` renderer in this file, so the sweep is complete
at two.

## LOW — `_split_range` is depth-unaware

`_split_range` (`:347-364`) splits on the **first** `..` regardless of nesting:
`int(x, f(a..b)..n) x` -> `\int_{\operatorname{f}(a)}^{b} x` — wrong bounds, not
a placeholder. The debug renderer has the same bug (`:974`, `:991`):
`Int(x, Call(f, Id(a)), Id(b), Id(x))`. Contrived input, hence low.

## LOW/INFO — open ranges

`sum(i, ..n)` -> `\sum_{i=?}^{n}` (`?` placeholder, consistent with the file's
convention). `sum(i, 1..)` -> `\sum_{i=1}`, valid LaTeX but indistinguishable
from the no-range form.

## LOW — the shipped repro spec under-constrains

`test/01_unit/lib/common/math_repr_sum_range_repro_spec.spl` asserts only
`to_contain("n")` + `to_contain("^{")`. That would also pass on
`\sum_{i=?}^{n}`, and it covers **sum only** — the `int` half of the commit
shipped with no test at all.

## Fix

Handle `..` in `_expr_latex` itself so every argument position inherits it, make
`_split_range` bracket-depth-aware, and tighten the repro spec to an exact
expected string covering both `sum` and `int`.
