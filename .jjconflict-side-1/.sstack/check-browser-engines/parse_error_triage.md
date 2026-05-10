# Browser Parse-Error Triage

## Summary

- **65 parse errors** across `examples/browser/` in 4 distinct clusters.
- **80 warnings** (68 REQC001 + 12 REQC004) — out of scope for this doc.
- Tests pass 440/440 despite these — Simple's `use {Symbol}` does selective parsing, so files with unparseable bodies are never fully compiled by callers that don't import the offending symbols.

## Cluster 1 — `use X.(Symbol)` should be `use X.{Symbol}`

- **45 files** (largest cluster). Biggest mechanical win.
- Error: `Unexpected token: expected identifier, found LParen` at the `(` after `.`.
- Sample: `examples/browser/feature/layout/block.spl:6`
  ```
  use examples.browser.entity.dom.box_types.(BoxKind, BoxModel, LayoutBox)
  ```
  Should be:
  ```
  use examples.browser.entity.dom.box_types.{BoxKind, BoxModel, LayoutBox}
  ```
- Same-file verification: line 7 (same file) already uses the correct `{}` form:
  ```
  use examples.browser.feature.style.css_functions.{FunctionContext, resolve_css_function}
  ```
- Pattern count across the tree:
  - `use X.(` → **45** usages (all broken)
  - `use X.{` → 106 usages (correct)
- **Fix:** sed replace — safe, mechanical, per-file.
- **Estimate:** 10 min including re-sweep.

## Cluster 2 — `[T<G,G>]()` empty-list-with-generic constructor

- **13 files, 19 occurrences**.
- Error: `Unexpected token: expected expression, found RBracket`.
- Sample: `examples/browser/entity/net/url_types.spl:41`
  ```
  UrlSearchParams(params: [Pair<text, text>]())
  ```
  The parser chokes on `]` after the generic args `<text, text>`.
- Other sites: `storage_types.spl:15`, `cache_types.spl:38`, `request_types.spl:28,41,48`, …
- **Fix options:**
  - (a) Replace with an explicit `var` + type-annotated empty list: `val xs: [Pair<text, text>] = []; ...`
  - (b) Introduce a factory helper: `pair_text_text_list()` returning `[Pair<text, text>]`
  - (c) File a parser bug — `[T<A,B>]()` should parse as empty-list constructor with type arg.
- Preferred: **(a)** — minimum disruption, works within current parser. Some sites need inline usage and may need (b).
- **Estimate:** 25-35 min.

## Cluster 3 — Match arms with field-keyword args

- **6 files**, all in `examples/browser/feature/parser/css_*.spl`.
- Error: `Unexpected token: expected Comma, found Colon`.
- Sample: `examples/browser/feature/parser/css_parser.spl:96`
  ```
  match part:
      SelectorPart.Id(name: _):
          ids = ids + 1
      SelectorPart.Class(name: _):
          classes = classes + 1
      SelectorPart.Attribute(name: _, op: _, value: _):
  ```
  The parser wants comma-separated positional args in the match-arm destructuring, but the code uses `field: _` keyword syntax.
- **Fix:** requires knowing Simple's correct match-arm destructuring for enum variants with named fields. Candidates:
  - Positional: `SelectorPart.Id(_)` (lossy — drops the field name)
  - Struct form: `SelectorPart.Id{name: _}` (unverified)
  - Bindings: `SelectorPart.Id(name) if name == "foo"` (only if value check needed)
- **Research needed** before fixing.
- **Estimate:** 20-30 min (5-10 research + fixes).

## Cluster 4 — `devtools.spl:114` one-off

- **1 file**, likely edge case related to `!` unwrap operator or interpolation formatting.
- Error: `expected '(', '{', or '[', found Newline`.
- Surrounding code uses `session!` unwrap and interpolated strings with dotted member access — `tab={s.tab_id}`.
- **Estimate:** 5-10 min after investigation.

## Warnings (not fixed here)

- **68 REQC001**: `pass_*` without rationale. Rule: use `pass_todo("what remains", "hint")` or `pass_do_nothing("why correct")`.
- **12 REQC004**: (not sampled — read `src/compiler/35.semantics/lint/` to confirm rule meaning before fixing).
- Top-warning files: TBD from log.

## Recommended Order

1. **Cluster 1 now** — biggest mechanical win, zero risk.
2. **Re-run lint sweep** — confirm drop from 65 → 20 errors, no regression.
3. **Re-run browser test suite** — confirm 440/440 still pass.
4. **Stop, report, get user direction** on clusters 2-4 (need research) and warnings.
