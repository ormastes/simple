# Coverage collector never records top-level `val`/`pub val` initializers, `match` heads, expression-position `if` heads, or certain executed `return`/`break` statements

- **Date:** 2026-08-15
- **Area:** interpreter coverage collector (`SIMPLE_COVERAGE=1` lane; reporter in
  `src/app/test_runner_new/test_runner_single.spl` `_cov_report_for_file` /
  `_cov_is_recordable`)
- **Severity:** medium — structurally caps line coverage of several stdlib
  modules below 100% no matter how thoroughly they are tested, so "100% of
  recordable lines" claims need a per-line exclusion table instead of the
  headline percentage.

## Symptom

During the 2026-08-15 browser_engine coverage-closure campaign
(`test/01_unit/browser_engine/*_coverage_closure_spec.spl`), several line
classes remained "uncovered" although the enclosing functions were verifiably
executed (their sibling lines, both branch outcomes in `coverage-branch`, and
the asserted return values all prove execution):

1. **Module top-level `val`/`pub val`/`const` initializers.**
   `simple_web_html_layout_renderer_declarations.spl:419`
   (`val _APPLY_DECLS_DISPATCH_PROPS: [text] = [...]`) is read by every
   dispatch call yet never appears in the `lines` dump. Same for
   `simple_web_html_layout_renderer_style.spl:5` (`const
   SIMPLE_WEB_STICKY_TOP_AUTO`). The reporter's own RESIDUAL note documents the
   flatten-path attribution gap (top-level statements are filed under
   `<entry>`), so these under-report by design; the recordable-line heuristic
   still counts them in the denominator because they contain `" = "`.

2. **Class field DEFAULT initializer lines.** 24 lines of
   `simple_web_html_layout_renderer_style.spl`'s `class Style` (e.g. line 19
   `background_image_uri: text = ""`) match the reporter's `" = "` fallback and
   inflate the denominator, but the collector has no statement to record for a
   field default — they can never be hit.

3. **`match` statement heads.** `render_fixtures.spl:310` (`match ch:` in
   `br_hex_value`) — the function's digit arms are all exercised by the hex
   parsing specs (its outputs are asserted) yet the head line never records.
   `match ` is explicitly in `_cov_is_recordable`'s allow list, so every
   tested `match` permanently costs one denominator line.

4. **Expression-position `if` heads (tail `if cond: a else: b`).**
   `layout_table.spl:97,109,175` — branch coverage records BOTH outcomes of
   these decisions in the same run (`coverage-branch` rose to 32/34 as the
   closure spec drove them both ways) while the line itself stays uncovered:
   statement-position `if` records, expression-position `if` does not.

5. **Sporadic executed `return`/`break` statements.**
   `simple_web_html_layout_renderer_declarations.spl:82,213` (`return ""`
   guards whose surrounding condition lines record and whose `""` results are
   asserted), `declarations.spl:995` (an `if` head between two recorded
   lines), and `render_fixtures.spl:363` (a `break` reached via
   `browser_renderer_find_char` returning its 999999999 miss sentinel — the
   sibling `break`s at 360/366/369/372 all record in the same run).

## Impact measured 2026-08-15

| module | reported | recordable-line honest |
|---|---|---|
| simple_web_html_layout_renderer_style.spl | 93% (388/415) | 100% (25 artifact lines: field defaults + const) |
| simple_web_html_layout_renderer_declarations.spl | 99% (809/815) | 100% (1 top-level val, 3 executed-unrecorded, 2 unreachable-defensive) |
| render_fixtures.spl | 97% (295/302) | 100% (1 match head, 1 executed-unrecorded break, 5 unreachable-defensive) |
| layout_table.spl | 96% (96/99) | 100% (3 expression-if heads, both branches proven) |
| layout_box.spl | 0% (0/0) | vacuous — the file has zero recordable lines at all |

## Expected

Either (a) the collector records these statement kinds, or (b)
`_cov_is_recordable` excludes what the collector cannot record — class field
defaults, top-level initializers, `match` heads, and expression-position `if`
heads — so the denominator matches the collector's actual capability and a
fully-tested module can report 100%.

## Repro

```
SIMPLE_COVERAGE=1 bin/simple test --coverage \
  test/01_unit/browser_engine/layout_table_coverage_closure_spec.spl --no-session-daemon
# -> coverage: .../layout_table.spl 96% (96/99), coverage-branch 94% (32/34)
# lines 97/109/175 are the three tail if-expressions, both branches taken.
```
