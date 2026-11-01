# Stage2 parser rejects an `if` expression with `<value> else:` on the continuation line

- **ID:** stage2_if_expr_then_value_next_line_parse_2026-11-01
- **Severity:** P1 (blocks the phase 3 per-file parse)
- **Status:** open (source workaround in place)
- **Component:** parser (10.frontend), frozen stage2 `C:/dev/p3new/stage2.exe`
- **Found by:** lane p3-mir-to-obj, per-file pool run `pf2` (2026-11-01)

## Symptom

```
[ERROR] parse error in .../src/compiler/80.driver/driver_build/incremental.spl: 1241:67:unexpected token in expression: : ':'
[build] phase=parse state=failed ... failed=1
```

The source (added by a2001a4129e / 7a44f5d65a4, after run 12):

```
val recorded_hash = if entries.contains_key(change.path):
    entries[change.path].fingerprint.content_hash else: ""
```

The parser accepts the then-value on the indented continuation line but then
treats the trailing `else:` as an unexpected `:` token. The block form, with
`else:` on its own dedented line, parses.

## Impact

Every phase 3 build whose source includes eb72b5c9fde (run 13 included) fails
parse for `compiler.driver.driver_build.incremental`. Under go-to-end that
module and its importers drop out of HIR.

## Workaround (bootstrap only)

`@workaround bug=stage2_if_expr_then_value_next_line_parse_2026-11-01` at the
site: a `var` plus a plain `if` statement. Remove it once a stage2 with the
parser fix is admitted.

## Real fix

In the expression parser, after the inline then-branch of an `if`
expression on a continuation line, accept `else:` / `elif` on that same
line. Regression spec:
`test/01_unit/compiler/parser_if_expr_then_value_next_line_spec.spl`.
