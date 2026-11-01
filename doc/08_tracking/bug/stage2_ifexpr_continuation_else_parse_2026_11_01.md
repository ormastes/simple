# Stage2 parser rejects a continued if-expression whose `else:` trails the value line

- **ID:** stage2_ifexpr_continuation_else_parse_2026_11_01
- **Priority:** P2
- **Status:** root fix in source; workaround revert-ready after stage3 self-build
- **Owner area:** `src/compiler/10.frontend` expression parser (if-expression continuation)
- **Found by:** phase-3 run 13 (frozen stage2 `C:/dev/p3new/stage2.exe`, source ef0681fc0e1), release/1.0.0 at eb72b5c9fde

## Symptom

```
[ERROR] parse error in .../src/compiler/80.driver/driver_build/incremental.spl: 1241:67:unexpected token in expression: : ':'
[build] phase=parse state=failed ... failed=1
```

The whole phase-3 build stops at parse (phase 2 FAILED, 0 objects).

## Minimal repro

```simple
fn pick(m: Dict<text, text>, k: text) -> text:
    val v = if m.contains_key(k):
        m[k] else: ""
    v
```

The value expression and `else:` share the continuation line after `if cond:`.
The frozen stage2 parser treats `else` as the end of the then-expression and then
fails on `:`. Block form (`else:` on its own line) and the one-line form
`if c: a else: b` both parse.

## Workaround

`src/compiler/80.driver/driver_build/incremental.spl` (macro RR pre-edit companion
hash): rewritten as `var recorded_hash = ""` + `if ...: recorded_hash = ...`.
Behavior-identical. Tagged `@workaround bug=stage2_ifexpr_continuation_else_parse_2026_11_01`.

Other sites of the same shape exist outside the phase-3 closure (`src/app/build/scheduler/*`);
they did not fail in run 13 and are left unchanged.

## Removal condition

Remove the workaround after the bootstrap completes on a stage2 whose parser accepts
the continued form (check current `src/compiler/10.frontend` with the repro above).

## Root fix (2026-11-01)

Confirmed the current pure-Simple frontend also rejected the repro (seed-run probe:
`unexpected token in expression: ':'` at 3:18). Cause: `parse_if_expr`'s colon-block
then-body (`parse_block`) kept looping after `m[k]` and tried to parse `else` as a
statement. Fix in `src/compiler/10.frontend/core/parser_stmts.spl`: for an if-expression
colon block whose body starts on the next line, the indented body returns when its
statement is followed by a same-line `else`/`elif`; the open INDENT is closed by the
existing continued-indent unwind. Spec:
`test/01_unit/compiler/frontend/ifexpr_continuation_else_parse_spec.spl` (4/4 pass, seed).
