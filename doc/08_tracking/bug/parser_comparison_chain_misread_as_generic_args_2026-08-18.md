# Comparison chain closed by `(` is misread as a generic-argument list

Status: PARTIAL — Rust seed fixed; pure-Simple parser OPEN (reproduced 2026-08-22)
Component: `src/compiler_rust/parser/src/expressions/postfix.rs`
           (`try_skip_ident_generic_args`)

## 2026-08-22 pure-Simple Stage 3 regression

The original fix landed only in the Rust seed twin. The pure-Simple
`10.frontend/core/parser_expr.spl::try_skip_ident_generic_args` has no
`need_comma` ratchet and still accepts consecutive numeric/keyword/identifier
tokens as one speculative type-argument list. A provenance-admitted ARM64
Phase 2 therefore rejects valid source in
`src/compiler/frontend/core/flat_pool_codec.spl:94`:

```simple
if n < 0 or n > (self.lines.len() - self.pos):
```

It reports the unrelated const-generic diagnostic three times after parsing
all 664 surfaces. The valid source is intentionally unchanged. The next fix
must port the existing Rust `need_comma` state machine into the pure parser and
run this file plus the existing defect-class spec and a real generic-call
positive control before Stage 3 is retried.

## Symptom

```
error: compile failed: parse: in "src/app/office/sheets/data_ops.spl":
Unexpected token: expected a type in generic argument position (Simple has no
const generic parameters, so a numeric literal such as `Tensor<i64, 2>` is not
a valid generic argument; drop the explicit generic arguments and let them be
inferred, e.g. `Tensor(...)`), found integer literal
```

Minimal reproducer (`/tmp/p3.spl`):

```
fn f(a: i64, b: i64, c: i64) -> i64:
    if a < 1 or a > (b):
        return 1
    2
```

Real site: `src/app/office/sheets/data_ops.spl:38`

```
    if key_col < 0 or key_col > (max_col - min_col):
```

## Root cause

`try_skip_ident_generic_args` speculates a generic-argument list on `Ident <`
and *confirms* it when a balanced `>` is followed by `(`, `.`, `::` or `{`.
Its scan loop accepted an unbounded run of arguments with **no separating
commas**, and `parse_type` accepts a bare keyword/identifier as a named type.
So the token run `key_col < 0 or key_col > (` scanned as three "arguments"
(`0`, `or`, `key_col`), reached `>` + `(`, was declared a confirmed generic
call, and hard-errored on the const-generic span recorded for `0` — instead of
backtracking into the comparison chain it actually is.

The const-generic diagnostic itself (added 2026-08-17) is correct; what was
missing is the grammar constraint that makes "confirmed" mean confirmed.

## Fix

A generic-argument list is `T (, T)*`. The scan now carries a `need_comma`
ratchet: after an argument is consumed without a following `,`, the next
argument token breaks the scan (`ok` stays false), so the speculation
backtracks and the comparison parses normally. Nesting resets it (`<`) and a
nested close sets it (`>`), so `Box2<Box2<i64>, i32>` is unaffected.

## Blast radius

This is a HARD parse error, so every module whose import graph reaches
`data_ops.spl` failed to LOAD. That includes `src/app/cli/main.spl`, which is
the subject of `test/integration/app/cli_log_modes_spec.spl` and its
`test/02_integration` mirror. Those specs shell out to the CLI and assert on
the exit code, so the defect surfaced only as the opaque
`Process exited with code 1` of failure class 2 in
`doc/08_tracking/test/failure_taxonomy_2026-08-18.md`.

Note for that taxonomy: the `*_log_modes_spec.spl` family is **not** a single
root cause. It is a symptom carrier. Most of its members' CLI targets fail with
the class-1 `object` type-erasure defect (`undefined field 'valid': cannot
access field on value of type 'object'`), which is owned separately; this
parser defect is an independent second cause within the same family.

## Tests

- `test/01_unit/compiler/parser/comparison_chain_then_paren_group_spec.spl`
  — defect-CLASS spec (paren group, `.`/method close, constructor close,
  `and`-chained form, non-literal left operand) with a positive control that
  real generic calls still parse.

## Census (2026-08-18) — the `log_modes` family is NOT one root cause

Probed all 102 distinct CLI targets referenced by
`test/integration/app/*_log_modes_spec.spl` by running each `main.spl --help`
directly and reading the child's stderr:

| child error | targets |
|---|---|
| `semantic: undefined field 'valid': cannot access field on value of type 'object'` (failure class 1) | 94 |
| ran clean | 5 |
| `parse:` — this defect, via `src/app/office/sheets/data_ops.spl` | 1 (`src/app/cli/main.spl`) |
| `parse:` — a DIFFERENT parse defect in `src/app/svim/tui_shell.spl` ("expected expression, found Plus") | 1 (`src/app/svim/main.spl`) |
| `method get_namespace_id not found on type object` (class 1) | 1 |

So ~92% of the family is the class-1 `object` type-erasure defect wearing a
`Process exited with code 1` mask. Fixing this parser defect clears the parse
failure for `src/app/cli/main.spl` only; the family will not go green until
class 1 does.

## Follow-ups unmasked by this fix (separate defects, not fixed here)

1. `src/app/cli/main.spl --help` now exits 0 (was 1) but prints **nothing** on
   stdout, so `cli_log_modes_spec.spl` still fails its `to_contain("Simple
   Language")` assertions. Previously masked by the parse failure.
2. `src/app/svim/tui_shell.spl` has an unrelated parse error
   (`expected expression, found Plus`).

## Note on diagnosability (taxonomy recommendation #3)

There is **no shared subprocess harness** to fix. Each `*_log_modes_spec.spl`
inlines its own `extern fn rt_process_run` helper and binds the child's `err`
but never asserts on or prints it. Surfacing child stderr would therefore be a
~193-file edit, not a one-line harness change. Recorded so the recommendation
is not re-attempted as if it were cheap.
