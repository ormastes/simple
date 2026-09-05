# Comparison chain closed by `(` is misread as a generic-argument list

Status: FIXED — Rust and pure-Simple parsers; Stage3 proof 2026-08-22
Component: `src/compiler_rust/parser/src/expressions/postfix.rs`
           (`try_skip_ident_generic_args`)

## 2026-08-22 pure-Simple Stage 3 regression

The original fix initially landed only in the Rust seed twin. The pure-Simple
`10.frontend/core/parser_expr.spl::try_skip_ident_generic_args` now has the
equivalent numeric-argument separator ratchet. The original admitted Phase2
had rejected valid source in `src/compiler/frontend/core/flat_pool_codec.spl:94`:

```simple
if n < 0 or n > (self.lines.len() - self.pos):
```

The valid source remained unchanged. On 2026-08-22 a freshly rebuilt and
admitted pure-Simple ARM64 Phase2 compiler parsed, promoted, committed, and
released all 665 Stage3 surfaces with no const-generic diagnostic. Stage3 then
advanced to `phase3:hir_typecheck:start`, where a separate native call-target
mis-resolution now blocks it. That downstream crash does not weaken the parser
proof.

## 2026-08-24 re-report was a STALE STAGE BINARY, not a parser regression

A lane re-reported this as a new, unfiled stage-3 blocker
(`src/app/office/sheets/data_ops.spl:38:33`, phase 2, 3 of 3 runs, "reproduced
on the working tree AND a pinned snapshot"). It is neither new nor a source
defect. Evidence:

- Column 33 of that line is the `(` in
  `if key_col < 0 or key_col > (max_col - min_col):`. The `Tensor<i64, 2>` in
  the message is canned EXAMPLE text inside the diagnostic string
  (`parser_expr.spl:882`), not anything present in the source. Reading it as a
  const-generics feature gap is a misread the message invites.
- The Rust seed accepts the shape: `bin/simple run` on a minimal fixture
  exits rc=0 and prints `true`.
- The pure-Simple source is fixed at `bf440c278b8` (2026-08-22 01:48), whose
  `const_arg_needs_separator` ratchet branch is ordered ahead of the
  keyword-as-type-name branch, so `or` (TOK_OR = 56) breaks the walk.
- The stage binaries on disk predate that fix:
  `build/bootstrap/stage2/x86_64-unknown-linux-gnu/simple` is dated
  **2026-08-20 23:53**. Running it directly on the minimal fixture
  (`compile --format=smf`) reproduces exactly: rc=1, `[ERROR] phase 2 FAILED`,
  two `const generic` occurrences. That is the whole reproduction — including
  "on a pinned snapshot", since the snapshot pins source, not the binary.

Resolution: no source change. Stage 3 is unblocked by a stage redeploy, not by
a parser edit and not by rewriting `data_ops.spl` (which is valid Simple and
must not be normalised around the bug).

Gap this re-report exposed and closes: `bf440c278b8` landed source-only with no
spec, so nothing pinned the pure-Simple half. Added
`test/01_unit/compiler/parser_comparison_chain_not_generic_args_spec.spl` —
the incident shape plus defect-class neighbours (`while` condition, returned
expression, ident-only chain with no numeric literal, `>>` kept as a shift),
and an absence control that a genuine `Box2<i64, 2>` const-generic argument is
still diagnosed. It honours `SIMPLE_BIN`, so aiming it at a pre-fix stage
binary is the failing-pre-fix run.

Secondary defect, left open deliberately: the diagnostic quotes a fixed
`Tensor<i64, 2>` example instead of the offending source tokens, which is what
sent this investigation to "const generics are unimplemented". Worth quoting
the real tokens if this text is touched again.

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
