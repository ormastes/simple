# Anonymous `fn` block call argument loses indentation

- ID: `parser_anonymous_fn_block_call_arg_2026-08-03`
- Severity: P1
- Status: fixed — focused parser verification passed; Stage 4 retry pending (2026-08-03)
- Owner: `/root/option_native_codegen_rootcause` — CLAIMED

## Reproducer

`src/app/cli/api_surface_snapshot.spl:210` passes a multi-statement anonymous
function to `sort_by`:

```spl
all_entries.sort_by(fn(a: SnapshotEntry, b: SnapshotEntry) -> i64:
    if a.module_key < b.module_key:
        return -1
    if a.module_key > b.module_key:
        return 1
    return 0
)
```

The pure-Simple checker reported `expected ), got if` at the second `if`, then
seven recovery diagnostics on the closing `)`, result literal fields, and `}`.
The Rust seed parser accepted the same source and reached execution before an
unrelated missing `runtime_args` function, proving the grammar divergence.

## Root cause and fix

`parse_fn_lambda_after_kw` handled a block body inside call parentheses without
enabling the lexer's existing forced-indentation mode. Newline and indentation
tokens were therefore suppressed by `paren_depth`, making the first statement
look like the anonymous function's complete inline body.

The anonymous-`fn` path now mirrors the established backslash-lambda lifecycle:
enable forced indentation before consuming `:`, parse the block until dedent,
closing parenthesis, comma, or EOF, repair the indent stack when the call token
terminates the block, and disable forced indentation on both block and
expression-body exits.

## Reopened Stage 4 expression-body case

The block-body repair enables forced indentation before consuming every
anonymous-function colon.  For an expression body such as
`target_triple_fn: fn(): "check"`, parsing the body scans the following newline
while forced indentation is still active.  Disabling forced mode afterward
does not remove that already-current `Newline`, so the enclosing call parser
expects `)` or `,` and rejects the legal closing delimiter on the next line.
The full Stage 4 occurrence is the five `BackendPort(...)` constructors in
`src/compiler/driver/driver_types.spl:72-109`.

The repair normalizes legal newline layout once in
`compiler.core.parser_expr.parse_call_arg`, after placeholder-lambda
transformation and before every constructor/function/method call loop inspects
its comma or close parenthesis.  This avoids four duplicated parser-loop edits
and does not change ordinary parenthesized arguments, whose lexer stream already
suppresses newlines.

Focused evidence (Rust seed executing the current pure-Simple parser source):

- before: 4 passed / 2 failed; the exact `BackendPort` expression callbacks and
  newline-before-comma adjacent argument failed;
- after: 6 passed / 0 failed, including all earlier block-body, comma,
  expression-body, and malformed-then-recovery cases.

No production constructor was reformatted and no full Stage 4 run was made in
this scoped repair lane.

## Regression coverage

`test/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.spl`
covers the exact comparator, comma termination with an adjacent argument,
unchanged expression-bodied syntax, and malformed-then-valid parser error-state
recovery.
