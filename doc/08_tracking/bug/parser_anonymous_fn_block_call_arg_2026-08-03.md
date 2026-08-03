# Anonymous `fn` block call argument loses indentation

- ID: `parser_anonymous_fn_block_call_arg_2026-08-03`
- Severity: P1
- Status: fixed
- Owner: pure-Simple frontend parser

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

## Regression coverage

`test/01_unit/compiler/parser/parser_anonymous_fn_block_call_arg_spec.spl`
covers the exact comparator, comma termination with an adjacent argument,
unchanged expression-bodied syntax, and malformed-then-valid parser error-state
recovery.
