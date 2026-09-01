# Rust interpreter loader rejects mixed inline/block if-expression chain

Date: 2026-08-25
Status: SOURCE FIXED; DEPLOYED IMPORT-RUNTIME EVIDENCE BLOCKED BY STALE SEED
Owner: `src/compiler_rust/parser/src/stmt_parsing/control_flow.rs`

## Symptom

The standalone Rust parser accepts the imported module's individual syntax
fragments, but the Rust bootstrap-seed interpreter fails while loading the full
module, before the importing SSpec executes an example:

```text
Unexpected token: expected expression, found Newline
```

The retained minimal reproducer is:

- `test/fixtures/parser_import_newline/escape_target.spl`
- `test/01_unit/compiler/parser_import_escape_newline_repro_spec.spl`

## Proven root cause

The failing executable identifies itself as the **Rust bootstrap seed**. Its
interpreter module loader parses imports with `simple_parser`, whose
statement-form `parse_if` recognized an inline first arm and then constructed
the following `elif` / `else if` arms as expression nodes. Both recursive call
sites used the narrow `parse_if_expr_after_condition` helper. Despite its name,
that helper parsed its own condition and then required an inline expression
immediately after `:`. A block arm therefore reached it with `Newline` current
and produced the observed diagnostic.

```text
Rust interpreter module import
  -> simple_parser::Parser
  -> stmt_parsing::control_flow::parse_if
  -> parse_if_expr_after_condition
  -> parse_expression with Newline current
```

The production repair routes both nested-arm call sites through the shared
`parse_if_expr`, which already accepts inline or indented bodies, and removes
the narrower duplicate helper. Structural Rust tests pin both spellings:
inline first arm, block `elif` or `else if`, final inline `else`, and the
following sibling statement. They also pin exact enclosing function-body
counts (`4` for the escape fixture and `3` for the non-escape fixture), so a
premature dedent or swallowed sibling cannot pass unnoticed.

This is not the raw-literal `}}` collapse: the reproducer contains no raw
literal or `}}`. It is not the frontend cache: the importing failure persists
with `--no-cache`. Independent imported fixtures proved parenthesized multiline
booleans, trailing `+`, multiline postfix `?`, and the triple-backslash quote
literal alone all parse.

## Pure-Simple parity evidence

The pure-Simple frontend is a separate implementation and is not the executable
that produced this failure. Its reset and append entrypoints both converge on
`parse_module_body`; append mode preserves the existing AST arena but does not
select a different statement grammar. Its current
`parser_stmts.spl::parse_if_expr` collects `elif` / `else if` arms iteratively
and calls the same `parse_block` path for each colon arm. This source parity,
plus the earlier reset/append inspection, is retained as negative evidence
against the original stale-append-state theory. No pure-Simple executable was
available in this lane, so this is not claimed as pure-Simple runtime
qualification.

## Required fix and acceptance

Keep both Rust `Expr::If` continuation call sites on the shared mixed-body
parser. Require a direct structural regression for each spelling and execute
the importing SSpec through the Rust interpreter for:

- `cp = 10`, an inline escape arm;
- `cp = 1`, the block-form control arm;
- `cp = 65`, the terminal inline `else` arm.

This closes the proven Rust loader/parser defect without rewriting valid
provider source. Pure-Simple runtime qualification remains a separate evidence
cell and must use a provenance-admitted self-hosted binary.

## Verification and provenance

- Current Rust parser source: the three focused structural cases pass (`3/3`),
  covering `elif`, `else if`, exact function-body counts, and the following
  sibling.
- Checked-in runner: the importing SSpec declares three cases but executes
  `0/3`, reproducing the pre-fix `expected expression, found Newline`. The
  runner explicitly identifies as a Rust bootstrap seed and is a prebuilt ELF
  from before this worktree repair (SHA-256
  `3ef64bffc68d0b1c2dd851d1f02976ca98fba6f88fbb406dddf56ba7f3ca27c0`,
  mtime `2026-08-25T06:08:41Z`). The focused Cargo command rebuilt the parser
  test artifact, not this CLI, so that SSpec result is not post-fix runtime
  evidence.
- Fresh isolated bootstrap build: the parser crate compiled, but building the
  current `simple-driver` exited `101` before linking because unrelated dirty
  compiler integration expects absent `read_trace`, import performance
  counters, `probe_source_cached`, and two `Lowerer` fields. Consequently no
  current-source bootstrap executable or post-fix importing run was produced.
  Those compiler errors are outside this bounded parser repair and are not
  bypassed or misreported as parser failures.
- No provenance-admitted pure-Simple executable was available. Neither the
  stale Rust seed result nor source inspection is reported as pure-Simple
  conformance.
