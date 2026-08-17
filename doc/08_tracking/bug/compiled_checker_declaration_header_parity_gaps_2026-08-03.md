# Compiled checker declaration/header parser parity gaps

- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- Claimed by: Codex Stage 4 declaration batch
- Date: 2026-08-03
- Base revision: `5e7c57e9c89a8f59df22830991327438ba37fc93`
- Workspace: `/tmp/simple-stage4-decl-batch.k7lsCY`
- Primary owner: `src/compiler/10.frontend/core/_ParserDecls/fn_struct_decls.spl`

## Inventory scope

This claim owns only the following routes from the frozen Stage 4 checker-owned
inventory. Other parser routes remain assigned to their existing owners.

- `pure_parser_metadata_block_gap`: 24 files
- `pure_parser_declaration_boundary_gap`: 10 files
- `pure_parser_declaration_newline_gap`: 9 files
- `pure_parser_class_member_gap`: 5 files

The frozen claimed manifest is
`build/mini_builds/stage4-decl-batch/claimed.tsv` in the isolated workspace.
The claim does not include `parser_expr.spl`, `parser_stmts.spl`, general type
parsing in `parser.spl`, or `src/app/check`.

## Exact pre-fix evidence

The compiled checker at
`/tmp/simple-stage4-b1df.WmYLW6/build/mini_builds/current-checker-cycle4/simple-check`
rejects representative production files as follows:

- metadata assignment: expected `:`, got `=`
- declaration following a completed declaration: expected `:`, got `fn`
- newline-style function/class header: expected `:`, got newline
- class member after a completed member: expected `:`, got `pub`
- generic function with a `where` clause: unexpected `:` in the constraint

## Resolution evidence

The shared declaration parser now:

- recognizes `arch`, `config`, and `metadata` blocks using encoding-safe token
  lookahead and balanced token consumption;
- distinguishes bodyless declarations from colonless indented bodies without
  consuming the following declaration;
- defaults bare class fields to `any`;
- consumes balanced where constraints without mistaking `T: Bound` for the
  body colon.

A fresh pure-Simple-compiled checker rebuilt 47 modules with no fallback. The
first 48-path retry passed 23 and failed 25. After the Unicode metadata root fix,
the failed-only retry passed 20 more, for 43/48 cumulative green paths. All 43
paths owned by this declaration/domain batch pass.

The five remaining rows are rerouted, not hidden:

- three `pass:` named-argument failures belong to expression/primary parsing;
- `phase1-image-lines.spl` now passes its colonless function header and exposes
  an `img{...}` struct-literal expression failure;
- `phase1-math-blocks.spl` now passes its colonless function header and exposes
  a `^` expression failure.

The focused native regression executable reports 7 examples and 0 failures,
covering exact, adjacent, malformed, and recovery cases. Durable build and retry
evidence is under `build/mini_builds/stage4-decl-batch/` in the isolated
workspace.
