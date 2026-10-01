# `val generic = ...` is rejected: contextual keyword has no `=` lookahead

- Date: 2026-09-24
- Status: open
- Found by: re-root of codex/spipe-local-knowledge-setup (spec
  `test/01_unit/os/qemu_lane_projection_v1_spec.spl`, worked around by renaming
  the binding to `generic_result`).

## Repro

```simple
val generic = 1
```

Both parsers fail with `Unexpected token: expected identifier, found Assign`.

## Cause

`val generic T limits [...]` (type-constraint declaration) is parsed by treating
`generic` after `val` as a keyword without looking at the next token:

- seed: `src/compiler_rust/parser/src/stmt_parsing/var_decl.rs:64`
- self-hosted: `src/compiler/10.frontend/core/parser_decls_use.spl:452`

`val generic =` / `val generic:` are unambiguous (the constraint form always has
an identifier next), so one token of lookahead fixes it in both parsers.
