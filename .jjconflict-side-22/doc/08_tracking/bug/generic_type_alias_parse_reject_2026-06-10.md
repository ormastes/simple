# Generic Type Alias `type X<T> = ...` Rejected by Parser

Date: 2026-06-10

Status: resolved (2026-06-14)

## Resolution (2026-06-14)

Fixed in the Rust seed parser: `parse_type_alias`
(`src/compiler_rust/parser/src/stmt_parsing/var_decl.rs`) now calls
`parse_generic_params_as_strings()` between the alias name and `=`, so
`type Alias<T> = Result<T, text>` parses (params consumed; substitution at
resolution is unchanged). Verified: `bin/simple check` passes on a generic-alias
repro that previously raised E0002; parser specs (associated_types, module_alias,
parser_declarations) still green. Requires seed rebuild to deploy.

## Summary

`type LowerResult<T> = Result<T, text>` fails with E0002 unexpected token at
the `<`. Non-generic aliases (`type TypeId = HirType`) parse fine. Found in
`src/compiler/30.types/type_check/mod.spl` while replacing legacy
`use hir (LowerResult)` imports during the E0410 export sweep.

## Repro

```spl
type Alias<T> = Result<T, text>   # E0002: unexpected token (col of '<')
```

## Workaround

Inline the right-hand side at use sites: `-> Result<(), text>` instead of
`-> LowerResult<()>` (applied in type_check/mod.spl).

## Fix direction

Accept type parameters on alias declarations and substitute at resolution
time, or document the restriction in the syntax reference if intentional.
