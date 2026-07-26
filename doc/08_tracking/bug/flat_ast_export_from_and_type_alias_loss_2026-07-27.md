# Flat AST loses export-from provenance and type aliases

## Observed

During the full Stage 4 CLI closure, `export X from module` retains only `X`;
the provider module is absent from `Module.exports`. Flat parsing also does not
dispatch `type Name = Target`, and module assembly hardcodes
`type_aliases: {}`.

This caused unresolved EasyFix facade types and `T32BridgeResult`.

## Current compatibility repair

Affected build-critical sources use supported `export use module.{...}` and
import alias syntax. This preserves their existing public names and targets.

## Required compiler fix

- Represent export provider modules in flat declarations and `Module.exports`.
- Add a flat type-alias declaration, parser dispatch, and module assembly.
- Resolve alias RHS ownership for type lowering and static member lookup.
- Add parser/HIR tests for generic and non-generic aliases and export-from.
