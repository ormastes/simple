# Flat AST loses export-from provenance and type aliases

Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 01).

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

## 2026-08-17 content triage (w0001 ZCLAIMED, source-inspection only)

Verdict: SPLIT — type-alias half ALREADY-FIXED, export-from half STILL-OPEN

Type-alias half is closed at
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:168-172`:

```spl
    # TAL1 (bug type_alias_declarations_discarded_at_parse_2026-07-29): the
    # arena now captures `type X = Y` (decl_type_alias, tag 17). Thread it
    # through into module.type_aliases instead of the old hardcoded `{}` --
    var type_aliases: Dict<text, ParserTypeAlias> = {}
```

Export-from half remains: `grep -n "export_from|export .* from|reexport"` on the
same file returns NOTHING, so the provider module of `export X from M` is still
not recorded. Keep this row OPEN for the export-from half only.
Owner path: src/compiler/10.frontend/**.
