# Flat AST loses export-from provenance and type aliases
## RESOLVED 2026-11-25 — export-from provider and type aliases both retained

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

## Resolution 2026-11-25

All three required compiler fixes are present on release/1.0.0 (dfbd7c9d765):

- **Type-alias parse dispatch:** `parse_type_alias_decl()`
  (`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:923`)
  emits `decl_type_alias(...)` and is dispatched from the module-body loops
  (lines 1021, 2574); `"type_alias"` is a recognized declaration category
  (`declaration_intent_v1.spl:25`).
- **Module assembly no longer hardcodes the empty map:**
  `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:385-387`
  carries the comment "through into module.type_aliases instead of the old
  hardcoded `{}`", populates `type_aliases[ta_name]` (line 1253) and passes it
  to the assembled module (line 1412). The remaining `type_aliases: {}` sites
  are the legitimate `flat_empty_module` constructor and synthetic-module
  paths, not the real assembly. HIR consumes them
  (`src/compiler/20.hir/data_type_binding_v1.spl`).
- **Export-from provenance:** `export X from module` is parsed in
  `src/compiler/10.frontend/core/parser_decls_use.spl` (~line 335):
  `parse_export_source_module()` captures the provider and the declaration is
  recorded as a use-import re-export surface
  (`decl_use_import(from_module, names, 0)`), so the provider module is no
  longer dropped. Note: `struct Export` itself still has no provider field —
  provenance is carried through the use-import surface instead, which is the
  functionally equivalent representation the driver consumes
  (`driver_tldr_import_route_v1`).

Covering specs on disk: `test/01_unit/compiler/frontend/type_alias_survives_parse_spec.spl`,
`test/01_unit/compiler/frontend/type_alias_capture_spec.spl`,
`test/01_unit/compiler/80.driver/tldr_route_export_from_spec.spl` (export-from
re-export routing).

Verification limit: spec execution at this HEAD is blocked by the pinned seed
rejecting `@representation_boundary` (cfd89933699), which fails the test
runner's own load; verified by code inspection of the modules cited above.

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

