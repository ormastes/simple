# Actual imported declaration category

Executable source: `test/01_unit/compiler/hir/imported_binding_category_v1_spec.spl`.

Five cases authored, **UNRUN**. Production parser, surface freeze, registration
and symbol owners preserve TypeAlias selection despite a shared Struct ID,
return the category on a warm memo hit, invalidate same-ID rebinding and unbind,
reset category ownership with the module, and distinguish lexical scopes.

These cases do not qualify positive permission grants or source-use route
receipts. The selected category is captured by the actual registration branch,
not reconstructed from the canonical target kind.
