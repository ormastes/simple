# P3 implementation boundaries

- SymbolTable owns qualified class identities and lexical bindings.
- provider_metadata owns relocation and declaration-derived callable names.
- bootstrap_type_registration adapts the flat HIR provider store.
- module_lowering adapts ordinary HirModules and field/return provenance.
- constructor lowering diagnoses unsupported defaults at use sites.
- function and expression lowering consume canonical class/link metadata.

Failure behavior is explicit: a missing declaration symbol, missing class
metadata at construction, or an unsupported used default records a fatal MIR
diagnostic. A provider SymbolId cannot be used as a consumer local fallback.

The field compatibility boundary retains raw layout aliases. External linkage
attributes preserve their existing spelling and export-map handling. No
backend-specific class ABI is introduced; MIR continues to represent the
existing class pointer/aggregate ABI with distinct ownership metadata.

The executable fixture has its own src/identity root so module names remain
stable when checked out under different Windows drives or Unix paths. It
expects checksum 103034443, distinct nested field values 7 and 17, helper-main
value 404, and array push value 73, with process exit zero.
