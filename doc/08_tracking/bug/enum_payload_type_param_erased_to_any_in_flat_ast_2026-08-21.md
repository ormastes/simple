# Enum type params dropped and payload `T` erased to `Any` by the flat AST

**Date:** 2026-08-21
**Status:** OPEN
**Severity:** Medium (blocks generic-enum template metadata in SMF; no runtime effect today)
**Found while:** delivering the "populate" follow-on of
`smf_enum_def_serializes_variant_names_only_2026-08-21.md`
(`src/compiler/40.mono/monomorphize/hir_bridge.spl`).

## Symptom

For the source

```
enum Opt<T>:
    Some(T)
    Nothing
```

the real pipeline (`parse_full_frontend` -> `HirLowering.lower_module`) yields a
`HirEnum` with

- `type_params.len() == 0` — the `<T>` list is gone, and
- `variants[0].kind == Tuple([HirType(kind: Any)])` — the payload `T` is erased.

So `enum_def_from_hir` produces `generic_params: []`, `is_generic_template: false`,
`variant_payload_type_names: ["any"]`, and the template can never be specialized
(`_specialize_enum_def` has no param name to substitute).

## Root cause (two halves, both in the flat AST enum record)

1. `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl:268` parses
   `val type_params = parse_type_params()` but
   `decl_enum_def(name, variant_names, variant_discriminants, variant_payload_types_flat,
   variant_payload_counts, variant_payload_field_names_flat, span_id)`
   (`src/compiler/10.frontend/core/_Ast/decl_nodes.spl:655`) has **no type_params slot**,
   so the list is dropped before the bridge; `ParserEnum.type_params` is always empty.
2. Payload types travel as an `i64` type TAG per slot (`variant_payload_types_flat`,
   pushed at `enum_module_body.spl:437`). A type parameter has no tag, so the bridge
   hands HIR a bare name, and `lower_type`'s seed-parity rule
   (`src/compiler/20.hir/hir_lowering/types.spl`, "Bare single uppercase letter -> Any")
   erases it. Struct fields go through `decl_field_types` and do keep their names, which
   is why `struct Box<T>` templates work and enums do not.

## Pinned by (KNOWN RED, left failing on purpose per `.claude/rules/testing.md`)

`test/01_unit/compiler/linker/smf_enum_def_source_round_trip_spec.spl`
(mirrored at `test/unit/...`):

- `marks a parameterised enum as a template with its params (KNOWN RED: ...)` —
  expects `generic_params == ["T"]`, gets `[]`.
- `names the payload type param T (KNOWN RED: ...)` — expects
  `variant_payload_type_names == ["T"]`, gets `["any"]`.

The other 9 examples in that file are green and prove the rest of the population path
(arity, kinds, positional/named field names, discriminants, decorators, `complete:`),
plus `_specialize_enum_def` substitution on a template that carries `T` by name.

## Unblock condition

Add an enum `type_params` slot to the flat AST record (`decl_enum_def` + the bridge in
`_FlatAstBridge/convert_nodes.spl`) and carry payload type params by name (the way
struct fields do). When `HirEnum.type_params` is populated and
`HirVariantKind.Tuple([TypeParam("T")])` (or `Named(sym_T)`) arrives at
`enum_def_from_hir`, both RED examples go green with no change to the bridge.

Those files are under active edit by other lanes (see `git status`), which is why this
is filed rather than fixed here.
