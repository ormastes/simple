# HIR: two distinct enums sharing one short name hard-failed the importing module

- **Date:** 2026-08-21
- **Status:** FIXED
- **Severity:** blocker (Stage 1 self-compilation)

## Symptom

Stage 1 HIR lowering aborted `src/compiler/80.driver/driver.spl`:

```
[hir-fatal] source_idx=1 path=src/compiler/driver/driver.spl error_idx=0
text=HIR lowering error in src/compiler/driver/driver.spl:
enum payload dependency `AdviceForm` conflicts:
`compiler.frontend.core.aop::AdviceForm::enum`
vs `compiler.mdsoc.weaving.advice_form::AdviceForm::enum`
```

`driver.spl` never names `AdviceForm` (`grep` returns 0 hits in all 156 lines);
the error was attributed to an innocent transitive importer.

## Root cause

There are two GENUINELY DISTINCT enums under that short name, neither dead nor a
duplicate of the other:

- `src/compiler/10.frontend/core/aop.spl:33` — `enum AdviceForm`
- `src/compiler/85.mdsoc/weaving/advice_form.spl:4` — `enum AdviceForm`

`HirLowering.materialized_payload_bindings` is keyed on the LOCAL SHORT NAME, so
the second module to be materialized into one lowering context could only ever
lose that slot. Losing it was treated as a defect:
`claim_materialized_payload_binding`
(`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl:234`
and `:279`) called `self.error(...)`, and both call sites
(`module_import_registration.spl:122`, `module_reexport_materialization.spl:300`)
then did a bare `return`. Net effect: the module failed to lower AND the second
enum got no symbol at all.

A short-name collision is not a defect. It only means the unqualified spelling
is taken. The signature-dependency path already knew this —
`materialize_imported_callable_declared_dependency`
(`module_reexport_materialization.spl:363`) registers every declared dependency
under `{module}::{name}` and then `bind_qualified_type`s it, so cross-module type
resolution finds it through the qualified lookup. The enum/payload path had no
such fallback.

## Fix

- `claim_materialized_payload_binding` no longer errors on an identity
  disagreement. It returns `false` with a level-gated advisory
  (`SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1`, `[hir-payload-shortname-taken]`), which
  makes the previously silent-or-fatal path loud without failing the build. The
  non-type-binding contest, a real defect signal, still errors.
- `module_import_registration.spl:122` re-registers the losing enum under
  `{owner_module}::{name}` (one retry, guarded against `local_name ==
  qualified_local` so it cannot recurse) instead of returning empty-handed.
- `module_reexport_materialization.spl:300` does the same for a payload
  dependency, choosing `payload_local_name` from the claim result.

Both paths route through `register_imported_symbol`, which already calls
`bind_qualified_type(owner_module, name)`, so both owners stay reachable.

## Reproduce spec

`test/01_unit/compiler/hir/enum_shortname_collision_two_owners_spec.spl`
(byte-identical mirror at `test/unit/compiler/hir/...`). Two owners each declare
`enum AdviceForm` with different variants; a consumer imports both.

- pre-fix: `outcome=ERROR ... passed=0 failed=2`
- post-fix: `outcome=OK ... passed=2 failed=0`

Neighbours in the same defect class still pass:
`enum_payload_origin_plain_use_spec.spl`,
`imported_composite_field_package_sibling_spec.spl`.
