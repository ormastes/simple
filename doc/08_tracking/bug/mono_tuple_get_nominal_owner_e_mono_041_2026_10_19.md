# Mono cannot prove nominal owner for `_sffi_tuple_get<Expr|Block>` (E-MONO-041)

Date: 2026-10-19
Bug: mono_tuple_get_nominal_owner_e_mono_041_2026_10_19
Database registration: pending (no qualified `simple check-dbs` binary on this host); DB reconciliation pending.
Status: open — tagged workaround active.

## Failure
Windows Phase 3 native build (producer `2e6409b5…98b1f1`, ee3d4 source; target
`release_phase3` a853e7e932a + #3799) aborted in phase 4:

```
[mono] generic_fns=87 call_sites=906 specializations=262 unresolved=3
E-MONO-041: instantiation of `_sffi_tuple_get` has a nominal type with no proven declaration owner in `compiler.hir.hir_lowering._Items.module_callable_types`; not specialized   (x3)
error[E-MONO-033]: monomorphization left 3 generic call site(s) unspecialized
```

Sites: `src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl`
`_sffi_tuple_get<Expr>`, `<Block>`, `<Block?>` in the `ExprKind.If` payload
projection (added by 9cd577dc553 / b1ebad3f119). `Block` reaches the module only
through `use compiler.frontend.parser_types_expr.*`; the same wrapper with other
type arguments in 50.mir / 70.backend specializes fine.

## Workaround
Three non-generic `@always_inline` forwarders (`_if_payload_*_v1`) call the
erased extern `rt_tuple_get<T>` directly — identical to what the generic
`_sffi_tuple_get<T>` wrapper forwards to — so mono has nothing to instantiate.
`recover=a853e7e932aef4a60ddbd2a5aa053505f42373e1` holds the original form.

## Underlying fix (owner: mono)
Make the E-MONO-041 declaration-owner proof resolve type arguments imported via
glob `use …*` (and explicit `{Expr}`), then restore the generic calls and verify
with the affected producer.
