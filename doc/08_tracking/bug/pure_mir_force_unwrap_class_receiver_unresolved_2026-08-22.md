# Pure MIR: `m!.method()` on an `Option<class>` lowers to the unresolved-method placeholder

**Date:** 2026-08-22
**Area:** pure-Simple MIR lowering — `src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`
(`Unwrap` arm of `lower_expr`, ~:3930)
**Status:** FIXED — pinned by
`test/01_unit/compiler/mir/force_unwrap_class_method_provenance_spec.spl`
(2 cases; both FAIL pre-fix, PASS post-fix) and a perf-gate row.
**Found by:** the pure-lane audit of seed fix `20416a1bda7` (JIT optional-class
unwrap emitted an enum payload read). The seed's defect shape is ABSENT on the
pure path: `expr!` lowers as `rt_is_some` + `rt_unwrap_or_self` +
`enum_payload_value`, and `enum_payload_value` reinterprets only U64/F64/F32
and passes class/struct pointers through (`switch_operators_calls.spl:395-420`),
so value class is runtime-tag driven. Pure-compiled native probes executed:
`val u = m!; u.n` → 42, `match Box.Leaf(cell): cell.get_n()` → 9.

## What IS wrong

`m!.get_n()` and `val u: Cell = m!; u.get_n()` hit
`[mir-lower] WARNING: unresolved method call 'get_n' lowered to const-0
placeholder` and the pure-compiled native binary prints `via_method=0`.
The `!` arm propagates `struct_value_syms` only when the BASE local already
has an entry (`expr_dispatch.spl:3939-3940`). An Option handle is a boxed
payload, never a construction site, so it has none. The `.unwrap()` arm got
the recovery-from-inner-Named-type fix for exactly this on 2026-08-09
(`method_calls_literals.spl:693-712`,
`native_option_unwrap_receiver_unresolved_2026-08-09`); the `!` arm never did.

## Fix

Mirror it: when the base has no owner entry and `uw_inner_type` is
`HirTypeKind.Named(sym, _)`, set `struct_value_syms[result_local_uw.id]` to the
symbol's name. Pure-compiled probe now prints `unwrap_class n=42 via_method=42`
(`bin/simple run src/app/cli/bootstrap_main.spl compile build/probe_c6/main.spl
--format=smf`, Cranelift object linked against `libsimple_runtime.a`).

## Related audit result (class 3, same lane) — already correct

The self-hosted HIR symbol table is per-module: `begin_module` calls
`SymbolTable.reset_module()` (`20.hir/hir_types.spl:262-282`) even though one
`HirLowering` is reused across the closure. Colliding imported composites are
re-registered under `module::Name` (`_Items/module_import_registration.spl:164-180`)
and the bare-name fallback fires only for a unique owner (`:451-453`). MIR keeps
one bare-name `struct_field_order` but warns and reads fields through
module-qualified keys (`_MirLowering/module_lowering.spl:820-851`). Executed
2-module probe (`a.Item{handle,tag}` vs `b.Item{alive,count,label}`) printed
`a.handle=41 b.count=7 sum=48` natively. No interpreter-fallback blast radius
exists on this path. Residual, not fixed: a same-scope duplicate declaration in
ONE module silently returns the first id (`hir_types.spl:333`) with no diagnostic.
