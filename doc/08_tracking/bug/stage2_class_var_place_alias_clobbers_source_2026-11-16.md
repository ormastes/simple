# Stage 2: class-typed `var t = a` aliases `a`'s local, `t = b` rebinds `a` (2026-11-16)

Status: fixed in MIR source on `work/class-var-place-alias-20261116`. It takes
effect natively only after Stage 2 is rebuilt. Stage 3 source has a tagged
workaround at the one site that blocked the build.

## Symptom (Stage 3 r16 self-build)

HIR lowering failed in every module that imports `LlvmTypeMapper`. The first
was `driver_bootstrap.spl`, and 303 modules cascaded from it:

    stale surface index [impls]: module=compiler.backend.common.type_mapper
    surface_key=1 802 4 owner=LlvmTypeMapper position=3 live_len=0

The smallest repro is a 4-line entry, `use compiler.backend.llvm_type_mapper.LlvmTypeMapper`.
`simple-r16 compile` of it fails the same way (228-file closure, 4m11s, 1.8 GB RSS).

## Root cause

In `register_imported_type_methods_inner`
(`src/compiler/20.hir/hir_lowering/_Items/module_reexport_materialization.spl`,
s3wa2 tip `03b340fbbfe`, lines 1786/1802), the code does:

    var trait_module = imported_mod                          # :1786
    ...
    trait_module = self.module_surfaces.surfaces[idx]        # :1802

`LlvmTypeMapper` (`llvm_type_mapper.spl`, 4 impl rows) implements
`TypeMapper`. That trait lives in `common.type_mapper`, which has 0 impls. The
reassignment overwrote `imported_mod` itself. The next impl row (position 3)
then read `type_mapper`'s empty impls. The surface key had been computed before
the clobber, so it still said `4`. The memo was not stale, and transient
reclamation was not involved.

The miscompile is in the MIR early-Let arm
(`src/compiler/50.mir/mir_lowering_stmts.spl` ~1839, the same on release/1.0.0
and on the integ2 pin `8453e87c8767`):

    elif (bf_sym != None or struct_sym != None) and not initializer_is_short:
        self.bind_local(symbol_value_id, init_local)

`maybe_copy_struct_value` returns nil for a class, which keeps reference
semantics. So a class place read fell through to an alias of the SOURCE local.
Sharing the object is correct; sharing the binding slot is not. The dead twin
arm (~2198) had the same shape.

Native fixture `test/fixtures/compiler/native_class_var_place_alias/main.spl`,
built by the integ2 Stage 2 (typed path, llvm):

    param a=tm t=tm      (expected a=llvm)
    typed a=tm t=tm      (annotation does not help)
    local a=tm t=tm
    loop a=llvm,tm,tm len=4   (expected llvm,llvm,llvm len=12)
    reverse a=tm t=tm    (val t = a; a = b also moves t)
    struct a=1 t=9       (structs are copied; unaffected)

An `if`-expression initializer does not alias, and neither do `i64`, `text`, or struct values.

## Fix

Alias only a fresh aggregate (`not mir_expr_kind_is_place(...)`). A place read
gets a new local and an `emit_copy` of the handle. The record
(`struct_value_syms`) and bitfield owner are carried onto it. Spec:
`test/01_unit/compiler/mir/class_var_place_alias_spec.spl` (red 2/4, green 4/4
on the seed).

## Workaround (Stage 3 source)

`@workaround bug=stage2_class_var_place_alias_clobbers_source_2026-11-16` in
`module_reexport_materialization.spl`. It selects the trait owner by index and
binds it once with `val`.

An awk census of `var X = Y` with a class-typed `Y` that is later reassigned
found no other site in the HIR/MIR/driver path. Library hits (`ByteBuffer`
writers, `Engine2D`, ...) are outside the Stage 3 closure, or they never read
the source again.

## Note on earlier guards

STALESURF (key includes `impls.len()`, 2026-11-08) and IMPLIDX-GUARD were added
for the same `live_len 0/1` symptom, assuming the memo was stale. They are
harmless, but they did not address this cause.
