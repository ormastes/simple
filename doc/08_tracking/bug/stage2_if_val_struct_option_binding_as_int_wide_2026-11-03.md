# Frozen stage2 binds `if val x = <struct-typed Option>` through rt_value_as_int_wide (MIR reads an integer as a HirModule)

- **ID:** stage2_if_val_struct_option_binding_as_int_wide_2026-11-03
- **Priority:** P1 (phase 3: the stage3 hello smoke dies in MIR setup on the first module)
- **Status:** open. Source workaround landed in `src/compiler/80.driver/driver_pipeline_lowering.spl`
  (explicit `!= nil` + annotated `.unwrap()` at the seven struct-typed binding sites); the stage2
  miscompile itself is not fixed.

## Symptom
With the HIR cache off (`SIMPLE_HIR_CACHE=0`, see the HIR-cache note below) the stage3 hello build gets
through HIR and dies at `phase=mir ... current=mir_setup:enum_inventory` with 0xC0000005 in
`MirLowering.register_module_enum_inventory_v1+0x7d` (`movq 0x58(%rdx),%rcx` = `module.enums` of
`modules[0]`), reading `0x395a783cb0`: not a heap address (minidump `veh_79040.dmp`).

## Root cause (OLD object `C:/dev/p3new/aot-26a723...o` = driver_pipeline_lowering, stage2 ef0681fc0e1)
`if val present_enum_hir = enum_inventory_hir:` is lowered as

```
rt_dict_get -> o ; rt_is_some(o) ; rt_unwrap_or_self(o) [result DROPPED] ; x = rt_value_as_int_wide(o)
```

so the bound value is an integer decode of the Some box, which is then pushed into `[HirModule]` and
dereferenced by MIR. The same shape occurs at every struct-typed optional binding of that object
(10 `rt_unwrap_or_self` -> `rt_value_as_int_wide` pairs: `lower_to_mir_with_target_context` x5,
`verify_lowered_mir_v1` x3, `driver_collect_mir_advisories` x2); the identical pairs exist in other
stage2-built objects (e.g. `driver_aot_native_output` group-pair helpers). The source file is unchanged
since the object was built, so a plain recompile reproduces it.

## Workaround
Each site binds through an explicit nil check and an annotated unwrap, which the same object lowers
through `rt_unwrap_or_self` alone (verified on `hir_cached.unwrap()` in `driver_hir_pipeline_lowering`):

```
if enum_inventory_hir != nil:
    val present_enum_hir: HirModule = enum_inventory_hir.unwrap()
```

Link-level interim (not landed): `C:/dev/p3new/s3new/fable_patch_26a723.ps1` rewrites the ten sites in a
copy of the old object (`s3_fable3.exe` passed MIR with it).

## HIR-cache note (separate, not yet root-caused)
With the HIR cache ON, `hir_cache_load_parsed_v1` returned `Some("bootstrap_hello_world")` (the module NAME
string) for the entry module (dump `veh_10416.dmp`: the decoded `HirModule` memory had been freed and
reused by a later string). The phase-3 smokes run with `SIMPLE_HIR_CACHE=0` until that is fixed.

## Removal condition
A stage2 that binds struct-typed optionals through the payload (any seed-built stage2 from release/1.0.0 at
or after this change) makes the `if val` form safe again.
