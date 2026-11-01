# Erased generic body ICE: invalid HirType kind carrier after MIR prescan transient scopes (2026-11-01)

status: OPEN (P1) — self-hosted stage2 built from release/1.0.0 HEAD cannot
native-build generic library code that the erased-body model now emits

## Symptom

Native-building `test/fixtures/compiler/erased_generics/array_sort_by_native.spl`
(or anything that pulls `lib.nogc_async_mut.array_advanced` into the closure)
with a self-hosted `simple-bootstrap` built from `release/1.0.0` at or after
`8a935437a98` (also at #5732's head `3b94b409c17`) fails in MIR lowering of the
generic template `array_rotate_left<T>(arr: [T], n: i64) -> [T]`:

```
[mir-type-invariant] receipt=2/16 owner=array_rotate_left context=body param_index=-1 caller_disc=-2 callee_disc=-1 invalid_kind_carrier=true
error: ICE[mir_lower] module lib.nogc_async_mut.array_advanced (attributed): worker died inside this module (worker exit status -1073741819)
```

or, on another attempt of the same build, the clean fatal

```
MIR lowering error: E-MIR-TYPE-Transport: invalid HirType kind carrier observed at MIR boundary owner=array_rotate_left context=body param_index=-1 caller_disc=-2 callee_disc=-1
```

A `HirType` reached the MIR boundary with a garbage `kind` discriminant
(`caller_disc=-2`): the carrier was freed and then read.

## Differential (Windows 11, llvm-mingw UCRT, Rust seed built from the same tree)

Four stage2 binaries were built with the same seed and used to native-build the
same fixture with a fresh HIR cache (`HOME`/`XDG_CACHE_HOME` redirected):

| stage2 built from | sources compiled | result |
|---|---|---|
| `2c7305bbbbb` (= release@`7c7444b8682` + erased-body merge) | release@`7c7444b8682` + erased-body | PASS (`PASS production array_sort_by three record layouts ordering and permutation`) |
| `2c7305bbbbb` | #5732 head `3b94b409c17` | PASS |
| `84e748fab7c` (= release@`8a935437a98` + erased-body merge) | release@`7c7444b8682` + erased-body | ICE in `lib.nogc_async_mut.array` |
| `84e748fab7c` | `3b94b409c17` | ICE in `lib.nogc_async_mut.array_advanced` |
| `3b94b409c17` (#5732, merged) | `3b94b409c17` | ICE / E-MIR-TYPE-Transport (3 of 3 attempts) |

So the compiler, not the library source, is the variable. The only
`src/compiler` commit between `7c7444b8682` and `8a935437a98` is
`5781b6e3f10` ("compiler: bound MIR setup transient scopes", PR #5709), which
wraps `prescan_module_struct_names`, `register_module_enum_inventory_v1` and
`register_module_composite_inventory_v1` in `transient_array_scope_begin_v1`
/ `_driver_mir_inventory_scope_end` (promote roots, then
`transient_array_scope_end_v1`). Before the erased-body landing (#5732) MIR
never lowered a generic template body, so the freed carriers were never read;
now every template body is lowered once and the first `[T]`-typed body with a
registry entry produced inside a prescan scope trips the invariant.

Other fixtures in the same family (`contextual_callback_native`,
`return_only_optional_tuple_native`, `runtime_generic_typed_key_native`,
`runtime_generic_extern_abi_native`) and
`test/fixtures/jit_differential/generic_erased_body_boundary.spl` build and
run correctly on the `3b94b409c17` stage2, so the leak is specific to what
`lib.nogc_async_mut.array_advanced` / `array_rotate_left` records during the
prescan.

Ruled out: adding the four `MirLowering` fields missing from
`promote_transient_owner` (`erased_callback_record_bindings`,
`runtime_value_extern_abis`, `rti`, `rti_last_error`) to the root list does
not change the outcome (stage2 rebuilt, fixture re-run: identical fatal).

## Reproduce

```
SEED=src/compiler_rust/target/x86_64-pc-windows-gnullvm/bootstrap/simple.exe   # cargo --profile bootstrap -p simple-driver
SIMPLE_BOOTSTRAP=1 SIMPLE_NATIVE_BUILD_RUST=1 SIMPLE_PARSE_SHARDING=0 $SEED native-build --backend cranelift \
  --runtime-bundle core-c-bootstrap --source src/compositions/kernel_llvm_cranelift --source src/compiler \
  --source src/app --source src/lib --entry-closure --entry src/app/cli/bootstrap_main.spl \
  --output build/stage2/simple.exe --target x86_64-pc-windows-gnu
SIMPLE_BOOTSTRAP=1 SIMPLE_PARSE_SHARDING=0 build/stage2/simple.exe native-build --entry-closure \
  --runtime-bundle core-c-bootstrap --mode one-binary --backend llvm --target x86_64-pc-windows-gnu \
  --entry test/fixtures/compiler/erased_generics/array_sort_by_native.spl --output build/fx.exe
```

## Fix direction

Find the registry that `prescan_module_struct_names` (or the enum/composite
inventory) fills with `HirType` values for a generic `[T]`-bearing template and
that is not reachable from `promote_transient_owner`'s roots, or that is
promoted by copy rather than by reference; then re-run the differential above
(the `2c7305bbbbb` row is the passing oracle). Do not work around by skipping
template bodies again.

Tracked by: `test/01_unit/compiler/generics/erased_generic_fixture_spec.spl`
("sorts three record layouts through array_sort_by") on the self-hosted binary.
