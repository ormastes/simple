# Stage 2 SEGV in HIR `lower_trait`: private dict alias field dispatches to `AdaptiveMap.contains_key`

- **Date:** 2026-10-24
- **Status:** source workaround landed (this record); seed root cause open.
- **Binary:** stage 2, x86_64-pc-windows-gnu, built by the Rust seed at `9feac254cae`
  (`.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-gnu/simple.exe.manual-wa-fltused`).
- **Blocks:** stage 3. Stage 2 cannot compile any module that declares a trait.

## Symptom

`native-build` of the compiler closure crashes with exit 139 in the HIR phase. In
the reported run it died at module 66 of 134 (`lib.common.encoding.external_text`).

## Smallest repro

```
# zz_repro.spl
trait T:
    fn f() -> i64
```

Running `SIMPLE_SCV_INVENTORY_COLD_INIT=1 simple.exe native-build zz_repro.spl -o o.exe`
exits 139. A file with only a plain `fn` reaches native_compile without crashing.

## Evidence (lldb)

```
Access violation reading location 0x00000010
frame #0 AdaptiveMap.promote_if_useful + 191   movq 0x10(%rax),%rax  ; rax = self.profile = 0
frame #1 AdaptiveMap.contains_key + 43
frame #2 HirLowering.lower_trait + 2031        ; self.lowered_traits.contains_key(name)
frame #3 HirLowering.lower_module ...
```

`lowered_traits` is a dict, but it is declared as
`lowered_traits: HirTraitsByName` with `type HirTraitsByName = {text: HirTrait}`.
That alias is private to `hir_lowering/types.spl`. The compiled call treats the
dict handle as an `AdaptiveMap`. It reads field 0 (`profile`), which is null, and
dereferences it.

In the same compiled function `HirLowering.with_trait_candidate_conforms`:

- `self.lowered_traits.contains_key` (alias-typed, `trait_impl_lowering.spl:195`)
  calls `AdaptiveMap.contains_key`.
- `self.imported_traits.contains_key` (typed directly as `{text: ParserTrait}`, line
  199) calls `rt_contains`.

So the difference is the alias. Nothing in the dict itself or the runtime causes it.

## Root cause (seed, not yet fixed)

The importing module (`_Items/trait_impl_lowering.spl`) does not see the private
alias. The seed resolves the imported class's field type there, and it becomes
`Any`. `receiver_is_dict` (`compiler_rust/compiler/src/mir/lower/lowering_expr_method.rs:53`)
then returns false. The call falls through to name-based method recovery, which
binds an unrelated user method of the same name (`AdaptiveMap.contains_key`). The
comment at `lowering_expr_method.rs:550-552` already describes this hazard.

Seed fix direction: resolve an imported struct or class's field types in the
declaring module's alias scope. Alternatively, never bind a nominal method by bare
name when the receiver type is `Any`. Either one needs a seed rebuild to verify.

## The `invalid array handle` line

`[simple-runtime][error] rejected invalid array handle ... (value_bits=0x0100000000000000)`
is printed for any file with a `struct` or `trait` declaration. A file with only an
`fn` does not print it. It is reported once per process and does not by itself
crash. It was not investigated further here.

## Workaround

`hir_lowering/types.spl`: `lowered_traits` and its initializer now spell
`{text: HirTrait}` directly. The `HirTraitsByName` alias is removed. This matches
the other `{text: ...}` fields of `HirLowering`, which dispatch correctly.
Verification needs a stage 2 rebuilt from this tree. Re-run the repro above and
expect no SEGV in `lower_trait`.

Other dict-alias-typed fields that may have the same exposure (not observed
crashing): `FunctionBoundsMap`, `FunctionTypeParametersMap`, `MutableSymbolsMap`,
`SubstitutionMap`, `TypeEnvironment` (30.types), `HirTypeBindings`
(hir_definitions), `SymbolNameMap` (70.backend), `ValueCaptureMap` (00.common).
