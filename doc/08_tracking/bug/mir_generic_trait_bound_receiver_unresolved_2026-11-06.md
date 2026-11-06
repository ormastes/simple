# MIR "unresolved method call" on a trait-bounded erased generic receiver (2026-11-06)

**Status:** fix-implemented-verification-pending

## Symptom
Bootstrap run 10 (`--full-bootstrap --stop-after-stage2 --backend=cranelift`,
aarch64) failed in Stage 2 compiler tests, row `compiler_cli_build`
(`build/bootstrap-opus-10/stage2-compiler-tests/aarch64-unknown-linux-gnu/verification/logs/compiler_cli_build.log:89052-89098`):

    [mir-lower] WARNING: unresolved method call 'read_tldr' is a FATAL lowering error ...
      module=compiler.driver.cache.reader.tldr_table_fill_v1 at=.../tldr_table_fill_v1.spl:8:16
      receiver_has_type=false receiver_type_kind=-1
    [ERROR] [mir-module-failure] module=compiler.driver.cache.reader.tldr_table_fill_v1 fatal_count=3
      first=unresolved method call: read_tldr route=runtime-fallback key=::read_tldr owner=

Same failure in `compiler.driver.driver_build.file_fiber_v1` (`read_tldr`,
`update_tldr`, and the DEFAULT trait method `update_tldr_async`). Introduced
by b4d003bb758 (2026-10-30), which added `fn _tldr_read_or_update<R: SourceReader>(reader: R, ...)`.

## Root cause
Monomorphization is deleted: a generic body is lowered once, and a type
parameter lowers to an erased tagged `i64` word. `lower_method_call`
(`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2338`) has
two trait routes: the native trait-object ABI (`native_trait_owner_for_kind`,
`_MirLowering/native_trait_registration.spl:150`) and whole-closure
devirtualization (`trait_receiver_identity`,
`_MirLowering/provider_metadata.spl:1017`). Both only recognise a receiver
whose type is `Named(trait)`/`DynTrait`/`Optional(trait)`. A receiver typed
`TypeParam("R", [Named(SourceReader)])` matched neither, so the call fell to
the const-0 + rt_panic placeholder. Teaching the dispatch predicate about
`TypeParam` alone would be wrong: the erased word is not an object (it carries
no vtable and stage2 objects have no runtime type identity), so the ABI has to
change at the generic's boundary, where the caller still knows the concrete type.

## Fix
`native_bounded_param_types` (`_MirLowering/native_trait_registration.spl`):
a free function's type parameter whose ONLY bound is an object-safe trait, and
which the signature uses ONLY as the direct type of parameters, takes that
trait's native object ABI -- `fn f<R: Tr>(r: R)` lowers exactly like
`fn f(r: Tr)`. It is a pure function of the declared signature, applied on
both sides:
- callee: `with_native_bounded_params` (`_MirLowering/function_lowering.spl`,
  from `lower_function`), non-method functions whose SYMBOL carries a declared
  type (HIR types a generic symbol only when it declares a return type);
- callers: `resolved_call_hir_param_types` (`_MirLoweringExpr/expr_dispatch.spl`,
  `SymbolKind.Function`), which reads that same symbol type. The bootstrap
  name registry never holds a `TypeParam` (`hir_type_metadata_symbol_free`).
- body check (`native_bounded_param_escape`): the object may only be a method
  receiver or a positional argument to a native-trait parameter slot; any
  other use is a compile error, never a two-word value in a one-word slot.
- UFCS `x.f()` -> `f(x)` converts a native-trait first parameter only when the
  free function itself stays the callee.

A bound type parameter that is also returned, nested (`[R]`, `R?`, ...), or in a
type the walk does not model keeps the erased word (fail closed).

## Evidence (aarch64, 2026-11-06)
- Unit, red -> green: `test/01_unit/compiler/mir/generic_trait_bound_receiver_spec.spl`
  (Rust seed, in-process HIR+MIR lowering): 3/9 on the unfixed tree (passing:
  the two negative controls and a pass-through compared with the broken
  baseline), 12/12 on the final tree (3 cases added after review).
- Regression: 81 MIR/trait/generic/driver specs, base `origin/release/1.0.0`
  vs fix, one at a time under `MemoryMax=24G`: identical per-file verdicts and
  pass/fail counts (44 green, 37 already red on base).
- Module (the bootstrap `module_compile` row shape, `<stage2> native-build
  <module> --emit-object --backend=cranelift`, `SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1`
  because the 24 GiB cgroup leaves the per-file pool < 2 workers):
  run-10 stage2 -> `unresolved method call` read_tldr x2 + update_tldr in
  `compiler.driver.cache.reader.tldr_table_fill_v1`; stage2 rebuilt from this fix
  (480622a793b) -> `[mir] 285/285`, 0 unresolved, 0 MIR module failures.
  That run then stopped in the cranelift backend on an UNRELATED pre-existing
  defect: `src/compiler/10.frontend/core/parser_cli.spl:226` passes an `f64`
  (`fval.to_float()`) to `expr_float_lit(value: text, ...)`
  (E-BACKEND-CRANELIFT-CALL-ABI). Not addressed here.
- A full Stage 2 rerun (`compiler_cli_build` row) was not run: under a 24 GiB
  cgroup the Stage 2 sanity smoke refuses its worker pool.

## Known limits
- Generic functions without a declared return type (e.g. `mir_visitor_walk_*`)
  and generic METHODS keep the erased word, so a trait call there is still the
  unresolved-method error.
- Callers fail loudly (not silently) for an enum/scalar implementor, an
  argument whose own `R` stayed erased, or a resource-typed argument.
- Cross-module eligibility relies on both modules projecting the bound to the
  same trait symbol and dropping the same builtin bounds; `R: Tr + Eq` where
  one side erases `Eq` and the other does not would disagree.
- `native_trait_bound_admits_object` admits a trait whose layout is not
  registered in the current lowering; only a registered non-object-safe
  layout refuses.

Related, different root cause: `mir_unresolved_method_inferred_receiver_2026-10-24.md`
(receiver type lost by inference, not a bounded type parameter).
