# Native method cleanup global misresolution

**Status: Resolved 2026-07-16** — owner dispatch verified empirically at
c8f4b62261a under the dual-backend protocol (seed-interpreter oracle vs
`native-build --entry`); regression case `method_owner_dispatch` added to
`scripts/check/check-native-seed-parity.shs`.

Strict `bootstrap_main` linking showed calls authored as `compiled.cleanup()` in a module
with a conflicting wildcard-imported `backend_types.CompiledModule` resolving to
`interp.execution.tiered_jit.TieredJitManager.cleanup` instead of `codegen.CompiledModule.cleanup`.
The wrong binding retained interpreter-only `rt_jit_cleanup` in a hosted native build.

Evidence: `/tmp/.tmpy70sui/mod_308.o` defines `CompilerBackendImpl` and relocates its
process path to `TieredJitManager_dot_cleanup`, while the receiver is returned by
`CodegenPipeline.compile_module` as `codegen.CompiledModule`.

The immediate collision is removed by the owner-specific method name
`release_codegen_module` across all eight callers. A compiler regression should later
prove explicit receiver type/import resolution wins when unrelated types expose the same
method name.

## Pure-Simple root fix (2026-07-15)

HIR method declarations now retain `<module>.<Owner>::method` identity, the resolution pass uses the
module's populated symbol table, and MIR emits the matching owner-qualified symbol. The
focused regression lowers two unrelated `cleanup` owners and proves the codegen receiver
selects its own method. Bootstrap closure lowering now retains impls/method bodies and
uses the same owner-qualified accumulator names. Explicit/glob imports register the
selected type's impl methods under the defining module, including concrete-owner copies
of trait defaults. `release_codegen_module` remains only as Rust-seed bootstrap
compatibility until a fresh self-hosted stage proves the old seed ambiguity is absent.

The focused owner-dispatch regression is present but was not executed in the
2026-07-15 source-only audit.

## Regression evidence (2026-07-16, tip c8f4b62261a)

Two unrelated owners exposing the same `cleanup` name; each receiver must bind
its OWN owner's method:

```simple
struct JitMgr:      # cleanup() -> 222
struct CompiledMod: # cleanup() -> 111 + self.name
fn make_mod(n) -> CompiledMod: ...
fn main():
    print(make_mod(1).cleanup())   # must be 112, never 222
    print(JitMgr(id: 7).cleanup()) # must be 222
```

- Oracle (`env -u SIMPLE_BOOTSTRAP bin/simple run p.spl`): `112`, `222` (rc 0).
- Native (`env -u SIMPLE_BOOTSTRAP bin/simple native-build --entry p.spl -o out
  --clean` + run): `112`, `222` (rc 0; native `print` emits no trailing
  newline). Identical after newline normalization — no misresolution.
- Targeted gate at the same tip: `NATIVE_SMOKE_CASES=enum_match
  scripts/check/native-smoke-matrix.shs` ends
  `total=1 pass=1 fail=0 ... codegen_fallback_hits=0`.
- Parity regression: `method_owner_dispatch` in
  `scripts/check/check-native-seed-parity.shs` (PARITY mode).

Verification note: an earlier attempt against 8ac259873334 was blocked by the
campaign-wide native-build wall (ca1e18c1744's rt_dict_*/rt_tuple_* extern
migration vs the deployed 2026-07-11 seed, since reverted on main). A separate,
still-open defect observed during verification: a method returning `text`
natively prints a raw handle integer (see
`native_method_text_return_prints_handle_2026-07-16.md`) — a text-decode gap on
the method-result path, not a dispatch misresolution (the same program with
`i64` returns has full parity).
