# Result unwrap loses receiver type during native method resolution
## Closed — verified fixed 2026-07-16 (see Verification section); header corrected 2026-11-25

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Correction 2026-11-25 (p2w4-ag lane):** the 2026-09-16 banner above was
misleading — the body's own `## Verification (2026-07-16)` section already
records a full oracle + native verification of the fix at origin tip
8932fcb3a148. Re-confirmed by source inspection on release/1.0.0
(63e791180d3): MIR retains each callable's declared return type through
erased locals via the bootstrap call-return-type registry
(`src/compiler/50.mir/mir_data.spl:2424-2442`, consulted by
`bootstrap_resolved_call_return_type` before the i64 fallback), which is the
mechanism the Resolution section describes. Native re-execution is
env-blocked on this host (pinned seed); status marked resolved on the
existing 2026-07-16 runtime evidence plus the source confirmation.

## Symptom

An unannotated local produced by `Result<T, E>.unwrap()` loses `T` before native
method resolution. If two types define the same method, codegen rejects the call
as ambiguous even though the `Result` payload type is concrete.

The strict Stage-4 build reproduced this in `aot_compile_to_bytes`:

```simple
val module = compiled.unwrap()
module.emit_object(tmp_path)
```

`compiled` is `Result<CompiledModule, CodegenError>`, but resolution considered
both `CompiledModule.emit_object` and `CraneliftCodegenState.emit_object`. Raw and
mangled index aliases inflated the diagnostic from two semantic methods to four
names.

## Bounded workaround

The receiver uses the existing typed-local pattern:

```simple
val module: CompiledModule = compiled.unwrap()
```

This is not a method-name exception. The next strict build compiled the body and
reached the linker.

## Source resolution (2026-07-16)

MIR now retains a callable's declared HIR return type beside its erased local,
copies that provenance through unannotated bindings, and uses it to recover the
`Result<T, E>` payload at `unwrap()`. Named struct payloads keep the one-word enum
ABI and register the existing `struct_value_syms` owner on the merged unwrap
local. No new ABI or parallel method resolver was added.

Method lookup already uses owner-qualified `struct_method_syms`, so the former
raw/mangled alias ambiguity is superseded and needs no second deduplication path.
The focused MIR regression defines colliding `A.emit_object` and
`B.emit_object`, proves `val pending = make(); val value = pending.unwrap()`
selects only `A`, and keeps an untyped receiver fail-closed.

Source implementation is complete; runtime execution remains pending under the
current no-build/no-compiler-command constraint. Keep the explicit annotation
workaround in bootstrap-critical callers until that execution proof exists.

Tracked by TODO 558.

## Verification (2026-07-16)

Verified fixed at origin tip 8932fcb3a148: `probe03_result_unwrap_erasure_a.spl` (two structs `A`/`B` each defining `emit_object`, `make() -> Result<A, text>` returns `Ok(A(x:1))`, unannotated `val module = compiled.unwrap(); module.emit_object()`). Oracle: `bin/simple run` → `111`. Native: `native-build --entry --clean` exit 0, binary built, run → `111`. No ambiguous-method-call error; MIR retains declared return type through unannotated bindings and correctly disambiguates.

