# Result unwrap loses receiver type during native method resolution

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

## Independent re-verification (2026-08-18)

Re-reproduced from scratch on the interpreter lane before touching anything.
The defect shape does **not** reproduce: `struct A`/`struct B` both defining
`emit_object`, `make() -> Result<A, text>` returning `Ok(A(x: 11))`, and an
UNANNOTATED `val module = compiled.unwrap(); module.emit_object()` prints
`111` (A selected) and the sibling `B(y: 5).emit_object()` prints `205`. No
ambiguous-method-call diagnostic. Payload type `T` survives `unwrap()` into an
unannotated local, so the TODO 558 premise is stale on this lane.

Regression coverage added so this cannot silently regress:

- `test/01_unit/language/result_unwrap_payload_type_preserved_spec.spl` —
  exact defect shape. `Results: 3 total, 3 passed, 0 failed`.
- `test/01_unit/language/unwrap_payload_type_erasure_class_spec.spl` —
  defect-CLASS sweep over sibling payload-extraction shapes (Option.unwrap,
  unwrap directly on a call expression, nested double unwrap, unwrapped value
  passed as a typed argument, unwrapped value stored in an array), all against
  the same colliding method name. Carries an explicit positive control
  asserting both colliding `tagged()` methods load and compute distinct values
  (1007 vs 2007), so a no-op scanner cannot report a false clean sweep.
  `Results: 7 total, 7 passed, 0 failed`.

**Native lane remains unproven on this host.** `bin/simple native-build --entry
<fixture> --clean` did not produce a binary: the worker exited with
`native-build worker timed out ... before producing a binary`. That is a host
throughput limit (load average 22+, ~30 concurrent `simple` processes), not
evidence about this defect — recorded as INCONCLUSIVE, not as a pass. The
earlier native proof at origin tip `8932fcb3a148` (above) still stands as the
native-lane evidence.

TODO 558 is therefore left **open** rather than closed: the interpreter half is
now proven and specced, the native re-proof on this host is not.
