# Imported callables without `->` carry no param types on their surface symbol

- Status: open (follow-up; the Stage 3 blocker is mitigated by the MIR receiver-tail registry)
- Severity: P2
- Found: 2026-11-12, early Phase 3 census on run 15's Stage 2
- Component: HIR import surface (`src/compiler/20.hir/hir_lowering/_Items/module_callable_types.spl`
  `declared_surface_callable_type`), MIR `symbol_to_operand`

## Observation
`declared_surface_callable_type` returns nil for every imported callable that
declares no return type (`if not callable.has_return_type and not callable.is_extern: return nil`).
The consumer's symbol therefore has `type_ = nil`, and MIR builds the callee
operand with no declared params. Cranelift then refuses any float argument:

```
E-BACKEND-CRANELIFT-CALL-ABI: compiler.hir.hir_codec_support.HirCodecWriter.put_f64: callee signature unknown; arg 1 is f64 and cannot be passed through the all-i64 import
```

This panicked the Stage 3-shape build of bootstrap_main at
`src/compiler/20.hir/generated/hir_codec.spl:3386` (`w.put_f64(b_value)`).

## Mitigation landed with this record
MIR now registers the provider method's params AFTER the receiver under
`<link>#receiver-tail` in the existing symbol-free param registry. It does
this only for a plain class/struct receiver, not for a unit/newtype owner.
`symbol_to_operand` consults that record only when `sym.type_` is nil. Still
uncovered, failing closed (loud):
- a method whose non-receiver params include a Named type (provider-local
  SymbolIds are rejected by the registry);
- an untyped method or function with an f64 result, since the return stays i64;
- a free function without `->`. This depends on whether its call path builds
  the operand from `sym.type_` only; see the PR evidence.

## 2026-11-14: nominal params and receiver-less callables covered
Stage 3 run 32 aborted in native codegen on the first uncovered case above:

```
E-BACKEND-CRANELIFT-CALL-ABI: plugins.backend_cuda.cuda.ptx_builder.PtxBuilder.emit_const_float: call in plugins.backend_cuda.cuda_backend.CudaBackend.compile_const: callee signature unknown; arg 3 is f64 and cannot be passed through the all-i64 import
```

`emit_const_float(dest: text, ty: PrimitiveType, value: f64)` has no `->`, and
its tail names an enum, so the registry rejected the whole tail. Measured on a
Stage 2 (pin 96ec72139608) with two-module fixtures: a `(text, f64)` tail
builds and runs, and so does the enum tail once the method declares `-> i64`;
the enum tail without `->` aborts with exit 134, as do a static method and a
free function of the same shape.

The provider prescan now publishes symbol-free ABI stand-ins, resolved while the
defining module's `SymbolTable` is the one in hand
(`module_lowering.spl` `mir_abi_param_stand_in_v1`): a class/struct/enum param
is the handle word, a unit/newtype its underlying scalar, array/slice/optional
keep their shape. Instance methods publish the receiver tail as before; static
methods and free functions publish every param under `<link>#abi-params`,
read by `symbol_to_operand` and by the direct-call path when no declared types
reach the call. The plain param record is untouched (it drives argument slot
lowering and still rejects a symbol-bearing list).

Still uncovered, failing closed (loud): params the provider table does not
prove (trait objects, type parameters, a unit/newtype whose name- and
symbol-keyed records disagree, dict/tuple/result shapes holding a nominal
type), a receiver that is not a plain class/struct, and an f64 result of an
untyped callable. A refusal no longer aborts the build: the Cranelift AOT
entry returns it as that module's compile error and codegen goes on to the
next module (`cranelift_runtime_imports.spl` `cl_aot_refuse_call_abi`; spec
`test/01_unit/compiler/backend/cranelift_aot_call_abi_refusal_spec.spl`,
native fixture `test/fixtures/native_call_abi_refusal_module_error/`).

Spec: `test/01_unit/compiler/mir/imported_untyped_callable_abi_params_spec.spl`.
Native fixture: `test/fixtures/native_method_named_f64_call_abi/`.

## Complete fix (not done)
Record declared param types on the surface symbol even when `type_` is nil.
This would be a new `HirSymbol` field, the same shape as the
`generic_param_count` precedent, set at import-surface registration and read
by MIR. It needs `src/compiler/20.hir/generated/hir_codec.spl` regenerated for
the new field and a HIR cache format version bump. Setting `type_` itself is
not an option: HIR call typing reads the symbol's Function return type
(`expression_core.spl:104/128/338/385`, `accessor_forwarding.spl:90`).

## 2026-11-14 recurrence and standalone repair candidate

The frozen fable stage-3 build based on 2864bc90f8ce failed at log line
1305144 before its SIGABRT: `PtxBuilder.emit_const_float` called by
`CudaBackend.compile_const` had an unknown callee signature, and its fourth
argument was f64. The 1664 aggregate failures are fallout from one worker abort.
Its preceding declaration includes the nominal `PrimitiveType` enum parameter,
so the historical receiver-tail workaround's explicit symbol-free restriction
cannot repair this call. Current release bb2a83ed4da contains neither the complete
metadata fix nor that historical workaround; the older mitigation wording above
must not be read as proof of current release behavior.

Candidate adds optional `HirSymbol.declared_param_types_v1`, independently from
`type_` and return inference. Complete nongeneric imported declarations project
parameters through their actual owner into importer-local nominal identities.
Unknown annotations, generic binders and projection errors remain unknown. MIR
uses the declaration evidence only when the original callable type is absent;
the Cranelift f64/all-i64 guard remains intact. Renames and same-table verification
copies preserve metadata. The nominal relocator accepts only type declarations,
not callable symbols; future cross-table callable transports must relocate their
parameter arrays explicitly rather than copying foreign numeric IDs.

Wire identities become `spl-hircodec-v19-declared-call-params` and
`spl-hircodec-canonical-v9-declared-call-params`, distinct from the unmerged
visibility schema. The actual pinned generator produced baseline bytes identical
to release and the changed 99-declaration codec in two bounded runs (1.841/1.899
seconds; peak tree RSS 545955840/567287808 bytes). All nine borrowed input files
and the prior generated output were restored byte-for-byte. Evidence is retained
under `/tmp/simple-imported-method-params-20261114/build/declared-params-codec/`.
This proves generation, not execution of the new codec or compiler pipeline.

Real parser/HIR/MIR/codec regression is authored at
`test/01_unit/compiler/hir/imported_declared_param_metadata_spec.spl` and remains
UNRUN until an executable containing the changed compiler is available. Merely
compiling changed target sources with the old P2 does not change its own importer
or MIR implementation. Bug remains fixing; no runtime qualification is claimed.
