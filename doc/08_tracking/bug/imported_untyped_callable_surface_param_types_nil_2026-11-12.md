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
untyped callable.

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
