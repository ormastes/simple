# Phase-2 Cranelift: f64 argument to an imported method without `->` aborts the codegen worker (2026-11-16)

**Status:** OPEN on frozen Phase-2 pin `18a1f28937c2`. Defect 2 is fixed in the current AOT source; the fix for defect 1 is unverified for this exact call.
**Area:** MIR call lowering (`symbol_to_operand`) + Cranelift AOT call-ABI check
**Context:** Stage 3 compiler built by the frozen Phase-2 compiler with `--backend cranelift`.

## Symptom

The codegen worker died on the first error (Windows fast-fail `0xC0000409`), not
collected even with `--keep-going --go-to-end`:

```
E-BACKEND-CRANELIFT-CALL-ABI: compiler.hir.hir_codec_support.HirCodecWriter.put_f64:
callee signature unknown; arg 1 is f64 and cannot be passed through the all-i64 import
```

Call site: `w.put_f64(b_value)` in `src/compiler/20.hir/generated/hir_codec.spl`
(~line 3391). Callee: `me put_f64(v: f64):` in
`src/compiler/20.hir/hir_codec_support.spl` (~496), which has no `->` return
annotation, so its surface symbol carries no callable type.

Build-tree workaround that worked (full 1,429-unit Cranelift codegen, 0 failed
modules): give the f64/f32-taking methods without `->` an explicit `-> i64`
(`put_f64`; `semantic_canonical_write_f32_v1` / `semantic_canonical_write_f64_v1`
in `src/compiler/00.common/cache_contract/semantic_canonical_stream_v1.spl`).

## Defect 1: missing callee param types

`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:6513-6538`
(`symbol_to_operand`): when the imported symbol has no callable type
(`sym_type_present == false`) it takes the provider-prescanned receiver-tail
params via `bootstrap_method_receiver_tail_params_lookup_v1(name)`
(`src/compiler/50.mir/mir_data.spl:2864`), builds
`[i64 receiver handle] + tail params` with return `i64`, and marks
`declared_params_known: true`. This mechanism is intended to cover the shape
in this bug (method with `me` receiver, f64 tail param, no return annotation,
imported from another module). Static/UFCS callables fall to
`callable_abi_declared_params_v1`; a later block (`declared_param_types_v1`)
outranks both when the importer retained exact param types.

The frozen pin already contains the receiver-tail lookup, yet the failure
occurred on it. The registry may not have been populated for this call, or the
generated-module call may have taken another path. The later ABI-declared and
`declared_param_types_v1` branches have not been verified to fix this exact call;
the build-tree workaround remains the only verified cure.

Spec pinning: `test/01_unit/compiler/mir/method_receiver_tail_params_spec.spl`
("answers an f64 tail for a method whose surface type is nil", header cites
this exact `w.put_f64` census) and
`test/01_unit/compiler/mir/imported_untyped_callable_abi_params_spec.spl`.
Both pin the registry/lookup, not the full lowering-to-Cranelift path;
`test/fixtures/native_method_named_f64_call_abi/main.spl` is the end-to-end
fixture. Not re-run for this doc (read-only verification).

## Defect 2: CALL-ABI error aborts the worker instead of failing one module

Raised in `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`
at lines 1822-1831 (runtime/foreign import path) and 1909-1915 (external
function path). Today it is a COLLECTED per-module failure when an AOT record is
open: `cl_aot_refuse_call_abi` (`cranelift_runtime_imports.spl:94`) appends the
message to `_cl_aot_call_abi_errors_v1` and the lowering emits a placeholder;
the AOT entry (`cranelift_codegen_adapter.spl:270-274` and `341-349`,
`cl_aot_call_abi_begin/end`) returns the refusals as that module's
CompileError before any object is emitted. The `panic(...)` at `:1831` and
`:1915` is reached only when no AOT record is open for the module handle
(fail-closed fallback). Introduced by `90b1f0433ac` ("a refused call ABI fails
its module, not the codegen worker"); pinned by
`test/01_unit/compiler/backend/cranelift_aot_call_abi_refusal_spec.spl` and
`test/fixtures/native_call_abi_refusal_module_error/main.spl`.

So the frozen Phase-2 compiler aborted because it predates `90b1f0433ac`; no
current-source action remains for defect 2.

## Tracking

No `bug_db.sdn` row added: the sealed file conflicts with other open PRs.
