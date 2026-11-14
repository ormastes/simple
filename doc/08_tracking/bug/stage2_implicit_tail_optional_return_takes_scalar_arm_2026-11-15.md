# Stage 2: implicit `-> T?` tail return takes the scalar-sink arm (2026-11-15)

Status: source fix committed on `work/p3-cranelift-option-f64-20261115`.
Native confirmation still needs a Stage 2 built from that branch.

## Symptom

Building any closure that contains `src/lib/common/sdn/value.spl` with Stage 2
(`pinned-a7be114a4db7`, `bootstrap-s2probe-p3codegen2`) fails:

```
cranelift: AOT define_function error: Verifier errors:
- inst41 (return v31): result 0 has type f64, must match function signature of i64
... Failed to compile function: lib.common.sdn.value.SdnValue.as_f64
```

The adapter already prints the verifier text on stderr
(`describe_module_error`, `cranelift_sffi.rs`). The `CompileFailed` line keeps
only the function name.

## Trigger

The trigger is the implicit tail of any function declared `-> T?`. An explicit
`return Some(x)` compiles and runs correctly. The payload type does not matter:

| shape (current Stage 2) | cranelift | llvm |
|---|---|---|
| `-> f64?` tail `Some(x)`, or a match/if tail | verifier refusal (`return f64` vs sig `i64`) | silent: returns `fptosi(payload)`, prints a denormal |
| `-> f32?` tail `Some(x)` | verifier refusal (`bitcast 64 bits ... expected 32`) | n/a |
| `-> i64?` tail `Some(x)` | compiles; returns the raw payload, not a handle | same |
| `-> i64?` tail `None` | compiles; caller sees `some 3` | same |
| `-> i64?` if/else tail, `None` arm | runtime abort `.unwrap() called on None` | same |
| `return Some(x)` (explicit) | correct | correct |
| `f64?` struct field, `[f64]?` tail, `Some(f64)` as argument | correct | correct |

The disassembly of `fn f(x: f64) -> f64?: Some(x)` (LLVM object) is
`rt_enum_new` -> `rt_unwrap_or_trap` -> `fmov d0,x0` -> `fcvtzs`. The handle is
built and then unwrapped again. On an implicit tail only
`option_payload_for_int_sink` emits `rt_unwrap_or_trap`
(`_MirLowering/function_lowering.spl`, the `Int|Float|Bool|Char` arm of
`match fn_.return_type.kind`). So compiled Stage 2 sends an `Optional` return
kind into the scalar arm. The signature is still `lower_type(Optional)` = ptr.

## Root cause

The seed interpreter dispatches that broad `HirTypeKind` match correctly, so it
lowers correct MIR. The fault exists only in the compiled Stage 2 compiler. This
is the same class `lower_type` already works around for Optional ("Stage3's
broad HirTypeKind match can fail to recognize Optional").

## Fix

`lower_function`'s tail-return dispatch now predispatches on
`_sffi_hir_type_discriminant` with an if/elif chain, tagged `@workaround`.
Behaviour per kind is unchanged. `lower_return_expr` has the same arm list and
dispatches correctly in Stage 2, so it is left unchanged. The earlier
`match fn_.return_type.kind` with an `Optional(tail_optional_inner)` arm (the
conditional-tail flag) has the same shape, but no evidence shows it
misdispatching.

## Evidence

- Spec: `test/01_unit/compiler/mir/implicit_tail_optional_return_handle_spec.spl`
  (source row red -> green; MIR rows pin the handle shape on the seed).
- Native oracle: `test/fixtures/native_option_f64_enum_payload/main.spl`
  (expected stdout is in its header). Run it with both backends on a Stage 2
  built from the fix. In the disassembly, `as_f64` must contain `rt_enum_new`
  and no `rt_unwrap_or_trap`.
