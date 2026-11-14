# Stage 2: implicit `-> T?` tail return takes the scalar-sink arm (2026-11-15)

Status: second source fix committed on `work/p3-cranelift-option-f64-20261115`.
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
| `-> f32?` tail `Some(x)` | verifier refusal (`bitcast 64 bits ... expected 32`) | llc refusal (`bitcast i64 to float`) |
| `-> i64?` tail `Some(3)` / bare tail `x` = 3 | compiles; returns the raw payload; `match` reads `None` | same |
| `-> i64?` if/else or match tail, `None` arm | runtime abort `.unwrap() called on None` | same |
| `-> i64?` tail `Some(9000000000)`, `bool?` `Some(false)`, `text?`, bare `nil` | correct output (raw word happens to read right) | same |
| explicit `return Some(x)` / `return x` / `return nil` / `return None` | correct callee (disassembly: `rt_enum_new(1, disc, ..)`) | correct |
| `f64?` struct field, `[f64]?` tail, `Some(f64)` as argument | correct | correct |

A separate caller-side defect turned up while checking. `if val a = <i64? None>`
prints `some 3` on both backends: a local `val o: i64? = None`, `rn()` and
`return nil` callees alike. `match` and `.?` on the same value answer None.
That bug is not in the return path and is not fixed here, so the fixtures use
`match`.

The disassembly of `fn f(x: f64) -> f64?: Some(x)` (LLVM object) is
`rt_enum_new` -> `rt_unwrap_or_trap` -> `fmov d0,x0` -> `fcvtzs`. The handle is
built and then unwrapped again. On an implicit tail only
`option_payload_for_int_sink` emits `rt_unwrap_or_trap`
(`_MirLowering/function_lowering.spl`, the `Int|Float|Bool|Char` arm of
`match fn_.return_type.kind`). So the tail takes the scalar arm, and the
signature is i64 (see Root cause for why).

## Root cause

The fault is not a miscompiled `match`; the HIR input differs. Under
`SIMPLE_BOOTSTRAP=1`, which is how native-build runs, HIR declaration
lowering (`20.hir/hir_lowering/_Items/declaration_lowering.spl`, bootstrap arm
of `lower_function`, ~line 446) replaces a declared return type with
`bootstrap_builtin_return_type`, the i64 default. Only
`Str|Bool|Float|Unit|TypeParam` are exempt, so a declared `-> T?` lands in
`HirFunction.return_type` as `Int`. The symbol keeps the declared `T?`.

`lower_function`'s implicit tail dispatched on `fn_.return_type`, so it took
the `Int|Float|Bool|Char` arm, and `option_payload_for_int_sink` unwrapped the
Some handle that had just been built. The MIR signature is i64 for the same
reason, which is why Cranelift reported `signature of i64`. The explicit
`return` was correct because `lower_return_expr` reads the declared type via
`resolved_call_hir_return_type(symbol)`.

Measured with the Stage 2 built from the first fix (`SIMPLE_COMPILER_TRACE=1`
plus `SIMPLEOS_FOCUSED_HIR_DIAG=1`):
- the flat return tag for `-> f64?` is 16 (`Option<f64>`);
- the `[mir-lower-type-probe]` of the return type gives the same
  discriminant as `-> i64`, not the Optional discriminant;
- `lower_type` emits no `[mir-optional-inner]` for it.

The first seed spec had lowered without `SIMPLE_BOOTSTRAP`, so it could not see
the erased type. The first fix (discriminant predispatch, `cd49cc6b8af`) rested
on a wrong diagnosis; a Stage 2 built from it behaved identically.

## Fix

`lower_function` takes the tail's return type from
`resolved_call_hir_return_type(fn_.symbol)` when that type is `Optional`, the
same source `lower_return_expr` uses. It uses that type for:
- the conditional-tail flag;
- `lower_block_expected`;
- `coerce_native_trait_object`;
- the tail dispatch, so the Optional arm calls `ensure_option_handle`.

The ABI slot does not change: the handle is a word, as on the explicit-return
path. The predispatch workaround is reverted.

## Evidence

- Spec: `test/01_unit/compiler/mir/implicit_tail_optional_return_handle_spec.spl`.
  Its bootstrap-HIR row lowers HIR with `SIMPLE_BOOTSTRAP=1`. On the seed it
  goes red -> green: `rt_unwrap_or_trap` appears in the tails before the fix
  and not after.
- Native oracles: `test/fixtures/native_option_f64_enum_payload/main.spl` and
  `test/fixtures/native_option_scalar_tail_siblings/main.spl` (expected stdout
  is in each header). Run both with both backends on a Stage 2 built from the
  fix. In the disassembly, `as_f64` must contain `rt_enum_new` and no
  `rt_unwrap_or_trap`.
