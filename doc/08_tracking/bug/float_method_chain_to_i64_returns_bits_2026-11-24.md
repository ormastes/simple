# Chained `x.ceil().to_i64()` returns the raw f64 bits (JIT / native)

- Status: fixed (lane `work/compiler-chain-repeat-bugs-20261124`)
- Found: 2026-11-24, web-render lanes
- Engines: Rust seed static JIT, default mode, native cranelift build. Interpreter correct for the cast.

## Repro

```
fn main():
    val x: f64 = 0.4
    val c = x.ceil()
    print("{x.ceil().to_i64()} {c.to_i64()} {x.ceil().to_i32()}")
main()
```

| engine | output |
|---|---|
| interpreter | `1 1 1` |
| JIT / default (base `4da62cc1731`) | `4607182418800017408 1 1` |

The same shape breaks `floor`/`round`/`trunc`/`sqrt`/`abs` followed by
`to_i64` or `to_int`, on f64 and f32 receivers, positive and negative.
The narrowing casts `to_i32`/`to_u8` and the bound-local form were already correct.
Other consumers of the same untyped result (`x.ceil() + 0.5`, `x.ceil() < 1.5`,
`x.ceil().to_string()`) were also correct.

## Root cause

MIR is `MethodCallStatic f64.ceil` -> `MethodCallStatic f64.to_i64`.
`build_vreg_types` (`codegen/instr/body.rs`) has no arm for the
float math methods, so the dest of `f64.ceil` is untyped. In the
numeric-cast lowering (`compile_method_call_static` in
`codegen/instr/closures_structs.rs`, and its twin in
`codegen/instr/methods.rs`), `from_ty` defaulted to I64.
`int_cast_needs_runtime_dispatch(I64)` is true, so `to_i64`/`to_int` routed
the raw F64 register to `rt_to_int_dynamic`, which returned the word verbatim:
the IEEE bit pattern. That branch ran before the existing "honor the
Cranelift value type" fallback. That fallback is why the narrowing casts were right.

## Fix

In both cast sites, a receiver whose Cranelift value type is F32/F64 now sets
`from_ty`. A Cranelift float value is always a real float, so this is ground
truth; only the reverse inference (untyped vreg => I64) is unsound. The cast
then takes the saturating `fcvt_to_sint` path like `to_i32` always did.

LLVM backend: `llvm/functions.rs` already gates its `rt_to_int_dynamic`
path on `recv_val.is_int_value()`, so it is not affected (not built here; no
`llvm` feature in the default seed).

## Companion: interpreter rejected `x.ceil().sqrt()`

The interpreter's chained-receiver arm (`call_method_on_value` in
`interpreter_helpers/method_dispatch.rs`) carried its own short float method
list (abs/floor/ceil/round/casts). `x.ceil().sqrt()` therefore failed with
"method 'sqrt' not found on value of type f64 in nested call context", while
`x.sqrt()` worked. Zero-argument float methods now delegate to the same
`primitives::handle_float_methods` the direct-receiver path uses.
For f32 the result is re-narrowed exactly as the direct path does.

## Test

`src/compiler_rust/compiler/tests/float_chain_repeat_engines.rs` over
`test/fixtures/native/float_chain_repeat/main.spl`. It runs the interpreter, the static JIT and a
native cranelift build, and each must return failure mask 0. Base: JIT mask 447,
interpreter error.
