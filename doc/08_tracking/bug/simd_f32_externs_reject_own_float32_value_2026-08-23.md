# SIMD f32 externs reject the interpreter's own `Float32` value as not-a-float

- **Filed:** 2026-08-23
- **Status:** FIXED (this change)
- **Engine:** Rust seed, tree-walk **interpreter**. Not JIT, not native — these
  are `interpreter_extern` handlers, so no other engine reaches this code.
- **Runtime:** the **Rust** runtime only. The C runtime (`src/runtime/*.c`) has
  no counterpart to `require_f64_field` and is unaffected. The two symbol sets
  are evaluated separately and were not unioned here.

## Symptom

Six specs failed with one message shape:

```
runtime: rt_simd_mul_f32x4: field x must be a float, got Float32(1.0)
```

i.e. the runtime rejected **its own** `Float32` box as not-a-float.

Verbatim pre-fix output, `bin/simple test test/01_unit/lib/simd_f32x4_boxed_field_repro_spec.spl`:

```
simd f32 dot repro
  ✗ reproduces the boxed-Float32 crash
    runtime: rt_simd_mul_f32x4: field x must be a float, got Float32(1.0)
  ✓ keeps the f64 sibling path green as a control

2 examples, 1 failure
Results: 2 total, 1 passed, 1 failed
```

## Root cause

`src/compiler_rust/compiler/src/interpreter_extern/simd.rs:542` —
`require_f64_field` matched `Value::Float` and `Value::Int` but **not**
`Value::Float32` (`compiler/src/value.rs:1558`), so every `f32`-lane SIMD extern
that reads a `Vec4f`/`Vec8f` field rejected a genuine f32 value. One predicate,
six failing specs.

## Neighbour sweep

The same omission was present in five sibling readers of the same class — every
place that accepts `Value::Float` + `Value::Int` for a float-typed read but
never `Value::Float32`:

| file:line | function |
|---|---|
| `interpreter_extern/simd.rs:542` | `require_f64_field` (the filed one) |
| `interpreter_extern/audio.rs:131` | `as_float` |
| `interpreter_extern/vulkan.rs:221` | `arg_f64` |
| `interpreter_extern/cranelift.rs:68` | `expect_f64` |
| `interpreter_extern/rapier2d_sffi.rs:94` | `get_f64` |
| `interpreter_extern/rapier2d_sffi.rs:109` | `get_f64_array` (element read) |

Deliberately **not** changed: `require_u32_field` and `require_i64_field`
(`simd.rs:519`, `:531`). Those read integer fields; accepting a float there
would be a semantic change, not a widening.

## Fix

Add a `Value::Float32(n) => f64::from(*n)` arm to each of the six readers. This
is a pure widening: every input previously accepted is still accepted and yields
the identical `f64`. No `rt_*` ABI, SFFI contract, value-semantics or COW
behaviour changed; no assertion was weakened.

## Tests

- `test/01_unit/lib/simd/simd_f32_extern_float32_field_spec.spl` (+ mirror in
  `test/unit/`) — reproduce plus four neighbouring lane ops in the same class.
- `test/01_unit/lib/simd_f32x4_boxed_field_repro_spec.spl` — the pre-existing
  repro, now green.
