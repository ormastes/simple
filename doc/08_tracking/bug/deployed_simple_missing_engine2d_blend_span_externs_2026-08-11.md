# Deployed Simple misses Engine2D blend-span externs

## Status

Open deployment skew; blocks focused software-backend parity verification.

## Evidence

The bounded 8x4 spec
`test/01_unit/lib/gpu/engine2d/backend_software_blend_span_spec.spl` reaches
semantic analysis but fails both cases with:

```text
unknown extern function: rt_engine2d_simd_blend_const_span_u32
```

The symbol is present in current authoritative sources:

- `src/runtime/runtime.h`
- `src/runtime/runtime_simd_dispatch.c`
- `src/compiler_rust/common/src/runtime_symbols.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/mod.rs`
- `src/compiler_rust/compiler/src/interpreter_extern/simd.rs`
- `src/compiler_rust/runtime/src/value/engine2d_simd_ops.rs`

Therefore this result does not contradict the kernel implementation; it proves
`build/native_probe/simple` predates the registration.

The same deployed artifact also reports `unknown extern function:
rt_is_interpreter_runtime` after the WM compositor frame-switch parser defects
were repaired. That symbol exists in current `runtime.h`, `runtime.c`,
`runtime_native.c`, pure-Simple core process support, runtime symbol tables,
codegen, and the interpreter extern registry. The focused compositor receipt
suite now reaches 3 pass / 1 fail before stopping on this deployment skew.

## Required resolution

Redeploy a pure-Simple CLI from the current admitted runtime authority, then
run the focused parity spec once. Admission requires exact scalar/SIMD pixels,
negative clipping, transparent no-op, identical damage rectangles, nonzero
native receipts for an ISA lane, and no per-row allocation. Keep the existing
cross-architecture C operation report as native kernel evidence, not as an
end-to-end Engine2D or 8K/80 receipt.
