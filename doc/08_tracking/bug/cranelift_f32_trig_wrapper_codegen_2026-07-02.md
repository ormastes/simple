# Cranelift JIT: f64→f32 trig wrapper bodies fail codegen (engine3d)

Date: 2026-07-02
Status: open (interpreter fallback works)
Severity: P3
Found by: W6 lane agent

## Symptom

```
JIT compilation failed ... Cranelift JIT compile: Module error: codegen:
7 function body/bodies failed to compile:
[_sin, _cos, _tan, _sqrt, gpu3d_sqrt_f32, gpu3d_sin_f32, gpu3d_cos_f32]
```

The Cranelift verifier rejects the f64→f32 trig wrapper bodies in
`src/lib/nogc_sync_mut/gpu/engine3d/` (math_hooks/simd_kernels3d).
Surfaced once earlier lowering blockers were cleared; engine3d programs
run interpreted until fixed.
