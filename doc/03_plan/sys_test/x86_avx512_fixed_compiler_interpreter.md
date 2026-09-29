# AVX-512 Fixed Compiler/Interpreter Test Plan

| Requirement | Evidence | Gate |
| --- | --- | --- |
| REQ-AVX512-001/003/004/005 | `mir_simd_avx512_semantics_spec.spl`, `mir_simd_interpreter_parity_spec.spl` | Interpreter behavior |
| REQ-AVX512-002/003 | `x86_avx512_mir_pipeline_spec.spl` | Selector and final encoding |
| REQ-AVX512-002 | `x86_avx512_memory_encoding_spec.spl` | Complete f32/f64 gather and permute byte goldens |
| REQ-AVX512-006 | capability, memory, and spill-guard unit specs | Fail closed |

Run each gate once with an admitted self-hosted artifact whose SHA is recorded. With PowerShell variables `$RUNTIME` and `$env:SIMPLE_LIB = 'src'`, resume with:

```powershell
& $RUNTIME test test/01_unit/compiler/interp/mir_simd_avx512_semantics_spec.spl --mode=interpreter
& $RUNTIME test test/02_integration/compiler/mir_simd_interpreter_parity_spec.spl --mode=interpreter
& $RUNTIME test test/01_unit/compiler/backend/native/x86_avx512_memory_encoding_spec.spl --mode=interpreter
& $RUNTIME test test/02_integration/compiler/native/x86_avx512_mir_pipeline_spec.spl --mode=interpreter
```

Native execution and performance are blocked pending a qualified AVX-512F machine. Resume there by native-building the pipeline fixture with the same admitted runtime, executing it once, and comparing its output hash with interpreter output; record CPU capability evidence and both hashes.
