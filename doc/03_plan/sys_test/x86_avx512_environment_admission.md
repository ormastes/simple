# AVX-512 and SIMD environment-gated test plan

## Scope

This plan covers portable admission logic, target policy, cross-OS target
labels, interpreter/fallback semantics, and the native execution admission
boundary for x86-64 AVX-512. Unit tests always run on every host. Native
instructions run only on x86-64 when CPUID and OS state admit the requested
operation and an explicit fixture supplies a runtime receipt.

## Test matrix

| Requirement | Executable evidence | Manual evidence | Coverage |
| --- | --- | --- | --- |
| REQ-AVX512-006, REQ-SIMD-002 | `test/01_unit/compiler/backend/native/x86_simd_environment_admission_spec.spl` | `doc/06_spec/01_unit/compiler/backend/native/x86_simd_environment_admission_spec.md` | Synthetic CPUID/XCR0 removal matrix, target gate, denied provenance |
| REQ-AVX512-002, REQ-AVX512-006 | `test/01_unit/compiler/backend/native/x86_avx512_fma_encoding_spec.spl` | `doc/06_spec/01_unit/compiler/backend/native/x86_avx512_fma_encoding_spec.md` | Complete VFMADD213PS EVEX goldens and malformed-register rejection |
| REQ-AVX512-001/002/006 | `test/02_integration/compiler/native/x86_avx512_native_execution_environment_spec.spl` | `doc/06_spec/02_integration/compiler/native/x86_avx512_native_execution_environment_spec.md` | Host classifier, operation subset gate, receipt, fixture execution |
| REQ-AVX512-001/004 | `test/01_unit/compiler/interp/mir_simd_avx512_semantics_spec.spl` | Existing generated manual | Fixed Vec16f/Vec8d/Vec16i interpreter oracle |
| REQ-AVX512-002/003 | `test/02_integration/compiler/native/x86_avx512_mir_pipeline_spec.spl` | Existing generated manual | Selector and final EVEX pipeline |

## Environment contract

The native row requires `arch=x86_64`, CPUID AVX-512F, OSXSAVE, XCR0 XMM/YMM
state, and XCR0 opmask/ZMM state. Operation-specific rows additionally require
AVX-512BW for byte/word operations, AVX-512DQ for DQ operations, and
AVX-512VL for VL operations. FMA defaults to `fma-f32x16` and requires F only.
Linux under WSL is tagged `wsl-linux`; native Linux is `native-linux`. Windows,
FreeBSD, and macOS retain distinct tags.

Unavailable rows remain visible as `UNSUPPORTED`; qualified hosts lacking the
fixture remain `BLOCKED`. Both force `enabled=false` and `attempted=false`.

## Qualified-host resume command

```powershell
$env:SIMPLE_LIB = 'src'
$env:SIMPLE_AVX512_NATIVE_OPERATION = 'fma-f32x16'
$env:SIMPLE_AVX512_NATIVE_PROBE = '1'
$env:SIMPLE_AVX512_NATIVE_FIXTURE = '<absolute path to admitted fixture>'
bin\simple test test\02_integration\compiler\native\x86_avx512_native_execution_environment_spec.spl --native
```

The fixture must emit `AVX512_RUNTIME_RECEIPT|status=PASS|operation=...|environment=...`
and exit zero. Capture that line with the test output as the runtime receipt.

## Verification and diff checks

Run each changed spec once through the admitted pure-Simple runtime. Before
handoff, inspect only this lane with:

```powershell
git diff --check -- test/01_unit/compiler/backend/native/x86_simd_environment_admission_spec.spl test/02_integration/compiler/native/x86_avx512_native_execution_environment_spec.spl doc/03_plan/sys_test/x86_avx512_environment_admission.md doc/06_spec/01_unit/compiler/backend/native/x86_simd_environment_admission_spec.md doc/06_spec/02_integration/compiler/native/x86_avx512_native_execution_environment_spec.md
```

The seed runtime cannot prove live CPUID probing when its runtime lacks
`rt_xgetbv`; use the redeployed pure-Simple runtime for the integration row.
No production source or commit/push is part of this lane.
