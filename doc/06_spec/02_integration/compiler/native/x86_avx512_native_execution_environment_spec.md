# x86_avx512_native_execution_environment_spec

## Overview

This host fixture lane classifies the running OS, architecture, CPUID AVX-512
subsets, OSXSAVE, and XCR0 extended-register state. Every run emits an
`AVX512_ENV_RECEIPT` row. A non-x86 or incomplete host is `UNSUPPORTED`; a
qualified host without an admitted fixture is `BLOCKED`. Neither state enables
or attempts an AVX-512 instruction.

**Requirements:** `doc/02_requirements/feature/x86_avx512_fixed_compiler_interpreter.md`

**Plan:** `doc/03_plan/sys_test/x86_avx512_environment_admission.md`

**Design:** `doc/05_design/x86_avx512_fixed_compiler_interpreter.md`

**Research:** `doc/01_research/local/full_pure_simple_simd_bootstrap.md`

## Scenarios

### should classify every host and leave an auditable capability receipt

The production host and SIMD capability facades are read. The output contains
the schema, OS, platform, architecture, WSL/native environment tag, requested
operation, all required AVX-512 subset bits, OSXSAVE/XCR0 state, status, reason,
and enable/attempt flags.

### should never enable or attempt AVX-512 when the host is unavailable

`UNSUPPORTED` rows are retained in the result and assert `enabled=false` and
`attempted=false`. `BLOCKED` rows apply the same fail-closed rule when a
qualified host has no fixture.

### should execute the admitted fixture only after capability and fixture admission

When `SIMPLE_AVX512_NATIVE_FIXTURE` names an executable and every requirement
for `SIMPLE_AVX512_NATIVE_OPERATION` is present, the fixture must return zero
and emit `AVX512_RUNTIME_RECEIPT|status=PASS` with matching operation and
environment tags. The fixture is never launched before that admission.

## Reproduction

```powershell
$env:SIMPLE_LIB = 'src'
$env:SIMPLE_AVX512_NATIVE_OPERATION = 'fma-f32x16'
$env:SIMPLE_AVX512_NATIVE_PROBE = '1'
$env:SIMPLE_AVX512_NATIVE_FIXTURE = '<absolute path to admitted native fixture>'
bin\simple test test\02_integration\compiler\native\x86_avx512_native_execution_environment_spec.spl --native
```

The fixture must print:

```text
AVX512_RUNTIME_RECEIPT|status=PASS|operation=fma-f32x16|environment=<native-linux|wsl-linux|native-windows|native-freebsd|native-macos>
```

## Limitations

The repository currently has no checked-in native fixture path, so a qualified
host reports `BLOCKED` until the FMA runtime artifact is admitted. The explicit
probe opt-in also keeps older bootstrap seeds that lack `rt_xgetbv` in the
`BLOCKED` state. This spec does not treat compiler selection or EVEX bytes as
native execution evidence.
