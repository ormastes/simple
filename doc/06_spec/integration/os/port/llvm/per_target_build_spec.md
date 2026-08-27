# Per Target Build Specification

> Tests covering SimpleOS LLVM per-target build (A4/A5).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per Target Build Specification

## Scenarios

### SimpleOS LLVM per-target build (A4/A5)

#### declares CROSS_SUPPORTED_TARGETS

- declares CROSS_SUPPORTED_TARGETS
   - Expected: src contains `val CROSS_SUPPORTED_TARGETS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("declares CROSS_SUPPORTED_TARGETS")
"""The SimpleOS target list constant must be present."""
val src = build_spl_src()
expect(src.contains("val CROSS_SUPPORTED_TARGETS")).to_equal(true)
```

</details>

#### CROSS_SUPPORTED_TARGETS lists all four SimpleOS triples

- CROSS_SUPPORTED_TARGETS lists all four SimpleOS triples
   - Expected: src contains `x86_64-unknown-simpleos`
   - Expected: src contains `aarch64-unknown-simpleos`
   - Expected: src contains `riscv64gc-unknown-simpleos`
   - Expected: src contains `riscv32imac-unknown-simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("CROSS_SUPPORTED_TARGETS lists all four SimpleOS triples")
"""All 4 triples required by A4 must appear in build.spl."""
val src = build_spl_src()
expect(src.contains("x86_64-unknown-simpleos")).to_equal(true)
expect(src.contains("aarch64-unknown-simpleos")).to_equal(true)
expect(src.contains("riscv64gc-unknown-simpleos")).to_equal(true)
expect(src.contains("riscv32imac-unknown-simpleos")).to_equal(true)
```

</details>

#### honours SIMPLE_TARGET env override

- honours SIMPLE_TARGET env override
   - Expected: src contains `SIMPLE_TARGET`
   - Expected: src contains `cross_selected_targets`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("honours SIMPLE_TARGET env override")
"""Single-target override must be wired into selection."""
val src = build_spl_src()
expect(src.contains("SIMPLE_TARGET")).to_equal(true)
expect(src.contains("cross_selected_targets")).to_equal(true)
```

</details>

#### cross_build_all iterates CROSS_SUPPORTED_TARGETS

- cross_build_all iterates CROSS_SUPPORTED_TARGETS
   - Expected: src contains `fn cross_build_all`
   - Expected: src contains `cross_build_stage_for_target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("cross_build_all iterates CROSS_SUPPORTED_TARGETS")
"""Full cross-build must loop via the per-target stage helper."""
val src = build_spl_src()
expect(src.contains("fn cross_build_all")).to_equal(true)
expect(src.contains("cross_build_stage_for_target")).to_equal(true)
```

</details>

#### exports build_compiler_rt(triple)

- exports build_compiler_rt(triple)
   - Expected: src contains `fn build_compiler_rt(triple: text)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exports build_compiler_rt(triple)")
"""A5's public compiler-rt builder must be present with a triple parameter."""
val src = build_spl_src()
expect(src.contains("fn build_compiler_rt(triple: text)")).to_equal(true)
```

</details>

#### exports build_compiler_rt_for_target

- exports build_compiler_rt_for_target
   - Expected: src contains `fn build_compiler_rt_for_target`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exports build_compiler_rt_for_target")
"""Internal per-target helper must also be exposed for callers/tests."""
val src = build_spl_src()
expect(src.contains("fn build_compiler_rt_for_target")).to_equal(true)
```

</details>

#### registers compiler-rt subcommand in cross_build_main

- registers compiler-rt subcommand in cross_build_main
   - Expected: src contains `"compiler-rt"`
   - Expected: src contains `subcommand`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("registers compiler-rt subcommand in cross_build_main")
"""The new `compiler-rt` subcommand keyword must be wired up."""
val src = build_spl_src()
expect(src.contains("\"compiler-rt\"")).to_equal(true)
expect(src.contains("subcommand")).to_equal(true)
```

</details>

#### exposes --print-plan CLI flag

- exposes --print-plan CLI flag
   - Expected: src contains `--print-plan`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("exposes --print-plan CLI flag")
val src = build_spl_src()
expect(src.contains("--print-plan")).to_equal(true)
```

</details>

#### stages builtins into clang resource dir

- stages builtins into clang resource dir
   - Expected: src contains `lib/clang/`
   - Expected: src contains `CLANG_RESOURCE_VERSION`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("stages builtins into clang resource dir")
val src = build_spl_src()
expect(src.contains("lib/clang/")).to_equal(true)
expect(src.contains("CLANG_RESOURCE_VERSION")).to_equal(true)
```

</details>

#### gates compiler-rt behind -simpleos triples

- gates compiler-rt behind -simpleos triples
   - Expected: src contains `ends_with("-simpleos")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("gates compiler-rt behind -simpleos triples")
val src = build_spl_src()
expect(src.contains("ends_with(\"-simpleos\")")).to_equal(true)
```

</details>

#### per-target build dir is cross-<triple>

- per-target build dir is cross-<triple>
   - Expected: src contains `cross-{{triple}}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("per-target build dir is cross-<triple>")
val src = build_spl_src()
expect(src.contains("cross-{{triple}}")).to_equal(true)
```

</details>

#### compiler-rt build dir is compiler-rt-<triple>

- compiler-rt build dir is compiler-rt-<triple>
   - Expected: src contains `compiler-rt-{{triple}}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiler-rt build dir is compiler-rt-<triple>")
val src = build_spl_src()
expect(src.contains("compiler-rt-{{triple}}")).to_equal(true)
```

</details>

#### build.shs threads SIMPLEOS_TARGET_TRIPLE

- build.shs threads SIMPLEOS_TARGET_TRIPLE
   - Expected: src contains `SIMPLEOS_TARGET_TRIPLE`
   - Expected: src contains `SIMPLE_TARGET`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("build.shs threads SIMPLEOS_TARGET_TRIPLE")
val src = build_shs_src()
expect(src.contains("SIMPLEOS_TARGET_TRIPLE")).to_equal(true)
expect(src.contains("SIMPLE_TARGET")).to_equal(true)
```

</details>

#### build.shs uses per-triple CROSS_DIR / RT_DIR

- build.shs uses per-triple CROSS_DIR / RT_DIR
   - Expected: src contains `CROSS_DIR=`
   - Expected: src contains `RT_DIR=`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("build.shs uses per-triple CROSS_DIR / RT_DIR")
val src = build_shs_src()
expect(src.contains("CROSS_DIR=")).to_equal(true)
expect(src.contains("RT_DIR=")).to_equal(true)
```

</details>

#### build.shs still dispatches compiler-rt subcommand

- build.shs still dispatches compiler-rt subcommand
   - Expected: src contains `compiler-rt)`
   - Expected: src contains `stage3_compiler_rt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("build.shs still dispatches compiler-rt subcommand")
val src = build_shs_src()
expect(src.contains("compiler-rt)")).to_equal(true)
expect(src.contains("stage3_compiler_rt")).to_equal(true)
```

</details>

#### build.shs stages builtins into resource dir

- build.shs stages builtins into resource dir
   - Expected: src contains `RES_LIB_DIR`
   - Expected: src contains `lib/clang/`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("build.shs stages builtins into resource dir")
val src = build_shs_src()
expect(src.contains("RES_LIB_DIR")).to_equal(true)
expect(src.contains("lib/clang/")).to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake exists

- compiler_rt_cmake.cmake exists
   - Expected: fs.file_exists(RT_CMAKE) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiler_rt_cmake.cmake exists")
expect(fs.file_exists(RT_CMAKE)).to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake enables COMPILER_RT_BUILD_BUILTINS

- compiler_rt_cmake.cmake enables COMPILER_RT_BUILD_BUILTINS
   - Expected: src contains `COMPILER_RT_BUILD_BUILTINS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiler_rt_cmake.cmake enables COMPILER_RT_BUILD_BUILTINS")
val src = rt_cmake_src()
expect(src.contains("COMPILER_RT_BUILD_BUILTINS")).to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake disables sanitizers / xray / profile

- compiler_rt_cmake.cmake disables sanitizers / xray / profile
   - Expected: src contains `COMPILER_RT_BUILD_SANITIZERS`
   - Expected: src contains `COMPILER_RT_BUILD_XRAY`
   - Expected: src contains `COMPILER_RT_BUILD_PROFILE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiler_rt_cmake.cmake disables sanitizers / xray / profile")
val src = rt_cmake_src()
expect(src.contains("COMPILER_RT_BUILD_SANITIZERS")).to_equal(true)
expect(src.contains("COMPILER_RT_BUILD_XRAY")).to_equal(true)
expect(src.contains("COMPILER_RT_BUILD_PROFILE")).to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake sets COMPILER_RT_OS_DIR to simpleos

- compiler_rt_cmake.cmake sets COMPILER_RT_OS_DIR to simpleos
   - Expected: src contains `COMPILER_RT_OS_DIR simpleos`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("compiler_rt_cmake.cmake sets COMPILER_RT_OS_DIR to simpleos")
val src = rt_cmake_src()
expect(src.contains("COMPILER_RT_OS_DIR simpleos")).to_equal(true)
```

</details>

#### SimpleOS ToolChain README exists

- SimpleOS ToolChain README exists
   - Expected: fs.file_exists(TOOLCHAIN_README) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("SimpleOS ToolChain README exists")
expect(fs.file_exists(TOOLCHAIN_README)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/os/port/llvm/per_target_build_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS LLVM per-target build (A4/A5).
- SimpleOS LLVM per-target build (A4/A5)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a7824174c06f0ce3b788ecb2d687268d8f6a595a520417d19e7812fce949e818`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a7824174c06f0ce3b788ecb2d687268d8f6a595a520417d19e7812fce949e818`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a7824174c06f0ce3b788ecb2d687268d8f6a595a520417d19e7812fce949e818`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/os/port/llvm/per_target_build_spec.spl
mirror: doc/06_spec/integration/os/port/llvm/per_target_build_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/os/port/llvm/per_target_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/os/port/llvm/per_target_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/os/port/llvm/per_target_build_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares CROSS_SUPPORTED_TARGETS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/llvm/per_target_build_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CROSS_SUPPORTED_TARGETS lists all four SimpleOS triples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/llvm/per_target_build_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'honours SIMPLE_TARGET env override' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
