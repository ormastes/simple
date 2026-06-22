# Per Target Build Specification

> _Scaffolding checks for the multi-target cross-build + compiler-rt stage._

<!-- sdn-diagram:id=per_target_build_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=per_target_build_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

per_target_build_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=per_target_build_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Per Target Build Specification

## Scenarios

### SimpleOS LLVM per-target build (A4/A5)
_Scaffolding checks for the multi-target cross-build + compiler-rt stage._

#### declares CROSS_SUPPORTED_TARGETS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("val CROSS_SUPPORTED_TARGETS").to_equal(true)
```

</details>

#### CROSS_SUPPORTED_TARGETS lists all four SimpleOS triples

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("x86_64-unknown-simpleos").to_equal(true)
src.contains("aarch64-unknown-simpleos").to_equal(true)
src.contains("riscv64gc-unknown-simpleos").to_equal(true)
src.contains("riscv32imac-unknown-simpleos").to_equal(true)
```

</details>

#### honours SIMPLE_TARGET env override

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("SIMPLE_TARGET").to_equal(true)
src.contains("cross_selected_targets").to_equal(true)
```

</details>

#### cross_build_all iterates CROSS_SUPPORTED_TARGETS

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("fn cross_build_all").to_equal(true)
src.contains("cross_build_stage_for_target").to_equal(true)
```

</details>

#### exports build_compiler_rt(triple)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("fn build_compiler_rt(triple: text)").to_equal(true)
```

</details>

#### exports build_compiler_rt_for_target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("fn build_compiler_rt_for_target").to_equal(true)
```

</details>

#### registers compiler-rt subcommand in cross_build_main

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("\"compiler-rt\"").to_equal(true)
src.contains("subcommand").to_equal(true)
```

</details>

#### exposes --print-plan CLI flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("--print-plan").to_equal(true)
```

</details>

#### stages builtins into clang resource dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("lib/clang/").to_equal(true)
src.contains("CLANG_RESOURCE_VERSION").to_equal(true)
```

</details>

#### gates compiler-rt behind -simpleos triples

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("ends_with(\"-simpleos\")").to_equal(true)
```

</details>

#### per-target build dir is cross-<triple>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("cross-{triple}").to_equal(true)
```

</details>

#### compiler-rt build dir is compiler-rt-<triple>

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_spl_src()
src.contains("compiler-rt-{triple}").to_equal(true)
```

</details>

#### build.shs threads SIMPLEOS_TARGET_TRIPLE

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
src.contains("SIMPLEOS_TARGET_TRIPLE").to_equal(true)
src.contains("SIMPLE_TARGET").to_equal(true)
```

</details>

#### build.shs uses per-triple CROSS_DIR / RT_DIR

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
src.contains("CROSS_DIR=").to_equal(true)
src.contains("RT_DIR=").to_equal(true)
```

</details>

#### build.shs still dispatches compiler-rt subcommand

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
src.contains("compiler-rt)").to_equal(true)
src.contains("stage3_compiler_rt").to_equal(true)
```

</details>

#### build.shs stages builtins into resource dir

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = build_shs_src()
src.contains("RES_LIB_DIR").to_equal(true)
src.contains("lib/clang/").to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs.exists(RT_CMAKE).to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake enables COMPILER_RT_BUILD_BUILTINS

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_cmake_src()
src.contains("COMPILER_RT_BUILD_BUILTINS").to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake disables sanitizers / xray / profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_cmake_src()
src.contains("COMPILER_RT_BUILD_SANITIZERS").to_equal(true)
src.contains("COMPILER_RT_BUILD_XRAY").to_equal(true)
src.contains("COMPILER_RT_BUILD_PROFILE").to_equal(true)
```

</details>

#### compiler_rt_cmake.cmake sets COMPILER_RT_OS_DIR to simpleos

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_cmake_src()
src.contains("COMPILER_RT_OS_DIR simpleos").to_equal(true)
```

</details>

#### SimpleOS ToolChain README exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fs.exists(TOOLCHAIN_README).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/02_integration/os/port/llvm/per_target_build_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
