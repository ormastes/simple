# Remote Interpreter Backend Specification

> Tests covering Remote interpreter backend routing, GPU remote backend routing (design doc §2.2).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Interpreter Backend Specification

## Scenarios

### Remote interpreter backend routing

#### extracts interpreter as the base runtime for T32 remote specs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- extracts interpreter as the base runtime for T32 remote specs
   - Expected: extract_base_runtime(spec) equals `interpreter`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts interpreter as the base runtime for T32 remote specs")
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
```

</details>

#### extracts remote as the platform layer for T32 remote specs

- extracts remote as the platform layer for T32 remote specs
   - Expected: extract_platform_layer(spec) equals `remote`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts remote as the platform layer for T32 remote specs")
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_platform_layer(spec)).to_equal("remote")
```

</details>

#### extracts arm32 as the effective architecture for T32 remote specs

- extracts arm32 as the effective architecture for T32 remote specs
   - Expected: extract_arch_from_spec(spec) equals `arm32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts arm32 as the effective architecture for T32 remote specs")
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_arch_from_spec(spec)).to_equal("arm32")
```

</details>

#### extracts t32 as the remote backend

- extracts t32 as the remote backend
   - Expected: extract_remote_backend(spec) equals `t32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts t32 as the remote backend")
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_remote_backend(spec)).to_equal("t32")
```

</details>

#### maps t32 stm32 targets to the trace32 board target

- maps t32 stm32 targets to the trace32 board target
   - Expected: extract_target_from_spec(spec) equals `trace32_stm32wb`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps t32 stm32 targets to the trace32 board target")
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_target_from_spec(spec)).to_equal("trace32_stm32wb")
```

</details>

#### extracts openocd as the remote backend

- extracts openocd as the remote backend
   - Expected: extract_remote_backend(spec) equals `openocd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts openocd as the remote backend")
val spec = "interpreter(remote(openocd(stm32wb)))"
expect(extract_remote_backend(spec)).to_equal("openocd")
```

</details>

#### extracts ghdl as the remote backend

- extracts ghdl as the remote backend
   - Expected: extract_remote_backend(spec) equals `ghdl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts ghdl as the remote backend")
val spec = "interpreter(remote(baremetal(ghdl(riscv32))))"
expect(extract_remote_backend(spec)).to_equal("ghdl")
```

</details>

#### maps ghdl riscv32 specs to the ghdl rv32 target

- maps ghdl riscv32 specs to the ghdl rv32 target
   - Expected: extract_target_from_spec(spec) equals `ghdl_rv32`
   - Expected: extract_arch_from_spec(spec) equals `riscv32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps ghdl riscv32 specs to the ghdl rv32 target")
val spec = "interpreter(remote(baremetal(ghdl(riscv32))))"
expect(extract_target_from_spec(spec)).to_equal("ghdl_rv32")
expect(extract_arch_from_spec(spec)).to_equal("riscv32")
```

</details>

#### returns empty backend for legacy remote specs

- returns empty backend for legacy remote specs
   - Expected: extract_remote_backend(spec) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty backend for legacy remote specs")
val spec = "interpreter(remote(arm32))"
expect(extract_remote_backend(spec)).to_equal("")
```

</details>

#### keeps qemu target resolution for legacy riscv32 remote specs

- keeps qemu target resolution for legacy riscv32 remote specs
   - Expected: extract_target_from_spec(spec) equals `riscv32`
   - Expected: qemu_binary_for_arch("riscv32") equals `qemu-system-riscv32`
   - Expected: qemu_machine_for_arch("riscv32") equals `virt`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps qemu target resolution for legacy riscv32 remote specs")
val spec = "interpreter(remote(baremetal(riscv32)))"
expect(extract_target_from_spec(spec)).to_equal("riscv32")
expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
expect(qemu_machine_for_arch("riscv32")).to_equal("virt")
```

</details>

### GPU remote backend routing (design doc §2.2)

#### routes jit(remote(cuda(sm80))) as a JIT-base cuda spec

- routes jit(remote(cuda(sm80))) as a JIT-base cuda spec
   - Expected: extract_base_runtime(spec) equals `jit`
   - Expected: extract_platform_layer(spec) equals `remote`
   - Expected: extract_remote_backend(spec) equals `cuda`
   - Expected: extract_arch_from_spec(spec) equals `ptx64`
   - Expected: extract_target_from_spec(spec) equals `cuda_sm80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes jit(remote(cuda(sm80))) as a JIT-base cuda spec")
val spec = "jit(remote(cuda(sm80)))"
expect(extract_base_runtime(spec)).to_equal("jit")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_remote_backend(spec)).to_equal("cuda")
expect(extract_arch_from_spec(spec)).to_equal("ptx64")
expect(extract_target_from_spec(spec)).to_equal("cuda_sm80")
```

</details>

#### defaults interpreter(remote(cuda(sm80))) to the launch submode

- defaults interpreter(remote(cuda(sm80))) to the launch submode
   - Expected: extract_base_runtime(spec) equals `interpreter`
   - Expected: extract_remote_backend(spec) equals `cuda`
   - Expected: extract_arch_from_spec(spec) equals `ptx64`
   - Expected: extract_target_from_spec(spec) equals `cuda_sm80`
   - Expected: extract_gpu_submode(spec) equals `launch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defaults interpreter(remote(cuda(sm80))) to the launch submode")
val spec = "interpreter(remote(cuda(sm80)))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
expect(extract_remote_backend(spec)).to_equal("cuda")
expect(extract_arch_from_spec(spec)).to_equal("ptx64")
expect(extract_target_from_spec(spec)).to_equal("cuda_sm80")
expect(extract_gpu_submode(spec)).to_equal("launch")
```

</details>

#### routes interpreter(remote(cuda(sm80(resident)))) to the resident submode

- routes interpreter(remote(cuda(sm80(resident)))) to the resident submode
   - Expected: extract_remote_backend(spec) equals `cuda`
   - Expected: extract_target_from_spec(spec) equals `cuda_sm80`
   - Expected: extract_gpu_submode(spec) equals `resident`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes interpreter(remote(cuda(sm80(resident)))) to the resident submode")
val spec = "interpreter(remote(cuda(sm80(resident))))"
expect(extract_remote_backend(spec)).to_equal("cuda")
expect(extract_target_from_spec(spec)).to_equal("cuda_sm80")
expect(extract_gpu_submode(spec)).to_equal("resident")
```

</details>

#### routes jit(remote(vulkan(spv15))) as a JIT-base vulkan spec

- routes jit(remote(vulkan(spv15))) as a JIT-base vulkan spec
   - Expected: extract_base_runtime(spec) equals `jit`
   - Expected: extract_remote_backend(spec) equals `vulkan`
   - Expected: extract_arch_from_spec(spec) equals `spirv`
   - Expected: extract_target_from_spec(spec) equals `vulkan_spv15`
   - Expected: extract_gpu_submode(spec) equals `dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes jit(remote(vulkan(spv15))) as a JIT-base vulkan spec")
val spec = "jit(remote(vulkan(spv15)))"
expect(extract_base_runtime(spec)).to_equal("jit")
expect(extract_remote_backend(spec)).to_equal("vulkan")
expect(extract_arch_from_spec(spec)).to_equal("spirv")
expect(extract_target_from_spec(spec)).to_equal("vulkan_spv15")
expect(extract_gpu_submode(spec)).to_equal("dispatch")
```

</details>

#### always dispatches interpreter(remote(vulkan(spv15)))

- always dispatches interpreter(remote(vulkan(spv15)))
   - Expected: extract_remote_backend(spec) equals `vulkan`
   - Expected: extract_target_from_spec(spec) equals `vulkan_spv15`
   - Expected: extract_gpu_submode(spec) equals `dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("always dispatches interpreter(remote(vulkan(spv15)))")
val spec = "interpreter(remote(vulkan(spv15)))"
expect(extract_remote_backend(spec)).to_equal("vulkan")
expect(extract_target_from_spec(spec)).to_equal("vulkan_spv15")
expect(extract_gpu_submode(spec)).to_equal("dispatch")
```

</details>

#### accepts any smNN token and forwards it into the target id

- accepts any smNN token and forwards it into the target id
   - Expected: extract_target_from_spec("interpreter(remote(cuda(sm90)))") equals `cuda_sm90`
   - Expected: extract_arch_from_spec("interpreter(remote(cuda(sm90)))") equals `ptx64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts any smNN token and forwards it into the target id")
expect(extract_target_from_spec("interpreter(remote(cuda(sm90)))")).to_equal("cuda_sm90")
expect(extract_arch_from_spec("interpreter(remote(cuda(sm90)))")).to_equal("ptx64")
```

</details>

#### accepts spv13..spv16 tokens and forwards them into the target id

- accepts spv13..spv16 tokens and forwards them into the target id
   - Expected: extract_target_from_spec("interpreter(remote(vulkan(spv13)))") equals `vulkan_spv13`
   - Expected: extract_target_from_spec("interpreter(remote(vulkan(spv16)))") equals `vulkan_spv16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts spv13..spv16 tokens and forwards them into the target id")
expect(extract_target_from_spec("interpreter(remote(vulkan(spv13)))")).to_equal("vulkan_spv13")
expect(extract_target_from_spec("interpreter(remote(vulkan(spv16)))")).to_equal("vulkan_spv16")
```

</details>

#### routes the exploratory cuda-gdb semihost lane token (parse-only)

- routes the exploratory cuda-gdb semihost lane token (parse-only)
   - Expected: extract_remote_backend(spec) equals `cudagdb`
   - Expected: extract_arch_from_spec(spec) equals `ptx64`
   - Expected: extract_target_from_spec(spec) equals `cudagdb_sm80`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes the exploratory cuda-gdb semihost lane token (parse-only)")
val spec = "interpreter(remote(cudagdb(sm80)))"
expect(extract_remote_backend(spec)).to_equal("cudagdb")
expect(extract_arch_from_spec(spec)).to_equal("ptx64")
expect(extract_target_from_spec(spec)).to_equal("cudagdb_sm80")
```

</details>

#### rejects resident submode under vulkan with the forward-progress diagnostic

- rejects resident submode under vulkan with the forward-progress diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects resident submode under vulkan with the forward-progress diagnostic")
val spec = "interpreter(remote(vulkan(spv15(resident))))"
expect(extract_gpu_submode(spec)).to_equal(
    "resident submode requires forward-progress guarantees; vulkan lanes are per-dispatch (see gpu_remote_interpreter_architecture.md §6.3)")
```

</details>

#### routes interpreter(remote(metal(msl2))) as a dispatch-submode metal spec

- routes interpreter(remote(metal(msl2))) as a dispatch-submode metal spec
   - Expected: extract_base_runtime(spec) equals `interpreter`
   - Expected: extract_platform_layer(spec) equals `remote`
   - Expected: extract_remote_backend(spec) equals `metal`
   - Expected: extract_arch_from_spec(spec) equals `msl`
   - Expected: extract_target_from_spec(spec) equals `metal_msl2`
   - Expected: extract_gpu_submode(spec) equals `dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes interpreter(remote(metal(msl2))) as a dispatch-submode metal spec")
val spec = "interpreter(remote(metal(msl2)))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
expect(extract_platform_layer(spec)).to_equal("remote")
expect(extract_remote_backend(spec)).to_equal("metal")
expect(extract_arch_from_spec(spec)).to_equal("msl")
expect(extract_target_from_spec(spec)).to_equal("metal_msl2")
expect(extract_gpu_submode(spec)).to_equal("dispatch")
```

</details>

#### routes jit(remote(metal(msl2))) as a JIT-base metal spec

- routes jit(remote(metal(msl2))) as a JIT-base metal spec
   - Expected: extract_base_runtime(spec) equals `jit`
   - Expected: extract_remote_backend(spec) equals `metal`
   - Expected: extract_arch_from_spec(spec) equals `msl`
   - Expected: extract_target_from_spec(spec) equals `metal_msl2`
   - Expected: extract_gpu_submode(spec) equals `dispatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("routes jit(remote(metal(msl2))) as a JIT-base metal spec")
val spec = "jit(remote(metal(msl2)))"
expect(extract_base_runtime(spec)).to_equal("jit")
expect(extract_remote_backend(spec)).to_equal("metal")
expect(extract_arch_from_spec(spec)).to_equal("msl")
expect(extract_target_from_spec(spec)).to_equal("metal_msl2")
expect(extract_gpu_submode(spec)).to_equal("dispatch")
```

</details>

#### rejects resident submode under metal with the forward-progress diagnostic

- rejects resident submode under metal with the forward-progress diagnostic


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects resident submode under metal with the forward-progress diagnostic")
val spec = "interpreter(remote(metal(msl2(resident))))"
expect(extract_gpu_submode(spec)).to_equal(
    "resident submode requires forward-progress guarantees; metal lanes are per-dispatch (see metal_gpu_lane_and_vulkan_jit_notebook_architecture_2026-08-09.md §1)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/remote_interpreter_backend_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Remote interpreter backend routing, GPU remote backend routing (design doc §2.2).
- Remote interpreter backend routing
- GPU remote backend routing (design doc §2.2)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bad055374f58b289c057d2915d2a1159827d8ff4dca7bae9f5e38e81c94da4b6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bad055374f58b289c057d2915d2a1159827d8ff4dca7bae9f5e38e81c94da4b6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bad055374f58b289c057d2915d2a1159827d8ff4dca7bae9f5e38e81c94da4b6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/compiler/remote_interpreter_backend_spec.spl
mirror: doc/06_spec/03_system/compiler/remote_interpreter_backend_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/compiler/remote_interpreter_backend_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/compiler/remote_interpreter_backend_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/compiler/remote_interpreter_backend_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts interpreter as the base runtime for T32 remote specs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/remote_interpreter_backend_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts remote as the platform layer for T32 remote specs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/compiler/remote_interpreter_backend_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts arm32 as the effective architecture for T32 remote specs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
