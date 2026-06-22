# Remote Interpreter Backend Specification

> <details>

<!-- sdn-diagram:id=remote_interpreter_backend_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=remote_interpreter_backend_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

remote_interpreter_backend_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=remote_interpreter_backend_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Remote Interpreter Backend Specification

## Scenarios

### Remote interpreter backend routing

#### extracts interpreter as the base runtime for T32 remote specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_base_runtime(spec)).to_equal("interpreter")
```

</details>

#### extracts remote as the platform layer for T32 remote specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_platform_layer(spec)).to_equal("remote")
```

</details>

#### extracts arm32 as the effective architecture for T32 remote specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_arch_from_spec(spec)).to_equal("arm32")
```

</details>

#### extracts t32 as the remote backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_remote_backend(spec)).to_equal("t32")
```

</details>

#### maps t32 stm32 targets to the trace32 board target

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(t32(stm32wb)))"
expect(extract_target_from_spec(spec)).to_equal("trace32_stm32wb")
```

</details>

#### extracts openocd as the remote backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(openocd(stm32wb)))"
expect(extract_remote_backend(spec)).to_equal("openocd")
```

</details>

#### extracts ghdl as the remote backend

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(baremetal(ghdl(riscv32))))"
expect(extract_remote_backend(spec)).to_equal("ghdl")
```

</details>

#### maps ghdl riscv32 specs to the ghdl rv32 target

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(baremetal(ghdl(riscv32))))"
expect(extract_target_from_spec(spec)).to_equal("ghdl_rv32")
expect(extract_arch_from_spec(spec)).to_equal("riscv32")
```

</details>

#### returns empty backend for legacy remote specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(arm32))"
expect(extract_remote_backend(spec)).to_equal("")
```

</details>

#### keeps qemu target resolution for legacy riscv32 remote specs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val spec = "interpreter(remote(baremetal(riscv32)))"
expect(extract_target_from_spec(spec)).to_equal("riscv32")
expect(qemu_binary_for_arch("riscv32")).to_equal("qemu-system-riscv32")
expect(qemu_machine_for_arch("riscv32")).to_equal("virt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/remote_interpreter_backend_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Remote interpreter backend routing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
