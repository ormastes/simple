# Remote Baremetal Runtime Checks

Checks the current remote baremetal execution plumbing used by the Simple test runner. The spec covers:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #RBRT-001 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | [doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md](doc/03_plan/remote_baremetal_remaining_without_trace32_2026-03-24.md) |
| Design | [doc/05_design/remote_jit_architecture.md](doc/05_design/remote_jit_architecture.md) |
| Research | [doc/01_research/trace32_remote_interfaces_2026-03-08.md](doc/01_research/trace32_remote_interfaces_2026-03-08.md) |
| Source | `/home/ormastes/dev/pub/simple/test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` |
| Updated | 2026-03-31 |
| Generator | `simple sspec-docgen` (Rust) |

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

## Overview

Checks the current remote baremetal execution plumbing used by the Simple test
runner. The spec covers:

- composite mode parsing for `interpreter(remote(baremetal(...)))`
- QEMU RISC-V32 remote debug smoke using a temporary ELF plus GDB memory read
- CH32V307 direct `wlink` readiness and register or memory access checks
- TRACE32 readiness state through `t32rem` discovery and repo-managed config

This spec is intentionally host-aware. It treats missing optional host tools as
`skip:` and host/runtime blockers as `blocked:` so the test captures current
environment state without claiming a full hardware verification that the repo
does not currently provide.

## Syntax

```simple
val spec = "interpreter(remote(baremetal(riscv32)))"
val base = extract_base_runtime(spec)
val layer = extract_platform_layer(spec)
val arch = extract_arch_from_spec(spec)
```

## Examples

```simple
val qemu_status = qemu_riscv32_remote_memory_status()
val t32_status = trace32_remote_status()
expect(status_is_acceptable(t32_status)).to_equal(true)
```

## Scenarios

- extracts runtime, platform, and arch from nested remote spec
- preserves nested jit stm32h7 mode strings
- maps riscv32 to qemu-system-riscv32 and virt machine
- finds the checked-in rv32 baremetal elf fixture
- can build a temporary rv32 elf and read memory through gdb remote
- resolves to a non-error readiness state
- reports openocd readiness for stm targets without treating host blockers as hard failures
- reports st-link tools readiness for stm targets without treating host blockers as hard failures
- detects CH32V307 through wlink status
- reads CH32V307 registers through wlink
- reads CH32V307 flash memory through wlink
- reads CH32V307 RAM through wlink
- keeps CH32 composite execution and RV32 raw injected execution as separate specs
- reads the H7 cpuid through openocd plus gdb
- reads the WB cpuid through openocd plus gdb
- reads the H7 cpuid through st-link tools
- reads the WB cpuid through st-link tools
