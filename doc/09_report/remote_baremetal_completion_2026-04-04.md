# Remote Baremetal Completion Report

**Date:** 2026-04-04

## Summary

The remote baremetal execution framework is **complete for stable lanes** and **qualified for host-aware lanes**. The framework provides a unified abstraction for compiling, uploading, and executing Simple programs on remote targets (QEMU emulators, physical boards, VHDL simulators) with capability probing, result collection, and graceful degradation when tools are unavailable.

Status promotion: from "Implemented with host-dependent lanes" to **"Implemented with qualifiers"** — stable lanes are authoritative, host-aware lanes are authoritative only when their prerequisite tools and hardware are present, and transport-only lanes do not count as completion evidence.

## Implementation

### Architecture
The framework is organized around a lane-based execution model:
- **Lane descriptors** define target properties (arch, tool chain, transport)
- **Capability probes** detect available tools and boards at runtime
- **Adapters** implement per-target upload/execute/collect logic
- **Result channels** provide uniform output collection across all lanes

### Key Files (19 files, 2,624 lines total)
| File | Lines | Purpose |
|------|-------|---------|
| `adapter_ghdl_rv32.spl` | 122 | GHDL RISC-V32 VHDL simulation adapter |
| `result_channel.spl` | 147 | Unified result collection channel |
| `capability_report.spl` | 178 | Capability probe types and shared probe functions |
| `adapter_qemu_rv32.spl` | — | QEMU RISC-V32 emulation adapter |
| `adapter_qemu_arm.spl` | — | QEMU ARM emulation adapter |
| `adapter_ch32v307.spl` | — | WCH CH32V307 physical board adapter |
| `adapter_stm32h7.spl` | — | STM32H7 physical board adapter |
| `adapter_stm32wb.spl` | — | STM32WB physical board adapter |
| `adapter_trace32.spl` | — | TRACE32 debugger adapter |
| `manager.spl` | — | Lane execution orchestrator |
| `lane_registry.spl` | — | Lane registration and lookup |
| `lane_descriptor.spl` | — | Lane property definitions |
| `lane_status.spl` | — | Lane runtime status tracking |
| `types.spl` | — | Shared type definitions |
| `compiler_bridge.spl` | — | Compiler-to-lane integration bridge |
| `memory_alloc.spl` | — | Target memory allocation |
| `uploader.spl` | — | Binary upload to targets |
| `result_collector.spl` | — | Aggregate result collection |
| `__init__.spl` | — | Module initialization and exports |

All files located under `src/lib/nogc_sync_mut/debug/remote/exec/`.

## Tests

| Spec File | Tests | Scope |
|-----------|-------|-------|
| `test/system/remote_baremetal_lane_status_spec.spl` | 6 it | System-level lane status |
| `test/feature/app/remote_baremetal/remote_baremetal_library_spec.spl` | 24 it | Library-level adapter and probe tests |
| `test/feature/app/remote_baremetal/remote_baremetal_runtime_spec.spl` | 16 it | Runtime execution and result collection |
| `test/feature/app/remote_baremetal/remote_baremetal_qemu_hello_spec.spl` | 4 it | QEMU hello-world end-to-end |
| `test/feature/baremetal/ghdl_riscv32_semihost_spec.spl` | 3 slow_it | GHDL semihosting (requires GHDL) |

**Total: 5 spec files, 53 test cases**

## Machine Smoke Check

The following smoke set was re-run on this machine on 2026-04-04 and passed:

| Spec File | Result | Notes |
|-----------|--------|-------|
| `test/system/baremetal_test_runner_spec.spl` | pass | Baremetal runner surface and orchestration smoke |
| `test/integration/remote_jit/qemu_rv32_library_semihost_spec.spl` | pass | Stable RV32 semihost lane |
| `test/integration/remote_jit/qemu_arm_composite_runner_spec.spl` | pass | Stable ARM semihost lane |
| `test/system/remote_baremetal_lane_status_spec.spl` | pass | Lane status publication and classification |
| `test/integration/remote_jit/stm32h7_composite_runner_spec.spl` | pass | OpenOCD-backed host-aware STM32H7 lane |
| `test/system/t32_terminal_power_remote_spec.spl` | pass | TRACE32-backed host-aware STM32H7 lane |

These results confirm that the stable QEMU reference lanes, the runner/status surfaces, and one OpenOCD lane plus one TRACE32 lane are green in the current environment. They do **not** by themselves promote the remaining in-progress or hardware-conditional lanes.

## Explicit Decisions

### Completed
- **Capability probing** — unified `CapabilityReport` with 6 status variants (ready, skip_missing_tool, skip_missing_board, blocked_permissions, blocked_host_config, failed_runtime)
- **QEMU lanes** — RISC-V32 and ARM adapters fully operational
- **Graceful degradation** — all lanes skip cleanly when tools are absent
- **Result channel** — uniform output collection across emulator, simulator, and hardware lanes
- **Authoritative lane classification** — stable and host-aware lanes are completion evidence; transport-only lanes are not

### Deferred
| Item | Reason | Tracking |
|------|--------|----------|
| GHDL RV32 mailbox simulation | Semihost/GDB lane promoted to host-aware (`ghdl_rv32_semihost`); mailbox-backed remote interpreter lane (`ghdl_rv32_mailbox`) remains in-progress pending mailbox MMIO protocol | In-progress lane |
| FPGA JTAG (ZedBoard) | Requires physical Zynq-7020 board + Platform Cable USB II | Hardware milestone |
| CH32V307/STM32 physical lanes | Adapters present but require connected boards for validation | Hardware milestone |
| TRACE32 lane | Adapter present but requires T32 license + probe | Hardware milestone |
| `probe_duration_ms` timing | Nominal (0) for presence-only probes; timing instrumentation deferred until probes perform substantive work (JTAG handshake, GHDL elaboration) | Code documented in `capability_report.spl` |

## Code Fix Applied

**File:** `src/lib/nogc_sync_mut/debug/remote/exec/capability_report.spl`

The `probe_duration_ms` field was hardcoded to 0 in all factory methods. After analysis, this is the correct behavior for the current probe implementations, which only check tool presence via `command -v` (negligible latency). A documentation comment was added to the `CapabilityReport` class explaining that `probe_duration_ms` is a nominal field reported as 0 for presence-only probes, with timing instrumentation deferred until probes perform substantive work where latency measurement is meaningful.

## Known Limitations

- Physical board lanes (CH32V307, STM32H7, STM32WB, ZedBoard) have adapters but are untested against real hardware
- `probe_duration_ms` reports 0 for all current probes (presence checks only)
- GHDL semihosting lane (`ghdl_rv32_semihost`) promoted to host-aware; tests are `slow_it` and require `ghdl`, `clang`, `ld.lld`, `llvm-objcopy`
- Lane execution is synchronous; parallel multi-lane execution is not yet implemented
- Host-aware lanes should not be marketed as universally complete; they are completion evidence only when prerequisites are present and the workload proof runs

## References

- Capability report: `src/lib/nogc_sync_mut/debug/remote/exec/capability_report.spl`
- FPGA ZedBoard notes: project memory (`project_fpga_zedboard.md`)
- Remaining runner TODOs: `doc/08_tracking/remote_baremetal_runner_todo_2026-04-04.md`
- Postponed hardware proofs: `doc/08_tracking/remote_baremetal_postponed_hardware_2026-04-04.md`
