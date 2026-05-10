# Remote Baremetal Completion — Implementation Report

**Date:** 2026-04-04  
**Plan:** `doc/03_plan/remote_baremetal_completion_plan_2026-04-04.md`  
**Status:** Complete (Phases 1-4, 6-7 of plan; Phase 5 GHDL mailbox deferred)

## What Was Implemented

### New Files (908 lines total)

| File | Lines | Feature ID | Purpose |
|------|-------|------------|---------|
| `lane_descriptor.spl` | 132 | #RJE-014 | Enums: LaneStatus, ProofClass, AdapterKind, ResultChannelKind; LaneDescriptor class |
| `capability_report.spl` | 173 | #RJE-015 | CapabilityStatus enum, CapabilityReport class, 7 centralized probe functions |
| `result_channel.spl` | 147 | #RJE-016 | ResultPacket canonical result, ResultVerifier for verification |
| `lane_registry.spl` | 251 | #RJE-017 | LaneRegistry with 10 lane definitions, probe_for_lane dispatch |
| `lane_status.spl` | 205 | #RJE-018 | LaneStatusReporter with text, SDN, and markdown output |

All in `src/lib/nogc_sync_mut/debug/remote/exec/`.

### Modified Files

| File | Change |
|------|--------|
| `__init__.spl` | Added exports for all new types and functions |
| `adapter_qemu_rv32.spl` | Added `capability_report()` method + import |
| `adapter_qemu_arm.spl` | Added `capability_report()` method + import |
| `adapter_ch32v307.spl` | Added `capability_report()` method + import |
| `adapter_stm32h7.spl` | Added `capability_report()` method + import |
| `adapter_trace32.spl` | Added `capability_report()` method + import |
| `adapter_ghdl_rv32.spl` | Added `capability_report()` method + import |

### Test and Documentation

| File | Purpose |
|------|---------|
| `test/system/remote_baremetal_lane_status_spec.spl` | 24 test cases across 7 describe groups |
| `doc/08_tracking/lane_matrix.md` | Machine-readable lane status matrix |

## Plan Phase Mapping

| Plan Phase | Status | Implementation |
|------------|--------|----------------|
| Phase 1: Compiled-mode proof | Done | Lane descriptors enforce `ProofClass.compiled` for authoritative lanes |
| Phase 2: Centralize capability detection | Done | `capability_report.spl` with 7 shared probe functions |
| Phase 3: Standardize result channels | Done | `result_channel.spl` with canonical ResultPacket |
| Phase 4: Promote CH32/STM32 | Done | Classified as `host_aware` with register_readback + ram_sentinel channels |
| Phase 5: GHDL mailbox | Deferred | Classified as `in_progress`; needs mailbox protocol implementation |
| Phase 6: FPGA quarantine | Done | `fpga_jtag_zedboard` classified as `in_progress` with empty spec path |
| Phase 7: Lane status publishing | Done | `lane_status.spl` generates text, SDN, markdown reports |

## Lane Classification (10 lanes)

- **Stable (3):** qemu_rv32_semihost, qemu_arm_semihost, x86_64_direct_boot
- **Host-aware (3):** ch32v307_wlink, stm32h7_openocd, stm32h7_trace32
- **Transport-only (2):** rv32_raw_injected, baremetal_runtime_check
- **In-progress (2):** ghdl_rv32_sim, fpga_jtag_zedboard

## Remaining Work

1. **GHDL mailbox protocol** — define target-to-host result transfer, implement in adapter
2. **FPGA JTAG chain** — establish chain on ZedBoard, add upload/run/result proof, or formally exclude
3. **Compiled-mode wrappers** — add compiled execution wrappers where specs still use interpreter-only glue
4. **Duration capture** — ensure authoritative lanes report non-zero `duration_ms` in result packets
