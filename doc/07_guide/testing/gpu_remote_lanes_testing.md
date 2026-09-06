# GPU Remote Interpreter Test Lanes

Quick orientation for the `cuda`/`vulkan` remote interpreter test lanes —
the `interpreter(remote(cuda(sm80)))` / `interpreter(remote(vulkan(spv..)))`
grammar family that runs SVM-G bytecode on real GPU hardware as a test
transport, alongside the existing baremetal/QEMU remote lanes.

This guide is intentionally link-heavy: the design doc, plan, and
feature-expert skill are the source of truth. Do not duplicate their content
here — update them, then this guide's links stay valid.

## Start here

| What | Where |
|------|-------|
| Research | `doc/01_research/runtime/gpu_remote_interpreter_research.md` |
| Design / architecture | `doc/05_design/runtime/gpu_remote_interpreter_architecture.md` |
| Implementation plan (streams A-E) | `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md` |
| Current landed/open status (updated as tasks land) | `doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md` |
| GHDL mailbox protocol GMB-1 reuses | `doc/04_architecture/hardware/ghdl_rv32_mailbox_protocol.md` |
| Related baremetal/QEMU lane status spec | `doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md` |
| Consumer plan (notebook lanes) | `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` |

## What this is, briefly

- **Grammar**: the composite remote-mode grammar
  (`src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` and its
  duplicate `test_executor_composite_parse.spl`) parses `cuda(smNN)` /
  `cuda(cudagdb(smNN))` / `vulkan(spvNN)` backend tokens and routes them
  through `GpuLaneExecutor` (`std.test_runner.gpu_lane_common`) instead of
  the `.spl`/`.elf` local-run branches.
- **GMB-1 mailbox**: a GHDL-mailbox-protocol-compatible arena
  (`src/lib/nogc_sync_mut/test_runner/gpu_mailbox.spl`) relocated into GPU
  device/host-visible memory — LOG ring, RECORD ring, exit/timeout
  sentinels — used to get pass/fail results back off the device without a
  device-side filesystem or stdout.
- **SVM-G**: a small shared bytecode VM (`src/lib/common/svmg/`, 50
  opcodes) with two independent implementations that share one conformance
  suite (`test/02_integration/svmg/conformance/conformance_suite_spec.spl`):
  a host reference VM (`ref_vm.spl`) and a CUDA PTX device kernel
  (`src/lib/gc_async_mut/gpu_lane/svmg_cuda_kernel.ptx`). A Vulkan SPIR-V
  device kernel is planned (plan Task C3) but not yet landed.
- **Lane executors**: `CudaJitLaneExecutor` / `CudaVmExecutor` /
  `VulkanJitLaneExecutor` under `src/lib/gc_async_mut/gpu_lane/` wrap a
  `CudaLaneSession`/`VulkanLaneSession` (arena + guard regions) to
  prepare/run/teardown a lane program.

## Running the lane specs locally

These specs SKIP cleanly (via a `probe().starts_with("skip:")` contract) on
hosts without live GPU hardware/toolchains, and exercise the real device
path on hosts that have them:

```bash
bin/simple test test/02_integration/gpu_lane/cuda_lane_session_spec.spl
bin/simple test test/02_integration/gpu_lane/vulkan_lane_session_spec.spl
bin/simple test test/03_system/gpu_lane/cuda_jit_hello_spec.spl
bin/simple test test/03_system/gpu_lane/vulkan_jit_hello_spec.spl
bin/simple test test/01_unit/lib/svmg/opcodes_and_sgp_header_spec.spl
bin/simple test test/01_unit/lib/svmg/ref_vm_spec.spl
bin/simple test test/02_integration/svmg/conformance/conformance_suite_spec.spl
```

Per `.claude/rules/testing.md`'s sequential-access rule, run these one file
at a time rather than as a parallel directory sweep.

## Current status

Do not duplicate the landed/open task table here — it changes as work
lands. Check
`doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`'s "Status"
section and "Known Constraints / Blockers" section for what is landed, what
is blocked, and the filed bug docs (e.g. the Vulkan non-blocking-submit gap,
the CUDA cubin NUL-byte rejection, the SVM-G record-ring layout divergence
between `gpu_mailbox.spl` and `ref_vm.spl`).
