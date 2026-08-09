# Lane Matrix

Authoritative, hand-maintained cross-reference of every remote test-execution
lane the runner routes to — baremetal/QEMU/hardware-debug lanes plus the GPU
remote-interpreter lanes. Created for Task E2 of
`doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`
(previously referenced by several docs as "does not exist yet" — it now does).

Do not hand-edit lane semantics here without also updating the source the row
was seeded from (`LaneRegistry.default()` for baremetal rows,
`gpu_lane_common.spl`/design §7 for GPU rows) — this file is a index/summary,
not the source of truth.

## Baremetal / hardware-debug lanes (authoritative subset)

Seeded from `doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md`
/ `src/lib/nogc_sync_mut/debug/remote/exec/lane_registry.spl`'s
`LaneRegistry.default()`. This table lists the 8 lanes classified
`stable` or `host_aware` (i.e. `LaneStatus.is_authoritative() == true`) at the
time this file was created — the registry itself carries more rows (16 total,
including `in_progress`/`transport_only`/`excluded_public` ones); see the
spec/source above for the full set.

| Lane ID | Target arch | Adapter | Class | Result channel (primary / fallback) | Authoritative spec |
|---|---|---|---|---|---|
| `qemu_rv32_semihost` | riscv32 | qemu_gdb | stable | semihost_text / exit_code | `test/02_integration/remote_jit/qemu_rv32_library_semihost_spec.spl` |
| `qemu_arm_semihost` | arm32 | qemu_gdb | stable | semihost_text / exit_code | `test/02_integration/remote_jit/qemu_arm_composite_runner_spec.spl` |
| `x86_64_direct_boot` | x86_64 | direct_boot | stable | exit_code / — | `test/03_system/qemu/os/boot/x86_64_boot_qemu_spec.spl` |
| `ch32v307_wlink` | riscv32 | wlink_cli | host_aware | register_readback / ram_sentinel | `test/02_integration/remote_jit/ch32v307_composite_runner_spec.spl` |
| `stm32h7_openocd` | arm32 | openocd_gdb | host_aware | register_readback / ram_sentinel | `test/02_integration/remote_jit/stm32h7_composite_runner_spec.spl` |
| `stm32h7_trace32` | arm32 | trace32 | host_aware | debugger_console / register_readback | `test/03_system/t32_terminal_power_remote_spec.spl` |
| `ghdl_rv32_semihost` | riscv32 | ghdl_sim | host_aware | semihost_text / exit_code | `test/03_system/feature/baremetal/ghdl_riscv32_semihost_spec.spl` |
| `ghdl_rv32_mailbox` | riscv32 | ghdl_sim | host_aware | ram_sentinel / register_readback | `test/03_system/feature/baremetal/ghdl_riscv32_mailbox_spec.spl` |

## GPU remote-interpreter lanes

Seeded from design §7 (`doc/05_design/runtime/gpu_remote_interpreter_architecture.md`)
plus current landed status per
`doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md` (2026-08-07).
All 5 rows are `host-aware` class (same tier as the hardware-debug lanes
above): they run for real only when the required driver/ICD and `rt_*`
symbols are present, and report `skip:`/`blocked:` otherwise per
`gpu_lane_common.spl`'s `route_gpu_lane` (A3's established contract — see the
status spec below for the assertions).

| Lane ID | Spec string | Class | Readiness probe | Executor | Spec / conformance file | Status on this host (2026-08-07) |
|---|---|---|---|---|---|---|
| `cuda_jit` | `jit(remote(cuda(sm80)))` | host-aware | `gpu_lane_common.probe_gpu_driver_present("cuda")` (nvidia-smi) + `probe_gpu_symbols("cuda")` (`rt_cuda_init`, `rt_cuda_module_load_data_bytes`) | `src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl` (`CudaJitLaneExecutor`) | `test/03_system/gpu_lane/cuda_jit_hello_spec.spl` | Working (13/14 passing; 1 failure is the filed `cuda_lane_session_create_unresolved_across_module_boundary_2026-08-07` deployed-binary gap, not an executor defect) |
| `cuda_vm` | `interpreter(remote(cuda(sm80)))` | host-aware | same as `cuda_jit` (cuda backend probe) | `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl` (`CudaVmExecutor`) | `test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl` | Working (2026-08-08 update) — the D3 conformance table now runs against `CudaVmExecutor` in this checked-in system spec (superseding the "none in-tree yet" note below, which was accurate as of 2026-08-07 but is now stale); verified 2/2 examples passing on live dual-GPU hardware same day. Two vectors run outside the bulk tally for documented reasons: `mem_store_load_byte` (real device/host code-data co-residency divergence, same class as the `vulkan_vm` row's exclusion, see `svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07`) and `budget_exhaustion_timeout` (intentionally times out; runs in its own isolated session since a real device timeout correctly, by design, latches the session for all subsequent calls — see `cuda_vm_executor_conformance_array_index_out_of_bounds_2026-08-08` for the root-cause writeup). Root cause originally flagged as an open gap in `svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07`, which remains accurate for the co-residency divergence itself but not for the "never run in-tree" claim. |
| `cuda_vm_resident` | `interpreter(remote(cuda(sm80(resident))))` | host-aware, opt-in | same cuda backend probe, **plus** `cuda_resident_session.resident_refusal_gate` (watchdog-attribute gate; `CUDA_RESIDENT_FORCE=1` overrides) | `src/lib/gc_async_mut/gpu_lane/cuda_resident_session.spl` (`ResidentSession`) | `test/03_system/gpu_lane/cuda_resident_session_spec.spl` | Blocked — protocol logic fully green (18/18), but live single-kernel resident dispatch is blocked on 3 missing SFFI bindings (`cuMemHostAlloc`/`cuMemHostGetDevicePointer` mapped memory, a real `CU_DEVICE_ATTRIBUTE_KERNEL_EXEC_TIMEOUT` query, a resident ring-polling PTX kernel) — filed `cuda_resident_session_missing_mapped_memory_and_watchdog_sffi_2026-08-07`. Watchdog attribute always reads `WATCHDOG_UNKNOWN` on this build, so `start()` refuses unless forced |
| `vulkan_jit` | `jit(remote(vulkan(spv15)))` | host-aware | `gpu_lane_common.probe_gpu_driver_present("vulkan")` (vulkaninfo) + `probe_gpu_symbols("vulkan")` (`rt_vulkan_alloc_buffer`, `rt_vulkan_begin_compute`) | `src/lib/gc_async_mut/gpu_lane/vulkan_jit_lane_executor.spl` (`VulkanJitLaneExecutor`) | `test/03_system/gpu_lane/vulkan_jit_hello_spec.spl`, `test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl` | Working (2/2 + 4/4 passing on real hardware, live dispatch confirmed, not skip) |
| `vulkan_vm` | `interpreter(remote(vulkan(spv15)))` | host-aware | same as `vulkan_jit` (vulkan backend probe) | `src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl` (`VulkanVmExecutor`) | `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl` | Working with one documented exclusion — 58/58 non-excluded D3 conformance vectors pass on real hardware; `mem_store_load_byte` is excluded due to a real device/host divergence (code+data co-residency), filed `svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07` |

### Notes / known gaps that affect this table

- **Generic runner routing (`gpu_lane_common.run_test_file_gpu_lane`) is not
  wired to any of the 5 real executors above.** It still reports
  `"<backend> lane executor not yet implemented (see B2/B3/C2/C3)"` (a FAIL,
  not a skip) whenever the driver is present and required symbols resolve —
  even for `cuda_jit`/`vulkan_jit`, which DO have real executors now. The
  executors above are exercised directly by their own dedicated specs, not
  through the generic composite-runner GPU-lane dispatch path yet. This is a
  real, live gap on any host with GPU hardware (confirmed on this host: both
  `nvidia-smi -L` and `vulkaninfo --summary` succeed, and all 4 probed `rt_*`
  symbols resolve, so `route_gpu_lane` returns the generic FAIL branch, not
  `skip:`, for every GPU lane on this host). Filed:
  `doc/08_tracking/bug/gpu_lane_generic_routing_not_wired_to_real_executors_2026-08-07.md`.
- **On a genuinely no-GPU host** (no `nvidia-smi`, no `vulkaninfo`, or both
  fail), `probe_gpu_driver_present` returns `false` for the relevant backend
  and `route_gpu_lane` returns a well-formed `skip:` result for every lane
  routed through it — this is what
  `test/03_system/gpu_lane/gpu_lane_matrix_status_spec.spl` (below) asserts
  at the pure-function level (`driver_present: false`), independent of what
  hardware the CI runner or dev host actually has.
- CI wiring: `.github/workflows/gpu-lane-tests.yml` — portable gate job
  (A1-A3/D1-D4 routing + conformance specs, no GPU required, runs on every
  push/PR on `ubuntu-latest`) plus two `workflow_dispatch`-only live-lane
  jobs gated on `runs-on: [self-hosted, cuda-live]` /
  `runs-on: [self-hosted, vulkan-live]` labels (neither runner is currently
  provisioned in this repo's Actions fleet — same honest-placeholder pattern
  `notebook-lanes-tests.yml`'s `gpu-notebook-fixtures` job already uses).

## Status spec

`test/03_system/gpu_lane/gpu_lane_matrix_status_spec.spl` — extends the
`remote_baremetal_lane_status_spec.spl` style (row-per-lane assertions,
`skip:`/`blocked:` semantics) to the 5 GPU rows above. See its own docstring
for scenario detail.

## Related

- Design: `doc/05_design/runtime/gpu_remote_interpreter_architecture.md` §7
- Plan: `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`
- Feature-expert skill: `doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`
- Baremetal status spec: `doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md`
- A3 routing contract: `src/lib/nogc_sync_mut/test_runner/gpu_lane_common.spl`
