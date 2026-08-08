# GPU Remote Interpreter Test Lanes — Research

**Date:** 2026-08-07
**Status:** Research complete (paths verified against the repo 2026-08-07)
**Design:** `doc/05_design/runtime/gpu_remote_interpreter_architecture.md`
**Plan:** `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`
**Scope:** Add `cuda` and `vulkan` remote backends to the existing composite-mode remote
test infrastructure (`interpreter(remote(...))` / `jit(remote(...))`), reusing the JTAG/GHDL
lane grammar, mailbox protocol, and runner contracts.

---

## 1. What already exists and is reused

| Existing asset | Location (verified 2026-08-07) | Reused for |
|---|---|---|
| Composite mode grammar `interpreter(remote(baremetal(riscv32)))`, `jit(remote(baremetal(stm32h7)))`, `interpreter(remote(t32(stm32wb)))`, `interpreter(remote(openocd(stm32wb)))`, `interpreter(remote(baremetal(ghdl(riscv32))))` | Spec: `doc/06_spec/03_system/compiler/remote_interpreter_backend_spec.md`. Helpers `extract_base_runtime`, `extract_platform_layer`, `extract_remote_backend`, `extract_arch_from_spec`, `extract_target_from_spec` — all `fn (spec: text) -> text` — defined in `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` **and duplicated** in `src/lib/nogc_sync_mut/test_runner/test_executor_composite_parse.spl`. A third mode-parsing path exists in the Rust seed driver (`src/compiler_rust/driver/src/cli/test_runner/{args,runner,types,execution}.rs`). | Grammar extension — `cuda`/`vulkan` become new **remote backends**, same nesting depth as `t32`/`openocd`/`ghdl`. Any grammar change must land in BOTH `.spl` files and be checked against the seed driver parser (three-implementations trap). |
| Remote JIT architecture: host compiles, Remote Execution Manager (breakpoint/memory/register managers), Debug Protocol Adapter (GDB RSP, T32 RCL) | `doc/05_design/runtime/remote_jit_architecture.md`; combination matrix in `doc/05_design/lib/runtime/remote_jit_combination_matrix.md` | GPU lanes slot in as new Target×Transport rows; the "upload → run → collect" manager shape is preserved, with the GPU driver replacing the debug probe |
| GHDL RV32 mailbox protocol: MMIO block at `0x80FF0000` (CMD/ARG0/ARG1/STATUS/RESULT/SEQ_ID/TRIGGER), trigger magic `0x0000DEAD`, commands PUTC(0x01)/EXIT(0x02)/RESULT(0x03), sentinel `0xCAFE0000\|ec` at `0x80008000`, timeout sentinel `0xDEAD0000` | `doc/04_architecture/hardware/ghdl_rv32_mailbox_protocol.md` (all constants re-verified 2026-08-07). Runner scripts: `scripts/fpga/ghdl_rv32_*.shs` | **Byte-for-byte reuse** as the GPU mailbox record layout (offsets become buffer offsets instead of MMIO addresses) |
| Multi-mode test runner + host-aware PASS/SKIP/FAIL semantics (`skip:` for missing host tools, `blocked:` for host blockers) | `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md`; `src/lib/nogc_sync_mut/test_runner/` | Runner routing for the new backends; same host-aware skip discipline |
| CUDA driver plumbing: `cuInit`/`cuModuleLoadDataEx` PTX JIT, guarded-buffer validation contract, `CUDA_LIVE_REQUIRED=0\|1`, "never convert JIT errors to SKIP" | `doc/03_plan/sys_test/cuda_host_validation_2026-07-11.md`; `src/lib/gc_async_mut/cuda.spl`; `src/lib/gc_async_mut/crypto_accel/cuda_session.spl` | The `jit(remote(cuda(...)))` lane is mostly wiring: the PTX-JIT-launch-readback loop already has a hardened contract |
| Vulkan compute + SPIR-V emitter (engine2d backend, processing IR CUDA/Vulkan parity work) | `doc/08_tracking/bug/processing_ir_cuda_vulkan_fill64_parity_2026-07-26.md`; `doc/08_tracking/bug/vulkan_spirv_struct_function_type_cache_empty_2026-07-20.md`. Host-side Vulkan calls go through `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` (vendored `ash` bindings). | The `jit(remote(vulkan(...)))` lane reuses the SPIR-V emission path; pipeline creation *is* the JIT step |
| Lane status discipline (host-aware baremetal lanes) | `doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md`. **Note:** `doc/08_tracking/lane_matrix.md` does NOT exist yet — the plan's Task E2 creates it. | New lanes are registered as host-aware rows, same tier as hardware-dependent lanes |

## 2. Known blocker already on file

`doc/08_tracking/bug/rt_cuda_module_load_data_bytes_missing_interpreter_adapter_2026-08-05.md`
— **still open (re-verified 2026-08-07)**. `rt_cuda_module_load_data_bytes` is declared at
`src/lib/nogc_sync_mut/cuda/sffi.spl:59` and `src/lib/nogc_sync_mut/gpu_driver/mod.spl:28`,
registered for codegen at `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1729`
(`(&[I64,I64],&[I64])`), but `interpreter_extern/mod.rs` registers only
`rt_cuda_module_load_data` (mod.rs:932 → gpu.rs:1479) — no `_bytes` variant. So
`bin/simple test` (interpreter) cannot call it. Hard prerequisite for every CUDA lane →
**Task B0** in the plan.

## 3. GPU platform facts that shape the design

**CUDA (NVIDIA):**
- Real runtime JIT exists twice over: (a) emit PTX from Simple's backend and
  `cuModuleLoadDataEx` it (already proven in-repo), (b) NVRTC compiles CUDA C++ at
  runtime (not needed — the PTX path is stronger for us).
- Pinned, host-mapped memory (`cuMemHostAlloc` with the mapped flag) gives a region both
  host and device can read/write — a software MMIO window. On sm_70+ (`cuda::atomic` with
  `thread_scope_system`) host↔device polling on that region is well-defined. This is the
  direct analog of the GHDL testbench watching the mailbox block.
- Persistent ("resident") kernels are legal and common, but a display-attached GPU has a
  watchdog (TDR on Windows, ~2s; similar on some Linux desktop setups). A resident VM must
  either run on a compute-only GPU or bound each program and re-launch.
- `cuda-gdb` exists but is driven via GDB MI/CLI, **not** a clean RSP socket for device
  threads — so the existing GDB RSP client does not port directly. A cuda-gdb "semihost"
  lane is possible via an MI adapter (analogous to the T32 RCL adapter) but is exploratory.
- `cuStreamWriteValue32`/`cuStreamWaitValue32` (batched memops) can implement doorbells
  without a spinning host thread, as a later optimization.

**Vulkan:**
- There is no "load PTX" equivalent; the JIT step is: emit SPIR-V → `vkCreateShaderModule`
  → `vkCreateComputePipelines` (driver JITs SPIR-V to ISA; `VkPipelineCache` makes repeats
  cheap).
- SPIR-V (compute) forbids recursion and function pointers; a bytecode VM must use an
  explicit operand/call stack in arrays. This is fine for a test VM.
- **No forward-progress guarantee**: a shader spin-waiting on host writes may never observe
  them and can deadlock the queue. Therefore **no resident VM on Vulkan** — every program is
  one bounded dispatch.
- Host-visible + host-coherent memory is guaranteed consistent at submission boundaries
  (fence signaled ⇒ device writes visible). Mid-dispatch host polling of device writes is
  not portable ⇒ device→host PUTC must be **buffered** (log ring drained after the fence),
  not interactive.
- Timeout handling: `vkWaitForFences` with a deadline; `VK_ERROR_DEVICE_LOST` (watchdog
  kill) maps to the existing timeout sentinel `0xDEAD0000`.
- Useful (optional, feature-gated) extensions: `VK_KHR_buffer_device_address` (pointer-ish
  addressing for the VM arena), `VK_KHR_shader_clock` (budget/timeout inside the VM),
  `maintenance4`, `VK_KHR_pipeline_executable_properties` (diagnostics).

## 4. Design consequences (one-paragraph version)

CUDA gets the full lane family (JIT lane, VM-per-launch lane, VM-resident lane, exploratory
cuda-gdb lane) because it has host-mapped memory with system-scope atomics and a real
module JIT. Vulkan gets two lanes (JIT lane, VM-per-dispatch lane) with a buffered mailbox
and hard per-dispatch bounds, because it lacks forward-progress and interactive host
polling guarantees. Both share one mailbox record layout (lifted verbatim from the GHDL
protocol) and one GPU bytecode VM ("SVM-G") so the CUDA and Vulkan interpreters are the
same program in two toolchains.

## 5. References

- `doc/05_design/runtime/remote_jit_architecture.md`; `doc/05_design/lib/runtime/remote_jit_combination_matrix.md`
- `doc/04_architecture/hardware/ghdl_rv32_mailbox_protocol.md`; `scripts/fpga/ghdl_rv32_*.shs`
- `doc/06_spec/03_system/compiler/remote_interpreter_backend_spec.md`; `doc/06_spec/feature/app/remote_baremetal/remote_baremetal_runtime_spec.md`; `doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md`
- `doc/03_plan/sys_test/cuda_host_validation_2026-07-11.md`
- `doc/08_tracking/bug/rt_cuda_module_load_data_bytes_missing_interpreter_adapter_2026-08-05.md`
- CUDA: driver API module loading (`cuModuleLoadDataEx`), mapped host memory, `cuda::atomic` system scope, kernel exec timeout attribute, stream memops
- Vulkan: compute pipelines + pipeline cache, host-visible/coherent memory model, fence timeout / `VK_ERROR_DEVICE_LOST`, SPIR-V restrictions (no recursion/function pointers), optional `VK_KHR_buffer_device_address`, `VK_KHR_shader_clock`
