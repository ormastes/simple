# GPU Remote Interpreter Test Lanes — Architecture & Design

**Date:** 2026-08-07
**Status:** Design Proposal
**Research:** `doc/01_research/runtime/gpu_remote_interpreter_research.md`
**Plan:** `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`

---

## 1. Goals / Non-Goals

**Goals**
1. Run SSpec test programs on a GPU through the same runner UX as baremetal lanes:
   `bin/simple test foo_spec.spl '--mode=interpreter(remote(cuda(sm80)))'`.
2. Reuse the composite mode grammar, extractor helpers, mailbox record layout, sentinel
   values, and PASS/SKIP/FAIL host-aware contract unchanged wherever possible.
3. One shared VM bytecode (SVM-G) executed by both a CUDA kernel and a SPIR-V shader.
4. A parallel plan whose tasks are small, file-scoped, and individually verifiable.

**Non-Goals (this phase)**
- General-purpose GPU debugging (breakpoints/watchpoints on device code). The breakpoint
  manager is *not* ported; GPU lanes are upload→run→collect only.
- Multi-GPU, graphics pipelines, interop with the engine2d render path.
- Running the *full* Simple interpreter on device. SVM-G executes a documented subset
  sufficient for test bodies (§5.4); unsupported constructs fail fast at lowering,
  mirroring the VHDL backend's strict fail-fast rule.
- Metal/ROCm backends (the transport trait is written so they can be added later).

---

## 2. Grammar Extension (reuse of the JTAG composite grammar)

### 2.1 New remote backends

`cuda` and `vulkan` are added at the same grammar position as `t32` / `openocd` / `ghdl`:

```
mode          := base_runtime "(" platform ")"
base_runtime  := "interpreter" | "jit"
platform      := "remote" "(" remote_backend "(" target [ "(" option ")" ] ")" ")" | ...
remote_backend+= "cuda" | "vulkan"          # NEW (existing: baremetal, t32, openocd, ghdl…)
```

Accepted spec strings (canonical set — tests quote them exactly):

| Spec string | Meaning |
|---|---|
| `jit(remote(cuda(sm80)))` | Host emits PTX for the test kernel; `cuModuleLoadDataEx`; one launch per test; mailbox readback |
| `interpreter(remote(cuda(sm80)))` | SVM-G bytecode VM kernel; **per-launch** mode (default): one launch per program |
| `interpreter(remote(cuda(sm80(resident))))` | SVM-G resident kernel + command ring in pinned mapped memory; opt-in (compute-only GPUs) |
| `jit(remote(vulkan(spv15)))` | Host emits SPIR-V for the test kernel; pipeline creation = JIT; one dispatch per test |
| `interpreter(remote(vulkan(spv15)))` | Prebuilt SVM-G interpreter shader; bytecode passed as SSBO data; one dispatch per program |
| `interpreter(remote(cudagdb(sm80)))` | **Exploratory P3** — cuda-gdb MI adapter semihost lane (§6.4) |

`sm80` is the default CUDA target token (any `smNN` accepted and forwarded to the PTX
`.target`); `spv15` is the default SPIR-V token (`spv13`…`spv16` accepted).

### 2.2 Extractor behavior (concrete interface — drives Task A1's spec)

The extractors are `fn extract_<x>(spec: text) -> text`, defined in
`src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` and **duplicated** in
`test_executor_composite_parse.spl` — Task A1 must change both, and check the Rust seed
driver's own mode parser (`src/compiler_rust/driver/src/cli/test_runner/args.rs`) for
drift (three-implementations trap).

| Helper | `interpreter(remote(cuda(sm80)))` | `jit(remote(vulkan(spv15)))` |
|---|---|---|
| `extract_base_runtime` | `"interpreter"` | `"jit"` |
| `extract_platform_layer` | `"remote"` | `"remote"` |
| `extract_remote_backend` | `"cuda"` | `"vulkan"` |
| `extract_arch_from_spec` | `"ptx64"` | `"spirv"` |
| `extract_target_from_spec` | `"cuda_sm80"` | `"vulkan_spv15"` |
| `extract_gpu_submode` (NEW) | `"launch"` (default) / `"resident"` | `"dispatch"` (always) |

Rule: `resident` is only legal under `cuda`; the parser rejects
`interpreter(remote(vulkan(spv15(resident))))` with a diagnostic naming the
forward-progress rationale (research §3, Vulkan).

---

## 3. GPU Mailbox Protocol (GMB-1) — the GHDL mailbox, relocated into a buffer

One buffer, the **mailbox arena**, replaces the target RAM + MMIO window. All offsets,
magic numbers, command codes, and sentinel values are **identical** to
`doc/04_architecture/hardware/ghdl_rv32_mailbox_protocol.md` (constants re-verified
2026-08-07); only "address" becomes "byte offset into the arena".

### 3.1 Arena layout

```
Arena size: 64 KiB + 64 KiB = 128 KiB (single allocation)

+0x00000 .. +0x0FFFF   DATA region ("RAM"): VM heap/arena, test I/O buffers
+0x08000               ram_sentinel        (mirrors 0x80008000 = RAM base + 0x8000)
+0x10000               REG block base      (mirrors 0x80FF0000)
   +0x00  CMD      device→host  u32
   +0x04  ARG0     device→host  u32
   +0x08  ARG1     device→host  u32
   +0x0C  STATUS   host→device  u32   (reserved, as in GHDL lane)
   +0x10  RESULT   host→device  u32   (reserved)
   +0x14  SEQ_ID   device→host  u32   (monotonic)
   +0x18  TRIGGER  device→host  u32   (write 0x0000DEAD to fire)
+0x10020               LOG ring            (NEW, Vulkan-required, CUDA-optional)
   +0x00  LOG_HEAD u32 (device atomic cursor)
   +0x04  LOG_CAP  u32 (host-initialized, bytes)
   +0x08  LOG[LOG_CAP] bytes (PUTC payloads)
+0x10020+8+LOG_CAP     RECORD ring         (NEW: CMD_RESULT records, 12 bytes each)
```

- Commands: `CMD_PUTC=0x01`, `CMD_EXIT=0x02`, `CMD_RESULT=0x03` — unchanged.
- Sentinels: normal exit `0xCAFE0000 | exit_code[15:0]`; timeout `0xDEAD0000` — unchanged,
  written to `+0x08000`.
- Trigger magic `0x0000DEAD`, cleared to 0 by the servicer — unchanged.

### 3.2 Two servicing modes

**Interactive (CUDA only).** Host servicer thread polls TRIGGER on the pinned mapped
arena (system-scope acquire load), dispatches CMD exactly like the GHDL testbench, clears
TRIGGER (system-scope release store). Device side uses `cuda::atomic_ref<uint32_t,
thread_scope_system>` for TRIGGER and spins with backoff + budget. PUTC streams live.

**Buffered (Vulkan; also CUDA per-launch fallback).** The shader never waits on the host.
`CMD_PUTC` appends to the LOG ring (atomicAdd on LOG_HEAD); `CMD_RESULT` appends a
12-byte record `(seq, pass, value)` to the RECORD ring; `CMD_EXIT` writes the sentinel to
`+0x08000` and returns from the kernel. Host drains LOG/RECORD **after** the fence/sync.
Semantically identical output, delivered late.

The host-side servicer + drainer is **one shared module** (Task A2) consumed by both
backends; sentinel-decode behavior is lifted from the GHDL runner scripts
(`scripts/fpga/ghdl_rv32_*.shs`).

### 3.3 Timeout / budget

- Host: watchdog deadline (default 30 s wall, override `GPU_LANE_TIMEOUT_MS`); on expiry —
  CUDA: `cuCtxSynchronize` abandoned, context destroyed, sentinel forced `0xDEAD0000`;
  Vulkan: fence timeout or `VK_ERROR_DEVICE_LOST` ⇒ sentinel forced `0xDEAD0000`.
- Device: SVM-G decrements a step budget (default 50M steps, host-set in the program
  header); on exhaustion the VM itself writes `0xDEAD0000` and exits cleanly. This is the
  GPU analog of the GHDL 1,000,000-cycle counter and is what keeps Vulkan dispatches
  watchdog-safe.

---

## 4. SVM-G: the shared GPU bytecode VM

### 4.1 Shape

- 32-bit word-oriented **stack machine** (simplest to lower to from the existing
  interpreter's expression evaluation; no register allocation needed).
- Explicit fixed-size stacks in thread-private arrays: operand stack 256 slots, call stack
  32 frames. No recursion in the *implementation* (Vulkan requirement) — VM `CALL` pushes a
  frame index, the dispatch loop is one flat `loop { switch(opcode) }`.
- Types: `i32`, `u32`, `f32`, plus `i64` as pairs (needed for checksums); `f64` excluded in
  v1 (Vulkan `shaderFloat64` is optional hardware).
- Memory: all loads/stores are bounds-checked offsets into the DATA region of the arena.
  Out-of-bounds ⇒ trap ⇒ `CMD_RESULT(pass=0, value=TRAP_OOB)` + `CMD_EXIT(0x7F)`.
- Threading: program executes on **thread 0 of workgroup 0** by default (deterministic,
  matches interpreter semantics). A `PARFOR` opcode fans a bounded body across the
  workgroup with a barrier at the end, for tests that want to prove parallel behavior.

### 4.2 Program container ("SGP" blob, uploaded into DATA at +0x0000)

```
u32 magic     = 0x53474250        ("SGPB")
u32 version   = 1
u32 code_off, code_len            (bytes, within DATA)
u32 data_off, data_len
u32 step_budget
u32 entry_pc
u32 reserved[1]
```

### 4.3 Opcode set v1 (complete list — implement exactly these, fail-fast on others)

```
0x00 NOP            0x10 PUSHI imm32      0x20 ADD/SUB/MUL/DIV/REM (i32: 0x20-0x24)
0x01 HALT code      0x11 PUSHF imm32      0x28 FADD/FSUB/FMUL/FDIV (f32: 0x28-0x2B)
0x02 TRAP code      0x12 DUP  0x13 DROP   0x30 AND/OR/XOR/SHL/SHR/SAR (0x30-0x35)
                    0x14 SWAP             0x38 EQ/NE/LT/LE/GT/GE (i32; f32 at 0x3E-0x43)
0x50 LOAD32 / 0x51 STORE32 / 0x52 LOAD8 / 0x53 STORE8      (arena offset on stack)
0x60 JMP rel16      0x61 JZ rel16         0x62 JNZ rel16
0x68 CALL pc16      0x69 RET
0x70 SYS_PUTC       0x71 SYS_EXIT         0x72 SYS_RESULT   (map 1:1 to GMB-1 commands)
0x78 TID            0x79 NTID             0x7A PARFOR len16 (fan next len16 bytes; barrier)
```

Anything the lowering pass cannot express in this set is a **compile-time** error naming
the construct — never a silent fallback (VHDL-backend rule).

### 4.4 Supported Simple subset for `interpreter(remote(gpu))` test bodies (v1)

Integer/float arithmetic and comparisons, `if/elif/else`, bounded `for i in a..b`, `while`
with the step budget as backstop, non-recursive `fn` calls, fixed-size arrays lowered into
the DATA region, `print` of string literals and integers (via PUTC), `expect(x).to_equal(y)`
lowered to `SYS_RESULT`. Excluded v1 (fail-fast): closures, GC types, actors/async, text
manipulation beyond literals, dictionaries, recursion deeper than the fixed frame count.
This mirrors the runtime-family rule: GPU lanes execute `gc_async_mut`-family *API* but the
device programs themselves are `noalloc`-shaped.

### 4.5 Two implementations, one conformance suite

- CUDA: `svm_g.cu`-equivalent emitted as PTX by the existing emitter (or a checked-in PTX
  artifact, same policy as the checked-in RV32 ELFs used by the baremetal specs).
- Vulkan: `svm_g.comp`-equivalent emitted once as SPIR-V, checked in with its SHA-256, and
  loaded via pipeline cache.
- Conformance: a golden test vector suite (Task D3) — ~40 SGP blobs with expected
  LOG/RECORD/sentinel outputs — run against **both** implementations and against a host
  reference interpreter of SVM-G (Task D2) which is also what CI without GPUs runs.

---

## 5. CUDA Lane Design

### 5.1 `jit(remote(cuda(smNN)))` — P0

Pipeline per test file:
1. Lower test body → kernel(s) via the existing PTX emitter (reuse the exact positive
   sequence in `doc/03_plan/sys_test/cuda_host_validation_2026-07-11.md`: record PTX
   SHA-256, `.version`, `.target`, `.address_size`, entry names).
2. `cuInit` → device select (`CUDA_VISIBLE_DEVICES` honored) → retain context →
   `cuModuleLoadDataEx` with bounded info/error buffers.
3. Allocate arena (device) + copy SGP-less layout (this lane needs only the mailbox block
   + DATA I/O); guard regions around every buffer (existing contract).
4. Launch; check immediate launch result; `cuCtxSynchronize`; DtoH the arena; decode
   sentinel + drain buffered LOG/RECORD.
5. Cleanup order and first-error retention exactly per the validation plan.

### 5.2 `interpreter(remote(cuda(smNN)))` per-launch — P0

Same as 5.1 but the module is the **SVM-G interpreter**, loaded once per session and
cached; per test program: write SGP blob into arena DATA, launch 1×1, sync, drain.
Buffered servicing; no host polling thread required. This is the default and the
watchdog-safe mode.

### 5.3 `interpreter(remote(cuda(smNN(resident))))` — P1

- Arena allocated with `cuMemHostAlloc(MAPPED|PORTABLE)`; device pointer via
  `cuMemHostGetDevicePointer`.
- Command ring (host→device): 8-slot ring of `(sgp_offset, doorbell)` pairs; device
  spins on the doorbell with system-scope acquire + `nanosleep`-style backoff; host writes
  program then doorbell (release).
- Interactive servicing thread for device→host TRIGGER (live PUTC).
- Session end: host writes `CMD=SHUTDOWN(0x7E)` slot; kernel returns; `cuCtxSynchronize`.
- Gate: refuse to start resident mode if the selected device has a display/watchdog
  (`CU_DEVICE_ATTRIBUTE_KERNEL_EXEC_TIMEOUT == 1`) unless `CUDA_RESIDENT_FORCE=1`.

### 5.4 `interpreter(remote(cudagdb(smNN)))` — P3 exploratory

Drive `cuda-gdb` via MI (adapter class parallel to the T32 RCL client): break on a device
`__semihost_trap()` function, read args from the mailbox block, service, `continue`. Value:
proves the semihost lane shape ports; not on the critical path. Timebox: research spike
only (Task B6) that produces a go/no-go doc in `doc/01_research/`.

---

## 6. Vulkan Lane Design

### 6.1 `jit(remote(vulkan(spvNN)))` — P0

1. Lower test body → compute SPIR-V via the existing emitter path (fix-forward any gaps by
   filing bugs like the existing SPIR-V cache bug — do not fork the emitter).
2. Instance/device selection: prefer a compute-capable queue; honor
   `VULKAN_DEVICE_INDEX`; record deviceName/driverVersion/apiVersion into the lane log.
3. Arena = one `VkBuffer` (STORAGE), memory HOST_VISIBLE|HOST_COHERENT (fallback: device-
   local + staging copies both ways). Bound as SSBO set 0 binding 0.
4. `vkCreateShaderModule` → `vkCreateComputePipelines` with a persistent `VkPipelineCache`
   file under the build dir (this *is* the JIT; cache makes re-runs cheap).
5. One `vkCmdDispatch` per test; fence with `GPU_LANE_TIMEOUT_MS`; on timeout or
   `VK_ERROR_DEVICE_LOST` force sentinel `0xDEAD0000`.
6. Drain sentinel + LOG + RECORD from the mapped arena after the fence.

### 6.2 `interpreter(remote(vulkan(spvNN)))` — P0

Same harness; the pipeline is the **prebuilt SVM-G shader** (checked-in SPIR-V + SHA-256,
compiled from source in Task D1's build step; validated by `spirv-val` in CI). Per test:
write SGP blob into DATA, dispatch 1×1×1 (or `PARFOR` workgroup size from the SGP header),
fence, drain. Step budget mandatory and validated > 0 before submit.

### 6.3 Explicit prohibitions (encode as parser/runner errors)

- No resident submode (grammar rejects it — §2.2).
- No host↔device handshake inside a dispatch.
- No unbounded loops in emitted SPIR-V: the JIT lane's lowering must thread the same step
  budget through generated loops (decrement + conditional `SYS_EXIT(0xDEAD…)` path).

---

## 7. Environment / Failure Contract (extends the CUDA host validation contract)

| Variable | Default | Meaning |
|---|---|---|
| `CUDA_LIVE_REQUIRED` | `0` | existing semantics, unchanged |
| `VULKAN_LIVE_REQUIRED` | `0` | same semantics for Vulkan lanes |
| `GPU_LANE_TIMEOUT_MS` | `30000` | host watchdog per program |
| `SVMG_STEP_BUDGET` | `50000000` | device step budget default |
| `CUDA_RESIDENT_FORCE` | `0` | override watchdog-device refusal (dev only) |

State machine per lane run (identical wording to the CUDA plan, extended):
- `SKIP`: live GPU optional and driver/device/ICD absent. Exit 0. Portable gates (SVM-G
  host-reference conformance, PTX/SPIR-V emission + static validation) remain mandatory.
- `FAIL`: emission, JIT/pipeline creation, symbol/entry resolution, allocation, launch/
  dispatch, sync/fence, sentinel decode, or conformance mismatch — **never** converted to
  SKIP once the GPU is required or detected.
- `PASS`: sentinel `0xCAFE0000|0`, all RECORDs pass, zero guard-region violations.

Lane registrations (host-aware tier, same as hardware lanes; recorded in
`doc/08_tracking/lane_matrix.md`, which Task E2 **creates** — it does not exist yet):

| Lane id | Spec string | Class |
|---|---|---|
| `cuda_jit` | `jit(remote(cuda(sm80)))` | host-aware |
| `cuda_vm` | `interpreter(remote(cuda(sm80)))` | host-aware |
| `cuda_vm_resident` | `interpreter(remote(cuda(sm80(resident))))` | host-aware, opt-in |
| `vulkan_jit` | `jit(remote(vulkan(spv15)))` | host-aware |
| `vulkan_vm` | `interpreter(remote(vulkan(spv15)))` | host-aware |

## 8. Consumer interface for the notebook plan

The notebook lanes design (`doc/05_design/app/tools/notebook_lanes_architecture.md`)
consumes exactly these interfaces; keep them stable:
- The spec-string grammar and extractor helpers of §2 (shared validation).
- `GpuLaneExecutor` trait (Task A3): `prepare(session) / run_program(blob) ->
  ArenaSnapshot / teardown`.
- The GMB-1 arena layout + `MailboxArena` host library (Task A2): `decode_sentinel`,
  `drain_log`, `drain_records`, `service_trigger`, `write_sgp_header`.
- CUDA resident session (Task B4) and Vulkan per-dispatch session (Task C3), whose arena
  DATA region is the cross-cell state store for notebooks.
- Lane locks (notebook plan Task H2) are shared back: the test runner GPU lanes honor the
  same per-device file locks.
