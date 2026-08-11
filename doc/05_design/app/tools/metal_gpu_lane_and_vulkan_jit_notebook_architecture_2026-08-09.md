# Metal GPU Lane + Vulkan JIT Notebook Support — Architecture

**Status:** Design, not yet implemented (implementation tracked in
`doc/03_plan/agent_tasks/metal_gpu_lane_and_vulkan_jit_notebook_parallel_plan_2026-08-09.md`)
**Parent designs:** `doc/05_design/runtime/gpu_remote_interpreter_architecture.md`
(SVM-G/GMB-1/CUDA/Vulkan lane design), `doc/05_design/app/tools/notebook_lanes_architecture.md`
(notebook executor contract)

## 1. Goals / Non-Goals

**Goals:**
1. Add a `metal` GPU backend to the `gpu_lane` architecture, symmetric with the
   existing `cuda`/`vulkan` backends: a VM-based `interpreter(remote(metal(...)))`
   submode (SVM-G bytecode interpreter running as a Metal compute kernel) and a
   `jit(remote(metal(...)))` submode (real per-cell Simple→MSL compilation).
2. Close the Vulkan notebook-lane JIT gap: `jit(remote(vulkan(...)))` is grammar-
   valid but was never wired into `vulkan_exec.spl` at all (no `jit` branch exists
   in that file today — confirmed by direct grep, zero matches). This mirrors the
   already-filed CUDA gap (`doc/08_tracking/bug/notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md`)
   but is currently even further behind: CUDA at least has an honest `Blocked`
   diagnostic; Vulkan has no code path at all.
3. Every new test must be **host-aware skip-clean** (same contract as existing
   CUDA/Vulkan specs): on a host without the required driver/framework, the spec
   SKIPs cleanly (not a fail, not a silent pass) via `probe_gpu_driver_present`/
   `probe_gpu_symbols`. This repo's primary dev/CI hosts are Linux — Metal is
   macOS-only, so every Metal spec written here will legitimately SKIP on this
   host today. That is correct, expected behavior, not a shortcoming: the spec is
   real and will run for real the first time it executes on an actual Mac host,
   exactly the same guarantee CUDA/Vulkan specs already give this repo for
   whichever host happens to have that hardware.

**Non-Goals (this design):**
- CUDA JIT lane's arbitrary-cell-source compile gap — tracked separately, already
  in progress in a concurrent stream (see `notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md`).
  This design's Vulkan-JIT and Metal-JIT streams should reuse whatever pattern
  that work lands (arbitrary Simple cell source → backend codegen → device
  artifact → `*_jit_lane_executor.run_program`), not re-derive it independently.
- Metal resident submode. Metal has no CUDA-style persistent-kernel + doorbell-
  ring primitive; like Vulkan (§6.3 of the parent design, "no resident submode"),
  Metal's `remote(metal(...))` grammar MUST reject a `(resident)` suffix.
- Physical Mac hardware access for THIS implementation pass — see §7 emulation/
  verification strategy. Real-hardware verification happens whenever this code
  is next run from an actual Mac host; that is by design, not deferred.
- Any change to the existing 2D-rendering Metal stack (`metal_graphics_runtime.rs`,
  `src/lib/*/gpu/engine2d/metal_session.spl`, `backend_metal_msl.spl`, etc.) —
  those are reused as a foundation (§3), never modified by this work.

## 2. Why Metal is architecturally closer to Vulkan than CUDA

Per the parent design's CUDA/Vulkan asymmetry (§5 vs §6 of
`gpu_remote_interpreter_architecture.md`): CUDA permits a resident submode because
context/allocation are independent of module load. Vulkan forbids it because even
a buffer-only session needs a pipeline object up front. **Metal is in the same
position as Vulkan**: an `MTLComputePipelineState` must be built from a compiled
`MTLFunction` before any dispatch, and there is no metal-native persistent-kernel/
polling-ring primitive analogous to a CUDA resident kernel. Consequence: Metal's
lane session (`metal_lane_session.spl`, §4) follows `vulkan_lane_session.spl`'s
shape (`init` bundles pipeline creation) rather than `cuda_lane_session.spl`'s
(separate `load_entry` after `init`), and the notebook layer (§6) follows
`vulkan_exec.spl`'s per-launch-only execution model, not CUDA's resident-preferred
one.

## 3. Reused foundation (do not reimplement)

Confirmed already in-tree and load-bearing for the existing 2D-rendering Metal
integration — this design reuses the FFI surface and OS-gating pattern, not the
2D-specific Simple-side session class itself (which is architecturally close but
lives in the wrong tier and has 2D-specific concerns like render passes/textures/
swapchains this design doesn't need):

- **Rust FFI**: `src/compiler_rust/runtime/src/metal_graphics_runtime.rs` (real
  Objective-C/Metal bindings via vendored `objc2-metal` crate,
  `#[cfg(target_os = "macos")]` real impl / `#[cfg(not(target_os = "macos"))]`
  "unavailable" stub) already exposes `rt_metal_init`, `rt_metal_is_available`,
  `rt_metal_device_count`, `rt_metal_create_device`, `rt_metal_alloc_buffer`,
  `rt_metal_compile_shader`, `rt_metal_create_compute_pipeline`,
  `rt_metal_dispatch_compute`, `rt_metal_create_command_queue`,
  `rt_metal_create_command_buffer`, `rt_metal_commit_command_buffer`,
  `rt_metal_wait_completed`, and more, all already wrapped into `rt_metal_*_fn`
  interpreter-extern shims in `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`
  (same file as the CUDA/Vulkan externs — imports at ~line 466-478, wrapper fns
  from ~line 597). **gpu_lane needs only a subset**: device init, command queue,
  buffer alloc (for the SVM-G arena), compile-shader, compute-pipeline-create,
  dispatch, command-buffer commit+wait. All present. No new Rust FFI functions
  are expected to be needed; if the implementing agent finds a genuine gap
  (e.g. no way to read back buffer contents into `[u8]` on the Simple side),
  that's a legitimate small Rust addition to `gpu.rs`, following the exact same
  wrapper pattern as the CUDA/Vulkan `rt_*_fn` functions immediately above it.
- **OS-gating precedent**: the `#[cfg(target_os = "macos")]` dual-path pattern
  in `metal_graphics_runtime.rs` is the model for any place gpu_lane code needs
  to know "is Metal even buildable on this host" — NOT the CUDA/Vulkan dlopen-
  at-runtime pattern (`cuda_dlopen`/`vulkan_dlopen` modules in `gpu.rs`), since
  `Metal.framework` isn't a runtime-dlopen'able shared object the same way
  `libcuda.so`/`libvulkan.so` are, and Metal calls go through Objective-C
  message-send plumbing the `objc2-metal` crate already handles.
- **MSL codegen precedent**: `backend_metal_msl.spl` (2D-rendering MSL emitter)
  establishes that this repo already generates Metal Shading Language source
  from Simple constructs. gpu_lane's MSL emitter (§5) is architecturally
  parallel but functionally new — it targets arbitrary SVM-G bytecode / compute
  kernels, not 2D draw commands, so it is a **new file**
  (`src/compiler/70.backend/backend/metal/msl_builder.spl`), not a modification
  of the rendering one, mirroring how `cuda/ptx_builder.spl` and
  `vulkan/spirv_builder.spl` are separate per-backend files already.
- **Session-shape precedent**: `src/lib/nogc_sync_mut/gpu/engine2d/metal_session.spl`'s
  `MetalSession` class (`init_device`/`load_library`/`get_or_create_pipeline`/
  `begin_command`/`commit_and_wait`/`release`) is the closest existing analog to
  the new `metal_lane_session.spl` (§4) — read it for the exact FFI call
  sequence/error-handling convention, but do not import/extend it directly (2D
  session concerns — texture/render-pass state — don't belong in gpu_lane; the
  new file is a clean-room lane session using the same underlying `rt_metal_*`
  calls, shaped like `vulkan_lane_session.spl`, not like `MetalSession`).

## 4. New layer: `metal_lane_session.spl`

`src/lib/gc_async_mut/gpu_lane/metal_lane_session.spl`. Mirrors
`vulkan_lane_session.spl`'s shape (§3 above — Metal, like Vulkan, needs a
pipeline before any dispatch):

```
class MetalLaneSession:
    static fn create() -> MetalLaneSession
    static fn create_for_device(ordinal: i64) -> MetalLaneSession
    me probe() -> text          # host-aware: "" (device usable) or "skip: <reason>"
    me init(arena_bytes: i64, lane_msl: text, entry: text) -> text
        # bundles: device init, command queue, MTLBuffer alloc (arena), MSL
        # compile via rt_metal_compile_shader, pipeline create -- mirrors
        # VulkanLaneSession.init's "init bundles pipeline creation" shape
    me arena_write(data: [u8]) -> bool
    me arena_read(byte_count: i64) -> [u8]
    me dispatch_once(grid_x: i64) -> text   # mirrors Vulkan's dispatch_once, not
                                             # CUDA's launch_once(grid,block,args)
                                             # -- Metal's MTLSize threadgroup shape
                                             # is closer to Vulkan's workgroup model
    me shutdown() -> text
```

No `retry_terminal_completion` equivalent is assumed up front (that was added to
`VulkanLaneSession` for a specific Vulkan device-lost-recovery need) — add it only
if Metal's own failure semantics (`MTLCommandBufferStatus.error`) demonstrate the
same need during implementation; don't speculatively port it.

**Probe contract**: `probe_gpu_driver_present("metal")` /
`probe_gpu_symbols("metal")` (§7) must be added to
`src/lib/nogc_sync_mut/test_runner/gpu_lane_common.spl`'s existing per-backend
dispatch, following the exact pattern already there for `"cuda"`/`"vulkan"` —
for Metal this checks `rt_metal_is_available()` returning true AND
`target_os == "macos"`, not a `dlopen` probe.

## 5. New layer: `metal_vm_executor.spl` (SVM-G interpreter on Metal)

`src/lib/gc_async_mut/gpu_lane/metal_vm_executor.spl`. Same GMB-1 arena / SGP
header / SVM-G opcode contract as `cuda_vm_executor.spl`/`vulkan_vm_executor.spl`
(byte-for-byte identical layout — this is the whole point of SVM-G being a
*shared* bytecode VM per parent design §4.5: "two implementations, one
conformance suite"). Reimplement the arena builder/decoders locally in this file
(not shared/imported), matching the existing convention documented in both
sibling files' module docstrings ("reimplemented here... for the same tier-
ownership reason").

Required: `build_svmg_arena`, `build_svmg_arena_persisting_data` (mirror the
absolute-offset-copy fix landed today in the CUDA/Vulkan siblings — see
`doc/08_tracking/bug/vulkan_vm_executor_run_source_clobbers_arena_data_each_call_2026-08-08.md`'s
"2026-08-08 follow-up" for the exact correct algorithm; do NOT reintroduce the
relative-offset bug that class of fix corrected twice already today), `read_log`,
`read_records`, `class MetalVmExecutor` with `create`/`init(kernel_bytes)`/
`run_source`/`run_source_persisting_data`/`shutdown`.

The one real new piece: **the SVM-G reference kernel must be authored in MSL**
(`svmg_metal_kernel.metal` or `.msl`, checked in alongside the existing
`svmg_cuda_kernel.ptx`/`svmg_vulkan_kernel.spv`, next to a `.sha256` per the
existing convention). This is a **port**, not a new design — D2's host reference
VM (`ref_vm.spl`) and D1's assembler already define the exact opcode/byte
semantics; the MSL kernel is a third device-side reimplementation of
`SvmgVm.step`/`run` against the identical GMB-1 wire format, exactly as the
existing module docstrings describe the CUDA/Vulkan kernels' relationship to
`ref_vm.spl`. Conformance is proven the same way: run every D3 vector through
this kernel and diff against `ref_vm.run()` on the same assembled bytes (see §7).

**Watch the two known cross-backend divergences already found and documented for
CUDA/Vulkan** (do not treat these as new Metal bugs if reproduced — reference the
existing bug docs and extend them):
- `doc/08_tracking/bug/svmg_a2_record_ring_head_counter_diverges_from_d2_ref_vm_2026-08-07.md`
  (RECORD ring layout convention divergence).
- `doc/08_tracking/bug/svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07.md`
  (single code+data buffer means a STORE into DATA can self-modify adjacent CODE
  on any single-buffer device — likely reproduces identically on Metal since
  Metal's `MTLBuffer` arena is single-buffer same as CUDA/Vulkan's arena;
  confirm the exact same `mem_store_load_byte` vector diverges the exact same
  way before assuming it's device-specific).

## 6. New layer: `metal_jit_lane_executor.spl` + notebook wiring

`src/lib/gc_async_mut/gpu_lane/metal_jit_lane_executor.spl`: `class
MetalJitLaneExecutor` — `create`/`prepare`/`run_program(blob) -> Result<[u8],
text>`/`lane_log_text`/`lane_log_records`/`lane_sentinel`/`teardown`, mirroring
`vulkan_jit_lane_executor.spl`'s shape (kernel format = MSL via
`src/compiler/70.backend/backend/metal/msl_builder.spl`, §3).

**Do this AFTER the CUDA JIT-lane arbitrary-source-compile gap lands** (tracked
in `notebook_cuda_exec_jit_lane_not_implemented_2026-08-08.md`, in progress
concurrently) — reuse whatever "Simple cell source → backend codegen → device
artifact → `run_program`" pattern that work establishes, applied to MSL instead
of PTX. If that work hasn't landed yet when this stream starts, build the
FFI/session/dispatch plumbing (which has no dependency on it) and stub
`run_program` the same honest way CUDA currently does — a clear `Blocked`
diagnostic citing this design doc, not a silent no-op or a fixed demo kernel.

`src/lib/nogc_sync_mut/notebook/metal_exec.spl`: new `MetalExec`/
`MetalExecFactory` implementing the `NotebookExecutor` trait
(`src/lib/nogc_sync_mut/notebook/executor.spl`), mode_spec parsing via the
existing `extract_base_runtime`/`extract_gpu_submode` helpers
(`std.test_runner.test_executor_composite_parse`), following `vulkan_exec.spl`'s
per-launch-only shape (§2) — both `interpreter(remote(metal(...)))` and
`jit(remote(metal(...)))` submodes route through this one file, same as CUDA/
Vulkan's exec files handle both their own submodes.

Wire into the factory dispatch in `executor.spl` (`create(mode_spec)`) alongside
the existing cuda/vulkan branches.

## 7. Vulkan JIT notebook gap (parallel, independent stream)

Two parts, can be one PR:

1. **`vulkan_jit_lane_executor.run_program`'s fixed-kernel limitation** — same
   class of gap as CUDA's (§6's dependency note applies here too: reuse whatever
   pattern the CUDA fix establishes for "arbitrary cell source → backend codegen
   → device artifact", applied to `src/compiler/70.backend/backend/vulkan/spirv_builder.spl`
   instead of `cuda/ptx_builder.spl`).
2. **Add the missing `jit` branch to `vulkan_exec.spl`** — today the file has
   *zero* references to `jit`/`remote(vulkan` mode routing (confirmed via
   direct grep — this is not even a stub, unlike CUDA's explicit `Blocked`
   diagnostic). Add `probe()`/`execute_cell()` handling for
   `jit(remote(vulkan(...)))` mode specs, mirroring the shape CUDA's exec file
   uses for its own `jit` branch (`extract_gpu_submode(mode_spec)` dispatch),
   routing to `VulkanJitLaneExecutor.run_program`. Until (1) lands, this can
   legitimately be an honest `Blocked` diagnostic (same pattern CUDA already
   uses) rather than blocked entirely on (1) landing first — having *a* code
   path that clearly says "not yet implemented" is strictly better than having
   no code path (today's state), even before (1) makes it actually run
   arbitrary code.

## 8. Grammar extension

Per parent design §2 ("Grammar Extension"): add `metal` as a valid backend
token in the composite mode-spec grammar/extractor
(`std.test_runner.test_executor_composite_parse` and wherever the top-level
`remote(...)` backend enum is validated — grep for where `"cuda"`/`"vulkan"`
are currently the only two accepted backend literals). Per §1 Non-Goals: the
grammar MUST reject `metal(...(resident))` the same way it already rejects
`vulkan(...(resident))` per parent design §6.3 — add the same prohibition, not
a new one from scratch (there should be an existing negative/rejection test to
mirror for Vulkan's resident-rejection; write Metal's analog).

## 9. Testing / verification strategy (host-aware, real for Mac, skip-clean for Linux)

**No mocked emulation.** Per this repo's testing rules and this session's
established practice for CUDA/Vulkan, specs must exercise the REAL device via
the REAL FFI path, using the exact same `probe_gpu_driver_present`/
`probe_gpu_symbols`/`route_gpu_lane` skip-clean contract already proven for
CUDA/Vulkan (`src/lib/nogc_sync_mut/test_runner/gpu_lane_common.spl`). On this
session's Linux dev host, every Metal spec will hit the `skip:` branch (no
`target_os=="macos"`, so `probe()` returns `skip: <reason>` immediately) — this
is the SAME behavior CUDA/Vulkan specs correctly exhibited on non-GPU hosts
before this session had access to the current dual-GPU Linux box. It is not a
weaker guarantee; it's the identical contract, just currently un-exercised for
lack of hardware, exactly as documented in each spec's own header comment
("Clean host-aware skip... when no [X] driver/ICD/framework is present").

Required new specs, mirroring the CUDA/Vulkan file set exactly:
- `test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl` — full D3
  vector table against `MetalVmExecutor`, same shape as
  `cuda_vm_executor_conformance_spec.spl`/`vulkan_vm_executor_conformance_spec.spl`
  (including today's lesson: isolate any intentionally-timing-out vector into
  its own session — see `doc/08_tracking/bug/cuda_vm_executor_conformance_array_index_out_of_bounds_2026-08-08.md`
  for why a shared session across a timeout vector poisons every subsequent
  vector).
- `test/03_system/gpu_lane/metal_jit_hello_spec.spl` — mirrors
  `cuda_jit_hello_spec.spl`/`vulkan_jit_hello_spec.spl`.
- `test/02_integration/app/tools/notebook/metal_exec_spec.spl` — mirrors
  `cuda_exec_spec.spl`/`vulkan_exec_spec.spl` (cross-cell arena persistence,
  interrupt/`%reset` recovery).
- Grammar-level rejection test for `metal(...(resident))`, mirroring whatever
  covers Vulkan's rejection today.

**"Prepare tests for Mac"**: writing these specs in the standard host-aware
form above IS the preparation — no separate/different Mac-specific spec
variant is needed or wanted (that would violate the "one spec, host-aware"
contract every other lane already follows). What IS worth doing explicitly:
document in each new spec's header comment, and in this design doc's
`doc/08_tracking/lane_matrix.md` entry (§10), the EXACT verification command
and expected real-hardware outcome, so that whenever this code is next run on
an actual Mac (this session, a future session, or a human), there is a
precise, unambiguous "run this, expect this" checklist rather than needing to
re-derive it. Add a short `doc/08_tracking/bug/metal_gpu_lane_never_verified_on_real_mac_hardware_2026-08-09.md`
tracking doc the moment implementation lands, explicitly filed (not silently
implied) exactly as this session's own standing rule requires
("Explicitly OUT of scope (filed, not forgotten)" pattern used throughout
today's notebook-lanes work) — this is not a defect, it's an honest
disclosure that the SKIP path, not the PASS path, is all that's been
exercised so far.

## 10. `doc/08_tracking/lane_matrix.md` updates

Add two new rows (`metal_jit`, `metal_vm`) following the exact column format
of the existing 5 GPU rows, `Status on this host` column reading something
like: "Not yet verified — host-aware skip-clean, this host has no macOS/Metal;
implementation complete and spec exists, real-hardware pass/fail unknown until
run on a Mac (see `metal_gpu_lane_never_verified_on_real_mac_hardware_2026-08-09.md`)."
Update the existing `vulkan_jit` row once §7 lands to note the jit-submode
notebook-lane gap closure (today's row text is about the standalone executor,
which already works — the notebook-lane gap was never reflected there since
`lane_matrix.md` tracks the standalone executor/spec pairing, not the
notebook `mode_spec` routing layer; §7's fix belongs in
`notebook_lanes_architecture.md`'s own status tracking, not this table).

## 11. Definition of done (this design)

- `metal_lane_session.spl`, `metal_vm_executor.spl`, `metal_jit_lane_executor.spl`,
  `metal_exec.spl` exist, lint clean, wired into the notebook executor factory.
- Grammar accepts `remote(metal(...))`, rejects `remote(metal(...(resident)))`.
- All 4 new specs exist, are host-aware skip-clean, and SKIP cleanly (not fail)
  on this session's Linux host — verified by actually running them, not assumed.
- Vulkan notebook `jit(remote(vulkan(...)))` has a real code path (§7) — at
  minimum an honest `Blocked` diagnostic if the underlying arbitrary-source
  compile isn't ready yet, ideally a working implementation if the CUDA
  pattern has landed by the time this stream executes.
- `lane_matrix.md` updated, `metal_gpu_lane_never_verified_on_real_mac_hardware_2026-08-09.md`
  filed.
- No existing CUDA/Vulkan/2D-rendering-Metal spec regresses.
