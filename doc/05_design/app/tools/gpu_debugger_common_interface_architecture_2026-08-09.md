# GPU Debugger — Common Interface over CUDA / Vulkan / Metal

**Status: SUPERSEDED (2026-08-09)** by
`doc/05_design/app/tools/unified_debug_profile_capability_architecture_2026-08-09.md`
and its plan
`doc/03_plan/agent_tasks/unified_debug_profile_capability_parallel_plan_2026-08-09.md`,
which landed the debug capability as one half of a unified debug+profile
capability. The D1/D3 protocol content here was inherited by streams P5/P6 and
is still accurate as background; the acquisition/`.from()` shape is NOT — it was
measured unsound under value semantics. Do not implement from this document.
Read the unified design's §3 CORRECTION block instead.

**Status:** Design, not yet implemented (implementation tracked in
`doc/03_plan/agent_tasks/gpu_debugger_common_interface_parallel_plan_2026-08-09.md`)
**Parent designs:**
`doc/05_design/runtime/gpu_remote_interpreter_architecture.md` (SVM-G/GMB-1,
§5.4 cuda-gdb exploratory note),
`doc/05_design/app/tools/metal_gpu_lane_and_vulkan_jit_notebook_architecture_2026-08-09.md`
(Metal lane, host-aware skip contract),
`src/app/dap/` (existing Debug Adapter Protocol server, ~3,000 lines — the
IDE-facing surface this design plugs into).

## 1. Goals / Non-Goals

**Goals:**
1. One common debugger interface (`GpuDebugSession` trait) over all three GPU
   backends, letting a caller set breakpoints, step, resume, and inspect VM
   state for code running on a GPU lane — with the SAME API regardless of
   backend.
2. IDE integration: expose GPU debug sessions through the EXISTING DAP server
   (`src/app/dap/`), so VS Code and any DAP-capable IDE can drive a GPU debug
   session the same way they debug a plain `.spl` file today.
3. Notebook integration: a notebook cell running on a GPU lane can be debugged
   (breakpoint inside the cell's program, step, inspect) via a Lab/Jupyter
   entry point built on the same trait.
4. Metal parity at the interface and unit-test level: the Metal wrapper is
   implemented and unit-tested like the others; its live-device (env) tests
   are host-aware skip-clean and will first actually run on a real Mac —
   the same honest contract as the Metal lane design (§9 there).

**Non-Goals:**
- Debugging arbitrary native/JIT kernels with vendor tools as the PRIMARY
  mechanism. `cuda-gdb` exists but is CUDA-only and MI-scripting it is the
  parent design's own "Exploratory P3"; Vulkan and Metal have NO scriptable
  step-debugger for headless compute (RenderDoc is capture-based, Xcode's
  Metal debugger is GUI-only). A "common interface" that only CUDA can
  implement is not common. Vendor-tool adapters are therefore an OPTIONAL
  P3 extension behind the same trait (§8), not the foundation.
- Watchpoints, reverse execution, multi-warp/threadgroup debugging. SVM-G is
  single-lane (1 thread) by design — the debugger inherits that.
- Debugging the `local` (host) notebook lane — already covered by the
  existing DAP server's source-level session.

## 2. Core insight: debug the VM, not the vendor

The `interpreter(remote(X(...)))` lanes all run ONE shared bytecode VM
(SVM-G) whose semantics this repo fully owns, with a byte-identical GMB-1
arena on every backend. A debugger implemented at the SVM-G level —
breakpoint on bytecode `pc`, single-step the VM, read the operand stack and
DATA region — is automatically identical across CUDA, Vulkan, and Metal,
because it debugs the VM contract, not the vendor runtime. This is the same
move the lane architecture already made for execution ("two implementations,
one conformance suite") applied to debugging.

Source-level mapping (breakpoint on a Simple source line rather than a
bytecode pc) is a thin layer on top: D1's assembler (`svmg_asm`) is where
source→pc mapping information exists; §6 covers emitting it as a debug map.

## 3. SVM-G protocol extension: DBG-1 (the one real protocol change)

Verified current state: the VM's execution state (`pc`, `sp`, `csp`, operand
stack, call stack — see `ref_vm.spl`'s `SvmgVm` fields) is kernel-local and
LOST between launches. The arena's REG block
(`mailbox_const.spl:28-36`) is only the mailbox command block, not VM state.
Therefore resume-after-break requires a protocol extension. Keep it minimal:

**DBG-1 debug block** — a new fixed-offset region in the arena (exact offset
chosen during implementation from the existing free space between the REG
block/rings and `ARENA_TOTAL_SIZE`; document it in `mailbox_const.spl` next
to the existing offsets):

```
DBG_FLAGS        u32   bit0: debug enabled; bit1: resume-from-saved-state;
                       bit2: single-step (break after 1 instruction)
DBG_BREAK_COUNT  u32   number of active breakpoints (cap: 16)
DBG_BREAK_PCS    u32[16]  bytecode pc values to break on
DBG_SAVED_PC     u32   ┐
DBG_SAVED_SP     u32   │ written by the kernel when it halts for ANY reason
DBG_SAVED_CSP    u32   │ (breakpoint, single-step, budget, HALT, TRAP);
DBG_SAVED_STACK  u32[OPERAND_STACK_SIZE]  │ restored at launch when bit1 set
DBG_SAVED_CALLS  u32[CALL_STACK_SIZE]     ┘
```

**Kernel changes** (identical semantics in all four implementations —
`ref_vm.spl`, `svmg_cuda_kernel.ptx`, `svmg_vulkan_kernel.spv`,
`svmg_metal_kernel.metal` once the Metal lane lands):
1. At launch: if `DBG_FLAGS.bit1`, load pc/sp/csp/stacks from the DBG block
   instead of starting fresh at `entry_pc`.
2. In the dispatch loop: if `DBG_FLAGS.bit0`, before executing each
   instruction compare `pc` against the breakpoint table; on hit, or when
   `bit2` (single-step) is set after one instruction, save state to the DBG
   block and halt with a new sentinel `SENTINEL_DEBUG_BREAK`
   (`0xCAFE00Dx` family, exact value chosen alongside the existing
   `SENTINEL_TIMEOUT`/`SENTINEL_EXIT_MASK` constants in `mailbox_const.spl`).
3. On EVERY halt (including normal HALT/TRAP/budget), save state to the DBG
   block when `bit0` is set — so "why did it stop" is always inspectable.

When `DBG_FLAGS == 0` the kernel behavior is byte-for-byte today's behavior —
zero cost, zero risk to the existing conformance suite (this MUST be asserted
by re-running the existing conformance specs unchanged, §9).

**Conformance:** debug semantics are part of the SVM-G contract, so they get
conformance vectors like everything else: a small D3-style table of debug
scenarios (break at pc, step N times, resume to completion, break-in-loop,
resume-with-persisted-arena) executed against `ref_vm` and each device
kernel, compared field-for-field. This is what makes the Metal wrapper
meaningfully testable without a Mac: the SAME vector table runs against
`ref_vm` (host, runs everywhere, proves the protocol) and against each
device (host-aware skip on absent hardware).

## 4. Common interface: `GpuDebugSession` trait

New file `src/lib/gc_async_mut/gpu_lane/gpu_debug_session.spl`:

```
struct GpuDebugState:
    pc: i64
    sp: i64
    csp: i64
    stack: [i64]          # operand stack, live entries only (sp deep)
    call_stack: [i64]     # return addresses, csp deep
    stop_reason: text     # "breakpoint" | "step" | "halt" | "trap" |
                          # "timeout" | "running" | "not-started"
    sentinel: i64

trait GpuDebugSession:
    fn backend() -> text                       # "cuda" | "vulkan" | "metal"
    me attach(source: text, step_budget: i64) -> text   # ""=ok | "skip:..." | error
    me set_breakpoint(pc: i64) -> bool         # false when table full (16)
    me clear_breakpoint(pc: i64) -> bool
    me breakpoints() -> [i64]
    me resume() -> GpuDebugState               # run until break/halt/budget
    me step() -> GpuDebugState                 # exactly one instruction
    me state() -> GpuDebugState                # last stop state, no execution
    me read_data(offset: i64, len: i64) -> [u8]   # DATA region inspection
    me write_data(offset: i64, bytes: [u8]) -> bool # poke (debugger writes)
    me detach() -> text
```

Three thin implementations, each delegating to its existing lane session +
arena builder (they add NO new device logic beyond DBG-1):
- `cuda_debug_session.spl` → `CudaLaneSession` + cuda arena helpers
- `vulkan_debug_session.spl` → `VulkanLaneSession` + vulkan arena helpers
- `metal_debug_session.spl` → `MetalLaneSession` (from the Metal lane plan,
  stream N2) + metal arena helpers

Plus a fourth, deliberately: `ref_debug_session.spl` wrapping `ref_vm.spl`'s
host `SvmgVm` behind the same trait. This is load-bearing, not a toy: it (a)
lets ALL interface-level unit tests run on any host with no GPU, (b) is the
conformance oracle for the device implementations, and (c) gives notebooks/
IDEs a working debug target even on GPU-less machines.

`resume()`/`step()` are implemented as: write DBG flags + breakpoint table
into the arena, dispatch once (`launch_once`/`dispatch_once`), read back the
DBG block + sentinel, decode to `GpuDebugState`. Cross-launch continuity uses
the same persisted-arena mechanism the notebook lanes already use
(`build_svmg_arena_persisting_data` — absolute-offset copy; the DBG block
persists the same way the LOG/RECORD rings do).

Factory: `gpu_debug_session_for(mode_spec: text) -> GpuDebugSession` parsing
the same composite mode-spec grammar as the notebook executors
(`extract_remote_backend`), so `interpreter(remote(cuda(sm80)))` etc. select
the right implementation, and `ref` (or absent remote) selects the host VM.

## 5. DAP integration (IDE story)

Extend the existing DAP server (`src/app/dap/`) with a second session kind.
Today `SimpleDapSession` is source-backed local. Add `GpuDapSession` selected
by launch-config: `{"type": "simple", "gpuModeSpec": "interpreter(remote(cuda(sm80)))",
"program": "cell.spl" | inline source}`. Mapping is mechanical:
- DAP `setBreakpoints` (source lines) → debug map (§6) → `set_breakpoint(pc)`
- DAP `continue`/`next`/`stepIn` → `resume()`/`step()` (SVM-G has no
  source-line granularity difference between next/stepIn at v1 — both map to
  `step()`; document this in the response's `granularity`)
- DAP `stackTrace` → synthesized from `call_stack` + debug map
- DAP `variables`/`evaluate` → `read_data` over the DATA region + debug map's
  variable-slot table (§6); v1 may expose raw `pc/sp/stack` registers and a
  hex DATA view when no map is available — honest and still useful
- DAP `stopped` event reason ← `stop_reason`

Keep this in new files under `src/app/dap/` (e.g. `gpu_session.spl`,
`gpu_adapter.spl`) — do not restructure the existing local session; the
protocol/transport/server layers are shared as-is.

## 6. Debug map (source→pc), minimal v1

`svmg_asm` (D1 assembler) already walks source to emit bytecode. Extend it
with an optional side-table output: `[(source_line, pc)]` pairs plus, if
cheaply available, `(name, DATA offset)` for named globals. New pure struct
`SvmgDebugMap` in `src/lib/common/svmg/debug_map.spl`, produced by a new
`svmg_asm_with_map(...)` entry point (existing `svmg_asm` untouched, callers
unaffected). Line-level fidelity only — no column/expression mapping at v1.

## 7. Notebook integration

`%debug` cell magic (K3's magics dispatch already exists) or Lab API —
minimal v1: a Lab HTTP endpoint pair on `lab_server.spl`
(`POST /api/lab/sessions/:sid/cells/:cid/debug` to start a debug session for
a cell's source on that session's lane; `POST .../debug/step|resume|break`
driving the trait; `GET .../debug/state` returning `GpuDebugState` as JSON).
The Lab UI story (gutter breakpoints etc.) is OUT of v1 scope — the endpoints
+ the DAP path give IDEs and tooling full access first; UI chrome can follow.

## 7b. Simple config: no tags needed — bare `gpu` distinguishes host vs GPU

Requirement (user, 2026-08-09): the verbose composite tags
(`interpreter(remote(cuda(sm80)))`) must not be REQUIRED. With a simple
config in place, users write no tag at all for host execution, and just
`gpu` to run/debug on the GPU — backend and submode come from config or
auto-probe.

**Config** (SDN, per repo rules — never JSON/YAML): a `[gpu]` section in the
existing project config file (find the existing config the toolchain already
reads — e.g. simple.sdn / lab config — and extend it; do NOT invent a new
config file if one exists):

```
gpu:
  backend: auto        # auto | cuda | vulkan | metal
  submode: interpreter # interpreter | jit
  arch: auto           # auto -> sm80 / spv15 / msl2 per backend default
```

**Resolution order** (one shared helper, `resolve_gpu_mode_spec(tag, config)
-> text`, in `src/lib/nogc_sync_mut/notebook/` or alongside the composite
parser — single implementation used by notebook magics, Lab API, DAP launch
config, and `gpu_debug_session_for` alike):
1. Explicit full mode-spec given → use it verbatim (power users unaffected).
2. Bare `gpu` tag (cell magic `%gpu`, DAP `"gpu": true`, Lab API
   `{"gpu": true}`) → expand from config: `<submode>(remote(<backend>(<arch>)))`.
   `backend: auto` probes in order cuda → vulkan → metal using the existing
   per-backend `probe()` and picks the first non-skip; if none available,
   honest error listing each backend's skip reason.
3. No tag → host (local lane / `ref_debug_session` for debugging). Bare
   `gpu` vs nothing is the ONLY distinction a casual user ever needs.

The verbose grammar remains the canonical internal representation — the
resolver expands to it, nothing downstream changes. Tests: unit-test the
resolver's full matrix (explicit / gpu+config / gpu+auto-probe-fallback /
no-tag / no-backend-available error) with a fake probe injection — no device
needed.

## 8. Vendor-tool adapters (optional P3, behind the same trait)

`cuda-gdb` MI adapter (parent design §5.4) can later implement
`GpuDebugSession` for the `jit(remote(cuda(...)))` lane — real
source-level device debugging of JIT kernels, CUDA-only. It slots behind the
same trait and DAP plumbing built here, which is exactly why the trait, not
cuda-gdb, is the foundation. No Vulkan/Metal equivalent exists; do not
pretend otherwise in any doc or diagnostic — `jit(...)` mode specs passed to
`gpu_debug_session_for` return an honest
`"skip: jit-lane debugging requires a vendor adapter (cuda-gdb: P3, filed; vulkan/metal: no scriptable debugger exists)"`.

## 9. Testing strategy (unit everywhere, env host-aware)

Per the user's explicit requirement: Metal might not be fully verifiable
here, but unit tests MUST run, and env (live-device) tests MUST exist.

**Tier 1 — unit tests (run on every host, no GPU needed):**
- `test/01_unit/lib/svmg/debug_map_spec.spl` — assembler map correctness.
- `test/01_unit/lib/gpu_lane/gpu_debug_session_ref_spec.spl` — the FULL
  trait contract driven against `ref_debug_session` (breakpoint hit, step,
  resume, stack/state decode, read/write_data, breakpoint-table-full,
  detach). This is the primary behavioral spec of the whole feature.
- `test/01_unit/lib/gpu_lane/dbg1_block_encode_spec.spl` — DBG-1 block
  encode/decode round-trip, flag semantics, offsets don't collide with
  existing arena regions (assert against `mailbox_const` values).
- Per-backend wrapper unit tests (`cuda/vulkan/metal_debug_session_unit_spec.spl`)
  — everything testable WITHOUT a device: mode-spec routing, probe
  short-circuit ("skip:" propagation), DBG block construction, state decode
  from a synthetic readback arena. Metal's run on Linux — that is the
  point.
- DAP mapping unit tests — request/response mapping against
  `ref_debug_session` (no device, no IDE needed: feed DAP JSON, assert
  responses), extending the existing DAP spec pattern.

**Tier 2 — env tests (live device, host-aware skip-clean):**
- `test/03_system/gpu_lane/cuda_debug_session_env_spec.spl`
- `test/03_system/gpu_lane/vulkan_debug_session_env_spec.spl`
- `test/03_system/gpu_lane/metal_debug_session_env_spec.spl`
Each runs the debug conformance vector table (§3) on the real device and
diffs against `ref_vm` results. Same probe/skip contract as every other
gpu_lane spec. On this Linux host: CUDA and Vulkan run for real (hardware
present); Metal SKIPs with the correct reason — and that skip PATH itself is
asserted (spec must produce `skip:` cleanly, not crash), which is a real,
runnable-today test of the Metal wrapper's probe logic.
- Existing conformance suites re-run UNCHANGED (`cuda_vm_executor_conformance_spec`,
  `vulkan_vm_executor_conformance_spec`) — proves DBG_FLAGS==0 changes nothing.

**Explicit disclosure:** extend (or file alongside) the Metal lane plan's
`metal_gpu_lane_never_verified_on_real_mac_hardware` tracking doc to cover
the debug wrapper — Metal debug env spec exists, skip-path verified, device
path pending first run on a Mac.

## 10. Definition of done

- DBG-1 documented in `mailbox_const.spl` + this doc; implemented in
  `ref_vm.spl` and the CUDA + Vulkan kernels (Metal kernel: implemented
  together with, or immediately after, the Metal lane's N3 kernel port —
  whichever stream lands second wires it).
- `GpuDebugSession` trait + ref/cuda/vulkan/metal implementations + factory,
  lint clean.
- Debug conformance vectors pass on ref (host) AND live CUDA AND live Vulkan
  on this host; Metal skip-path asserted.
- DAP GPU session type works end-to-end against `ref_debug_session`
  (unit-tested) and against live CUDA (env-tested).
- Lab debug endpoints respond with real state against ref + live CUDA.
- All Tier-1 unit specs green on this host including the Metal wrapper's.
- Existing conformance/notebook specs unchanged and green (no regression).
- `lane_matrix.md` gains a "debug" note per lane; tracking doc for Metal
  device-path-pending filed.
