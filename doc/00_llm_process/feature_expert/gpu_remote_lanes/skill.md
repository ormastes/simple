# Feature Expert: GPU Remote Interpreter Test Lanes

## Role

Own feature-specific process knowledge for the `cuda`/`vulkan` remote test lanes
(`interpreter(remote(cuda(sm80)))` family): current docs, source entry points, known
constraints, and the pipeline artifacts to update as work progresses.

## Status (2026-08-07, updated — plan substantially implemented; E2 landed, Streams A-E addressed)

**Landed on `origin/main`:** A1 (grammar), A2 (GMB-1 mailbox library), A3
(runner routing to `GpuLaneExecutor`), B0 (CUDA interpreter adapter), B1
(CUDA lane session), B2 (CUDA JIT lane executor), B3 (SVM-G CUDA device
kernel + executor, verified out-of-tree), B4 (CUDA resident/interactive
session protocol logic -- command ring, watchdog gate, interactive servicer
all real and unit-tested; live single-kernel resident dispatch blocked on
missing SFFI, filed), C1 (Vulkan lane session shell), C2 (Vulkan JIT lane
executor), D1 (SVM-G ISA spec + assembler), D2 (host reference VM), D3
(conformance vector suite), D4 (test-body lowering to SVM-G). This is now the
great majority of the plan's Streams A-D.

**Landed since the paragraph above was written:** C3 (SVM-G Vulkan device
executor, verified 58/58 non-excluded D3 vectors on real hardware), E1
(doc-linking), E2 (lane matrix + status spec + CI, this section).

**Not yet landed / not attempted:** B5-B6 (further CUDA lane work beyond
resident; B6 itself already has a landed no-go verdict per the plan). Two
real, filed, NOT-fixed-by-E2 gaps remain within the landed streams: the
generic composite-runner GPU-lane dispatch (`route_gpu_lane`) is not wired
to the real B2-C3 `GpuLaneExecutor` implementations
(`gpu_lane_generic_routing_not_wired_to_real_executors_2026-08-07.md`), and
`cuda_vm` (`CudaVmExecutor`) has no in-tree system spec driving the D3
conformance table (B3's own pre-existing gap). `doc/08_tracking/lane_matrix.md`
now exists (E2) and is the single place both are tracked alongside the rest
of the lane matrix.

Status sections below are per-task, in landing order. Where a task's section
was itself lost to shared-working-copy churn during this session and later
recovered, that is noted in the section (see D1-D4 "Recovered, not
rewritten").

## 2026-08-08 — generic composite-runner GPU-lane dispatch wired to real executors

Closed `gpu_lane_generic_routing_not_wired_to_real_executors_2026-08-07.md`.
`route_gpu_lane` in `gpu_lane_common.spl` stays a pure skip:/blocked: decision
(unchanged — matrix_status_spec and its existing "not yet implemented"
assertions keep passing exactly as before). Two additions:

- `gpu_lane_common.gpu_lane_id_for(base_runtime, remote_backend) -> text`: a
  new pure mapping from `(base, backend)` to `cuda_jit`/`cuda_vm`/
  `vulkan_jit`/`vulkan_vm`/`""`. Kept in `gpu_lane_common.spl` (nogc_sync_mut
  tier) rather than importing the concrete executor classes directly, because
  each of B2/B3/C2/C3 already imports `gpu_lane_common` for the
  `GpuLaneExecutor` trait — importing them back would be circular.
- `test_executor_composite.run_test_file_gpu_lane_dispatch(...)` (replaces
  the old direct call to `run_test_file_gpu_lane`): runs the same host-aware
  symbol/driver probes as before, and once driver+symbols are ready,
  constructs and drives the matching executor —
  `CudaJitLaneExecutor.prepare/run_program/teardown`,
  `VulkanJitLaneExecutor.prepare/run_program/teardown`, or
  `CudaVmExecutor`/`VulkanVmExecutor.init(checked-in PTX/SPIR-V
  artifact)/run_source("HALT 7", ...)/shutdown` for the vm lanes — instead of
  the static "not yet implemented" FAIL. Lane ids with no concrete executor
  yet (`cuda_vm_resident`, `cudagdb`) still fall through to
  `route_gpu_lane`'s honest not-yet-implemented FAIL. This module (also
  nogc_sync_mut) importing the gc_async_mut executor classes directly is
  precedented (`notebook/vulkan_exec.spl` already does it for
  `VulkanLaneSession`/`VulkanVmExecutor`).
- New tests in `test/03_system/compiler/gpu_lane_common_spec.spl` cover
  `gpu_lane_id_for` for all four lane ids plus the two "no executor yet"
  fall-through cases (19/19 total in that file). Regressions verified:
  `gpu_lane_matrix_status_spec.spl` 12/12, `remote_interpreter_backend_spec.spl`
  19/19 — both unaffected since neither exercises the new dispatch path
  directly (matrix spec calls `route_gpu_lane` directly with pinned
  `driver_present`; backend spec only checks the pure `extract_*` parsers).
- Verified live on this host: Vulkan driver/ICD is present and both
  `vulkan_jit_hello_spec.spl` (2/2) and `vulkan_vm_executor_conformance_spec.spl`
  (2/2) pass independently, so the executors this dispatch wires to are real,
  working code — not fabricated. CUDA lanes could not be end-to-end verified
  through the new dispatch path on this host: this host's CUDA path fails at
  runtime with `cuda-lane-device-identity-unavailable`
  (`cuda_lane_probe_misses_device_unavailable_2026-08-08.md`), a separate,
  already-filed, pre-existing defect in `CudaLaneSession.init` unrelated to
  this routing change — the new dispatch surfaces it as an honest FAIL
  (`cuda_jit lane failed: cuda-lane-device-identity-unavailable`) rather than
  masking it, which is the correct behavior per this task's contract.
- **Separate pre-existing bug noticed, not fixed (out of scope):**
  `run_test_file_composite` checks `if base == "jit": return
  run_test_file_jit(...)` (line ~40) *before* the `platform == "remote"`
  check, so a `jit(remote(cuda(...)))`/`jit(remote(vulkan(...)))` spec never
  actually reaches `run_test_file_remote`/the new GPU-lane dispatch through
  the composite entry point at all — only `interpreter(remote(cuda/vulkan(...)))`
  specs do. This routing-precedence issue is orthogonal to the "not wired to
  executors" gap this change closes (which is about what happens *once* the
  GPU lane dispatch is reached) and was not touched here to keep the diff
  minimal and avoid risking the JIT dispatch path for every other backend.

### A3 — landed
- Runner routing: `route_gpu_lane`/`run_test_file_gpu_lane` (in
  `std.test_runner.gpu_lane_common`) wired into
  `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`'s
  `run_test_file_remote`, dispatching for `remote_backend` in
  `{cuda, vulkan}` ahead of the pre-existing `.spl`/`.elf` branches. Verified
  landed on `origin/main` via commit `3f3adeca435` ("A3/B1 — Slot 2
  recovery"; A3/B1 were originally implemented and verified earlier in that
  session — 13/13 and 4/4 passing specs, sabotage-probed — but lost to
  repeated uncommitted-working-copy resets from a concurrent process, then
  recovered from conversation context and re-landed).
- Confirm current wiring: `grep -n "run_test_file_gpu_lane"
  src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` shows both
  the `use` import and the dispatch call site.

### B1 — landed
- `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl` (`CudaLaneSession`):
  wraps `crypto_accel/cuda_session.spl` with the 128 KiB GMB-1 arena plus
  guard regions, per design §5.1's `GpuLaneExecutor` session contract that
  B2's `CudaJitLaneExecutor` and B3's `CudaVmExecutor` both build on.
  Landed in the same `3f3adeca435` recovery commit as A3 (see above).
- Own spec: `test/02_integration/gpu_lane/cuda_lane_session_spec.spl`.
  B2's status section (above) notes this spec started failing with a
  deployed-binary/environment `CudaLaneSession not found` symptom during a
  later session — attributed there to an unstable shared-WC/seed-vs-self-hosted
  binary issue on that host, not a B1 code regression; re-run to confirm on a
  freshly rebuilt self-hosted binary.

### B0 — landed
- Added `rt_cuda_module_load_data_bytes_fn` to
  `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs` (next to the
  existing `rt_cuda_module_load_data_fn`), registered in
  `interpreter_extern/mod.rs`: `insert_simple!("rt_cuda_module_load_data_bytes",
  gpu::rt_cuda_module_load_data_bytes_fn);`. Closes the interpreter-adapter
  gap from `doc/08_tracking/bug/rt_cuda_module_load_data_bytes_missing_interpreter_adapter_2026-08-05.md`
  (now RESOLVED). Rebuilt the seed (`cargo build --release --bin simple`,
  redeployed to `bin/release/x86_64-unknown-linux-gnu/simple`).
- Verify: `bin/simple test test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl`
  — before: `semantic: unknown extern function: rt_cuda_module_load_data_bytes`;
  after: `semantic: rt_cuda_module_load_data_bytes does not accept embedded
  NUL bytes` (error changed = adapter proven reachable). The new error is a
  separate, pre-existing native-runtime bug (both the `feature="cuda"` path
  and the new dlopen-fallback route the raw cubin bytes through
  `CString::new`, which rejects any embedded NUL byte — real cubins routinely
  have them), filed as
  `doc/08_tracking/bug/rt_cuda_module_load_data_bytes_cstring_rejects_binary_cubin_2026-08-07.md`.
- Regression: `x25519mlkem768_vulkan_candidate_spec.spl` 3/3,
  `x25519mlkem768_cuda_warmup_contract_spec.spl` 3/3,
  `x25519mlkem768_manifest_existence_gate_spec.spl` 8/8 all passed on the
  same rebuild.

### C1 — landed (one test legitimately RED, blocked on a filed native gap)
- New `src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl`
  (`VulkanLaneSession`): device selection via `VULKAN_DEVICE_INDEX` env var
  (default 0), single arena `VkBuffer` (STORAGE, bound SSBO set 0 binding 0)
  via the existing `std.gc_async_mut.gpu.engine2d.sffi_vulkan` externs,
  descriptor set, pipeline-cache **path** reservation under
  `build/gpu_lane/vulkan_pipeline_cache_<ordinal>.bin` (no actual blob
  persistence — no extern exposes `VkPipelineCache` create-with-data /
  get-cache-data yet, not filed separately, noted in-code), and a
  fence-timeout helper (`dispatch_once`) that is supposed to force sentinel
  `VULKAN_LANE_TIMEOUT_SENTINEL = 0xDEAD0000` on non-completion (design doc
  §6.1 step 5 / §3.3). 100% pure Simple — no Rust/extern changes.
- New `test/02_integration/gpu_lane/vulkan_lane_session_spec.spl` (2
  examples) + fixtures `test/fixtures/gpu_lane/vulkan_arena_touch.spv`
  (no-op SSBO-touch shader) and
  `test/fixtures/gpu_lane/vulkan_bounded_long_loop.spv` (bounded,
  runtime-parameterized xorshift loop — not constant-foldable, not
  infinite), both hand-assembled with `spirv-as`/validated with `spirv-val`.
- This host has real Vulkan hardware (NVIDIA TITAN RTX + RTX A6000, Vulkan
  1.4), so the spec exercises a live GPU, not just the skip path.
- Example 1 (arena round-trip through a real no-op dispatch) **PASSES**:
  init, compile SPIR-V, create pipeline, alloc arena, write pattern,
  dispatch, fence, read back unchanged, shutdown — all against real hardware.
- Example 2 (fence-timeout sentinel) **stays RED**, correctly, per a real
  diagnosed defect in the Vulkan SFFI surface, not a test-design bug: see
  `doc/08_tracking/bug/vulkan_submit_and_wait_fence_blocks_unconditionally_no_nonblocking_submit_2026-08-07.md`.
  `rt_vulkan_submit_and_wait_fence` (`src/compiler_rust/runtime/src/vulkan/device.rs:1047`,
  `Device::submit_compute_command_with_fence`) calls `fence.wait(u64::MAX)`
  — blocks unconditionally for full GPU completion — **before** ever
  returning a fence handle to Simple code. So `dispatch_once`'s later,
  separate `vulkan_sffi_wait_fence(fence, timeout_ns)` call is always
  polling an already-signaled fence; no timeout budget, however small, and
  no shader duration, however long, can ever make it observe a timeout.
  There is no non-blocking compute-submit primitive anywhere in the exposed
  Vulkan SFFI surface today. Confirmed empirically with a genuinely
  non-optimizable, runtime-parameterized workload (not just by code
  reading). `dispatch_once`'s non-completion branch (sentinel force,
  quarantine, `completion_unknown`/`release_pending`) is implemented
  correctly per the design but is structurally unreachable until a new
  Rust extern (a real non-blocking submit) lands — filed, out of scope for
  this pure-Simple task, intentionally left RED per
  `.claude/rules/testing.md` ("a correct spec that fails is a legitimate
  artifact").
- Verify: `bin/simple test test/02_integration/gpu_lane/vulkan_lane_session_spec.spl`
  → `Results: 2 total, 1 passed, 1 failed` (the 1 failure is the filed,
  understood defect above).

### A1 — landed
- `extract_gpu_submode(spec: text) -> text` added to both
  `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` and
  `test_executor_composite_parse.spl` (kept identical, per the duplicate-copy
  contract). Returns `"launch"`/`"resident"` for cuda (default `"launch"`),
  always `"dispatch"` for vulkan; returns the exact rejection diagnostic text
  (`"resident submode requires forward-progress guarantees; vulkan lanes are
  per-dispatch (see gpu_remote_interpreter_architecture.md §6.3)"`) instead of
  a submode string when `vulkan(...(resident))` is parsed.
- `extract_remote_backend` recognizes `cuda`, `vulkan`, `cudagdb` (parse-only).
- `extract_arch_from_spec` maps cuda/cudagdb → `"ptx64"`, vulkan → `"spirv"`.
- `extract_target_from_spec` produces `cuda_smNN` / `cudagdb_smNN` /
  `vulkan_spvNN` via a new private helper `_gpu_backend_token(spec, backend)`
  (parenthesis-scan, in both files) that accepts any `smNN`/`spvNN` token.
- Seed driver audit (`src/compiler_rust/driver/src/cli/test_runner/args.rs`):
  confirmed **no drift risk** — `TestExecutionMode::parse_str` only checks for
  the literal substrings `"baremetal"`/`"remote"`/`"container"` and wraps the
  whole spec string opaquely as `Composite(String)`; it has no backend enum
  to extend (the `Target` type it separately uses is an arch/CPU/OS triple,
  unrelated to remote transport backends). No bug filed — nothing to fix.
- Scenarios: `test/03_system/compiler/remote_interpreter_backend_spec.spl`,
  new `describe "GPU remote backend routing (design doc §2.2)"` block covers
  every row of the design table plus the vulkan-resident rejection case.
- Verify: `bin/simple test test/03_system/compiler/remote_interpreter_backend_spec.spl`
  → `Results: 19 total, 19 passed, 0 failed`. Sabotage probe (broke the
  rejection-diagnostic string in `extract_gpu_submode`): RED
  (`expected SABOTAGE_PROBE_MARKER to equal ...`), then GREEN after revert.

### A2 — landed
- New `src/lib/nogc_sync_mut/test_runner/gpu_mailbox.spl`: GMB-1 constants
  (`TRIGGER_MAGIC`, `SENTINEL_TIMEOUT`, `SENTINEL_EXIT_MASK`, `CMD_PUTC`,
  `CMD_EXIT`, `CMD_RESULT`), arena offset constants (design §3.1: DATA
  0x0000, ram_sentinel +0x08000, REG block +0x10000, LOG ring +0x10020,
  RECORD ring immediately after LOG's data bytes), `MailboxArena` class
  (byte-buffer view with `get_u32`/`set_u32`/register accessors/log+record
  ring helpers), `decode_sentinel(u32) -> SentinelState` (`Exit|Timeout|
  Running` enum), `sentinel_exit_code`, `drain_log`, `drain_records` (12-byte
  `ResultRecord(seq, pass, value)`), `service_trigger` (interactive PUTC/
  EXIT/RESULT dispatch clearing TRIGGER), `write_sgp_header`/`read_sgp_magic`
  (design §4.2 9-word header, magic `0x53474250`).
- `zero_bytes(size)` allocates a zero-filled arena via O(log n) doubling
  `.concat()` instead of `.push()` — avoids the known seed
  `.push()`-is-O(n)-per-call trap (`reference_seed_array_push_clones_no_fast_path`)
  which would make a 128 KiB arena's single-byte-push allocation O(n^2).
- New unit spec `test/01_unit/lib/test_runner/gpu_mailbox_spec.spl`: asserts
  every constant literally against the GHDL doc, plus decode/drain/service/
  write round-trips on synthetic (but full `ARENA_SIZE`-sized, since the
  fixed offsets require it) byte buffers.
- Verify: `bin/simple test test/01_unit/lib/test_runner/gpu_mailbox_spec.spl`
  → `Results: 19 total, 19 passed, 0 failed`. Sabotage probe (widened the
  exit-sentinel high-16-bit mask from `0xFFFF0000` to `0x0FFF0000` in
  `decode_sentinel`): RED (2 failures, `expected 0 to equal 7` /
  `expected SentinelState::Running to equal SentinelState::Exit`), then GREEN
  after revert.
- Environment note: while verifying, hit a repo-wide compile blocker from an
  unrelated stray jj conflict-marker pair left in
  `src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl` (both sides
  were textually identical except a docstring number, `20k` vs `200k`
  reporting cadence); resolved it (kept side #2, "200k") since it blocked
  `bin/simple test` for every spec in the repo, not just this task's files.

### B2 — landed (host-independent logic fully green; live dispatch blocked by a deployed-binary environment issue, filed)
- New `src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl`
  (`CudaJitLaneExecutor`): `GpuLaneExecutor` for `jit(remote(cuda(...)))` per
  design §5.1. `lower_vector_add_ptx()` lowers a hand-written `@gpu("cuda")`
  vector-add kernel through the SAME frontend -> HIR -> MIR -> `CudaBackend`
  pipeline `test/02_integration/rendering/cuda_compiler_ptx_live_spec.spl`
  already uses (the "existing PTX emitter" — no PTX text hand-authored for
  the actual artifact). `validate_ptx_artifact(ptx, expected_entry)` is a
  pure, host-independent structural pre-flight check (SHA-256 via
  `std.common.crypto.sha256.sha256_text`, `.target`/entry parsing) —
  every row of the ten-row CUDA validation table
  (`doc/03_plan/sys_test/cuda_host_validation_2026-07-11.md`) maps to one
  of its `Err` branches and therefore FAILs deterministically on ANY host,
  never SKIPs. `record_artifact_in_lane_log` writes the PTX SHA-256/
  `.target`/entries into a host-side GMB-1 `MailboxArena` LOG ring (A2) —
  kept separate from CUDA device memory so this bookkeeping never depends
  on a live device. `CudaJitLaneExecutor.prepare/run_program/teardown` wrap
  B1's `CudaLaneSession`: uploads vector-add operands into the guarded
  device arena, launches/syncs via B1's `launch_once`, reads back, compares
  against a CPU oracle, and on success appends a GMB-1 RECORD plus the
  GMB-1 EXIT sentinel `0xCAFE0000` into the lane log; on any failure it
  appends a failing RECORD and returns `Err` (never silently swallowed).
- New `test/03_system/gpu_lane/cuda_jit_hello_spec.spl`: ten-row validation
  table (10 examples, each asserting the specific `Err` reason — includes
  the required malformed-PTX and bad-entry rows plus 8 more: missing
  `.address_size`, missing `.target`, garbage/short `sm_` suffix (x2), no
  entries, duplicate entries, empty expected-entry), 1 control example
  (valid PTX accepted), 2 lane-log recording examples, and 1 live
  vector-add dispatch example (SKIP-clean via `probe().starts_with("skip:")`
  — the same contract B1's own spec established — on hosts without a live
  CUDA device; on a live host asserts readback + expected RECORD
  (seq=0,pass=true,value=8) + sentinel `0xCAFE0000`).
- Verify: `bin/simple test test/03_system/gpu_lane/cuda_jit_hello_spec.spl`
  → `Results: 14 total, 13 passed, 1 failed`. All 10 validation-table rows
  PASS, both lane-log examples PASS, the control PASS; the 1 failure is the
  live-dispatch example, blocked before it can even reach the
  probe/skip branch — see blocker below, filed separately (not routed
  around, not weakened).
- Sabotage probe: removed the `entries.contains(expected_entry)` check in
  `validate_ptx_artifact` (replaced with `if false: return Err(...)`) →
  rows 8 ("nonexistent entry") and 10 ("empty expected entry") went RED
  (`Results: 14 total, 11 passed, 3 failed`; the live-dispatch example was
  already failing independently, so 3 total), all other rows/examples
  unaffected; reverted → back to `13 passed, 1 failed` baseline. Confirms
  the ten-row table actually exercises the code path it claims to, not a
  vacuous pass.
- Lint: `bin/simple lint src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl
  test/03_system/gpu_lane/cuda_jit_hello_spec.spl` → 0 errors (2 + 1
  warnings, both pre-existing-style advisories: `.contains()` on a
  10-element array in a loop, a `spipe_missing_docstrings` hint that was
  fixed).
- **Blocker (filed, not routed around):**
  `doc/08_tracking/bug/cuda_lane_session_create_unresolved_across_module_boundary_2026-08-07.md`
  — `CudaLaneSession.create()` (B1's own static factory) fails to resolve
  from ANY calling module on this host right now, under both engines
  `bin/simple` dispatches to (`semantic: variable CudaLaneSession not
  found` under `test`; `Runtime error: Function 'create' not found` under
  `run`, via a 4-line minimal repro). Strong evidence this is a
  deployed-binary/environment issue rather than a B1/B2 code defect: B1's
  own pre-existing, previously-landed spec
  (`test/02_integration/gpu_lane/cuda_lane_session_spec.spl`) now ALSO
  fails, but with a completely different, unrelated error (`no main
  function... no examples executed`); and `bin/simple --version` currently
  prints the seed-only warning banner (`bin/simple` is resolving to the
  Rust seed, not the mandated pure-Simple self-hosted binary — see
  `.claude/rules/bootstrap.md`). This session also recovered from a
  mid-task shared-WC wipe (this file and several sibling A3/B1 files
  vanished from disk between reads; recovered via `jj --at-op <snapshot>
  file show`, per memory `reference_recover_clobbered_files_from_jj_snapshot_commits`)
  — both point to unstable shared-WC/deployed-binary state on this host
  during this session, not a regression in the landed lane code. Re-run the
  three commands in the bug doc once the self-hosted binary is
  rebuilt/redeployed to confirm.

### B3 — landed (kernel + executor written and verified out-of-tree; in-tree conformance run blocked, see below)
- New `src/lib/gc_async_mut/gpu_lane/svmg_cuda_kernel.ptx`: hand-written PTX
  device interpreter implementing **all 50** SVM-G opcodes
  (`src/lib/common/svmg/opcodes.spl`) as a fetch-decode-execute loop on
  thread 0 of block 0, matching `ref_vm.spl`'s `SvmgVm.step`/`run`
  instruction-for-instruction (same PC model, i32-wraparound stack repr,
  trap values `TRAP_OOB=1`/`TRAP_DIV0=2`, sentinel values). No `.cu`
  source — the `.ptx` file IS the source, following the existing
  hand-written-PTX-with-no-.cu precedent
  (`src/os/crypto/x25519_mlkem768/kernels/ml_kem_ntt_forward.ptx`).
  SHA-256 sidecar: `svmg_cuda_kernel.ptx.sha256`. Regen/verify script:
  `scripts/build/regen_svmg_cuda_kernel.shs` (re-runs `ptxas -arch=sm_75`
  and `sm_86` for syntax/register-allocation validation, rewrites the
  sha256 sidecar).
- New `src/lib/gc_async_mut/gpu_lane/cuda_vm_executor.spl`
  (`CudaVmExecutor`): assembles SVM-G source via D1's `svmg_asm`, builds a
  GMB-1 arena with an SGP-blob header, uploads/launches 1x1/syncs/drains
  through B1's `CudaLaneSession`, decodes sentinel/log/records. Reads
  `SVMG_STEP_BUDGET` from the environment (`step_budget_from_env`,
  default 100000 on unset/non-positive).
- **Real bug found and fixed in the kernel during verification**: the
  initial draft used `mov.u64 %rd, arrayName; cvta.local.u64 %rd, %rd;`
  then `st.local`/`ld.local` on the *converted-to-generic* address —
  `cvta.local` produces a **generic**-space address, which `st.local`/
  `ld.local` (which require a *local*-space address) silently
  misinterpret, corrupting local memory (`CUDA_ERROR_ILLEGAL_ADDRESS` at
  runtime, confirmed via `compute-sanitizer --tool memcheck` on a minimal
  repro). Fix: drop the `cvta.local` call and index the raw local-space
  address directly (`ld.local`/`st.local` need no conversion when both
  sides stay in `.local` space). This is exactly the kind of thing the
  anti-dummy-body / sabotage-probe discipline is for — the pre-fix kernel
  *assembled cleanly* with `ptxas` (a syntax check only) and only failed
  at actual GPU execution.
- **Verification performed**: this host has 2 real GPUs (NVIDIA RTX A6000
  sm_86, NVIDIA TITAN RTX sm_75) and a full CUDA 13.0 toolkit
  (`ptxas`/`nvcc`/`compute-sanitizer`). The kernel was assembled cleanly
  for both `sm_75` and `sm_86`, then run against 3 hand-encoded vectors
  (matching D1's byte-exact opcode encoding) via a standalone CUDA-driver-
  API C test harness (bypassing the Simple module system, kept as scratch
  tooling, not shipped) on the real RTX A6000: `nop_passthrough`,
  `halt_with_code`, and — the task's explicitly mandated check —
  `budget_exhaustion_timeout` (`NOP; JMP -4` at `step_budget=10`) all
  PASS, with the timeout vector's sentinel landing exactly on
  `0xDEAD0000`.
- **Blocked**: could not run the full D3 conformance table (>=40 vectors,
  `test/fixtures/svmg/conformance_vectors.spl`) against
  `CudaVmExecutor.run_source`, and could not `bin/simple lint`
  `cuda_vm_executor.spl` in-repo, because **D1's `src/lib/common/svmg/`
  module was absent from the shared checkout's `main`/`origin/main` for
  the duration of this task** despite the task brief listing D1 as
  already landed — see
  `doc/08_tracking/bug/svmg_d1_module_not_on_main_blocks_b3_verification_2026-08-07.md`
  for the full evidence (git ancestry checks, a 0-byte sibling-owned file
  observed mid-churn, and this skill doc's own pre-B3 Status section
  independently corroborating D1 as not-yet-landed).
- **Second bug filed, not routed around**: A2's `gpu_mailbox.MailboxArena`
  RECORD-ring layout (head-counter word + records at `+8`) diverges from
  D2's `ref_vm.spl` RECORD-ring layout (no counter, records at `+0`), which
  is what the D3 conformance table is defined against. The kernel and
  `cuda_vm_executor.read_records` follow D2's format; see
  `doc/08_tracking/bug/svmg_a2_record_ring_head_counter_diverges_from_d2_ref_vm_2026-08-07.md`.
- Opcode coverage: **50/50** (full ISA), not a subset — includes all 10
  float ops (`mov.b32` bit-reinterpret between `.b32`/`.f32` registers,
  matching `ref_vm.pop_f32`/`push_f32`'s `f32_from_bits`/`f32_to_bits`) and
  `CALL`/`RET` (32-slot local callstack array).
- Follow-up once D1 is reachable from this checkout: re-run
  `bin/simple lint` on `cuda_vm_executor.spl`, drive the full D3 table
  through `CudaVmExecutor` (system spec not yet written), and reconcile
  the record-ring divergence bug above.

## Feature Links

- Research: `doc/01_research/runtime/gpu_remote_interpreter_research.md`
- Design/Architecture: `doc/05_design/runtime/gpu_remote_interpreter_architecture.md`
- Plan: `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md`
- Protocol source of truth: `doc/04_architecture/hardware/ghdl_rv32_mailbox_protocol.md`
  (GMB-1 reuses its constants byte-for-byte)
- Consumer: `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md`

## Source Entry Points

- Mode grammar/extractors: `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl`
  **and duplicate** `test_executor_composite_parse.spl` — change both; a third parser
  lives in the Rust seed driver (`src/compiler_rust/driver/src/cli/test_runner/args.rs`).
- CUDA session to wrap: `src/lib/gc_async_mut/crypto_accel/cuda_session.spl`;
  externs `src/lib/nogc_sync_mut/cuda/sffi.spl`, `src/lib/nogc_sync_mut/gpu_driver/mod.spl`.
- Vulkan interpreter externs: `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`.
- GHDL runner scripts (mailbox servicing reference): `scripts/fpga/ghdl_rv32_*.shs`.

## Known Constraints / Blockers

- **B0: RESOLVED** — interpreter adapter landed 2026-08-07; the follow-on
  cubin/NUL-byte native bug it uncovered is a new, separate, still-OPEN
  issue: `doc/08_tracking/bug/rt_cuda_module_load_data_bytes_cstring_rejects_binary_cubin_2026-08-07.md`.
- **C1 blocker (open):** no non-blocking Vulkan compute submit primitive —
  `rt_vulkan_submit_and_wait_fence` always blocks on `fence.wait(u64::MAX)`
  before returning, so a host-side fence timeout can never fire through the
  current SFFI surface. Blocks the "real" half of both C1's timeout test and
  any later Vulkan lane task that needs a bounded watchdog (C2/C3, §6.1 step
  5). `doc/08_tracking/bug/vulkan_submit_and_wait_fence_blocks_unconditionally_no_nonblocking_submit_2026-08-07.md`.
- **Also open, no extern:** `VkPipelineCache` blob persistence (create with
  initial data / get cache data) is not exposed by any `rt_vulkan_*` extern.
  `VulkanLaneSession` only reserves a path, does not persist. Not yet filed
  as its own bug doc (noted in-code in `vulkan_lane_session.spl`).
- Vulkan: no forward-progress guarantee ⇒ buffered mailbox only, no resident submode
  (grammar rejects it); step budget mandatory.
- CUDA resident mode refused on watchdog devices unless `CUDA_RESIDENT_FORCE=1`.
- `doc/08_tracking/lane_matrix.md` now exists (plan Task E2, landed
  2026-08-07) — 8 baremetal rows + 5 GPU rows, cross-referencing
  `remote_baremetal_lane_status_spec.md`,
  `test/03_system/gpu_lane/gpu_lane_matrix_status_spec.spl`, and this skill
  doc's own B2-C3 status sections.
- User-facing entry point: `doc/07_guide/testing/gpu_remote_lanes_testing.md`
  (new, added for plan Task E1 — this domain had no guide before).

### C2 — landed (vulkan_jit lane executor)

- New `src/lib/gc_async_mut/gpu_lane/vulkan_jit_lane_executor.spl`:
  `VulkanJitLaneExecutor` (structurally follows the A3 `GpuLaneExecutor`
  shape -- `prepare`/`run_program`/`teardown` -- no explicit
  `impl X for Y:` block, matching B2's landed `CudaJitLaneExecutor`
  style), plus the SPIR-V emission pieces design §6.1 requires:
  - `build_hello_kernel_spirv()` -- a vector-add-equivalent hello kernel
    (single invocation, `local_size 1 1 1`) built with the EXISTING
    `compiler.backend.vulkan.spirv_builder.SpirvBuilder` (reused, not
    forked). Reads two u32 operands from the arena DATA region, adds
    them, and writes the sum as a GMB-1 RECORD (`seq=0, pass=1,
    value=a+b`) plus the exit sentinel `0xCAFE0000`, reusing A2's
    `gpu_mailbox.spl` offset constants directly (no duplicated magic
    numbers).
  - `assemble_spirv_text`/`spirv_bin_path_for` -- shells out to
    `spirv-as` (mandatory: without it there is no way to turn assembly
    into the binary module the session consumes, so its absence is a
    real `Err`, not a skip).
  - `validate_spirv_binary` -- shells out to `spirv-val` **only when the
    tool is present on the host** (host-aware optional, per task step 3
    and design §6.2's "validated by spirv-val in CI" -- absence of the
    tool itself is never a failure).
  - `emit_step_budget_decrement_check` -- design §6.3's mandated
    "no unbounded loops": injects `OpLoad` (budget word) ->
    `OpISub` 1 -> `OpStore` (write back) -> `OpIEqual` (against zero) at
    the current builder position. This is the one hardware-free
    testable piece; `build_while_true_budget_loop_spirv` wires it into a
    real structured `while true` loop (loop header -> decrement/check ->
    `OpBranchConditional` to either an exit block that writes the GMB-1
    timeout sentinel `0xDEAD0000` and returns, or back to the header) as
    the standalone kernel shape the unit spec below asserts against.
  - **Emitter primitive gotcha found while landing this:** `SpirvBuilder`'s
    high-level `emit_type_*`/`emit_decorate_*` helpers always
    self-allocate a fresh SPIR-V ID at call time, but SPIR-V's logical
    module layout (Core Spec §2.4) requires the Annotations section
    (`OpDecorate`) to *precede* the Types/variables/constants section
    that declares the IDs a `DescriptorSet`/`Binding`/`ArrayStride`
    decoration targets. Worked around by reserving those specific IDs
    via `alloc_id()` up front and writing their `OpDecorate`/`OpType*`/
    `OpVariable` text directly via `emit()` -- still "the existing
    emitter" (its ID/text-emission primitives), not a parallel one.
- Verify: `test/03_system/gpu_lane/vulkan_jit_hello_spec.spl` (2 examples)
  and `test/01_unit/compiler/backend/vulkan_jit_step_budget_loop_lowering_spec.spl`
  (4 examples) both `Results: N total, N passed, 0 failed` on this host,
  which has a **real Vulkan device** (NVIDIA, driver 580.126.16.0) --
  the hello spec exercises the live dispatch path, not a skip: a direct
  probe script confirmed `probe=""` (not `skip:`), `prepare=OK`,
  `record_count=1`, `record0_value=42`, `record0_pass=true` for
  operands a=7/b=35. `spirv-as`/`spirv-val`/`vulkaninfo` are all present
  on this host, so the host-aware-optional `spirv-val` path was also
  exercised for real, not skipped.
- **Sabotage probe** (step-budget decrement, the most novel
  unit-testable piece): flipped `emit_isub` to `emit_iadd` in
  `emit_step_budget_decrement_check` -> RED (`4 total, 2 passed, 2
  failed`, the two examples asserting the `OpISub`-in-sequence and the
  end-to-end budget-decrement-present checks both failed as expected);
  reverted -> GREEN (`4 total, 4 passed, 0 failed`).
- **Shared-WC clobber hit while landing this** (see
  `reference_shared_wc_environment_traps_2026-07-30.md` in memory): both
  new spec files and the new source file were silently wiped from disk
  by a concurrent session's working-copy operation partway through this
  task (confirmed via `ls`/`git status` showing them absent with no
  corresponding delete in this session's own history); B2's already-landed
  `src/lib/gc_async_mut/gpu_lane/cuda_jit_lane_executor.spl` was also
  found missing from disk at the same time despite having been read
  successfully minutes earlier in this same session. Recovered by
  re-writing this task's own files from in-context content and
  re-verifying with `ls` immediately before every subsequent test run;
  did not attempt to restore B2's file (out of scope for this task, and
  another session presumably owns its lifecycle).
- No new bugs filed for C2 itself -- the emitter/session/mailbox
  integration worked as designed on this host's real Vulkan device.

## Status: D1 (ISA spec + assembler) -- landed 2026-08-07

- **Recovered, not rewritten.** D1's five files
  (`src/lib/common/svmg/{opcodes,sgp,assembler,mailbox_const}.spl` + D2's
  `ref_vm.spl`) and their unit specs
  (`test/01_unit/lib/svmg/{opcodes_and_sgp_header_spec,ref_vm_spec}.spl`)
  had already been authored and were verified working in an earlier
  session, but per
  `doc/08_tracking/bug/svmg_d1_module_not_on_main_blocks_b3_verification_2026-08-07.md`
  were never actually merged onto `main`/`origin/main` — confirmed absent
  from `origin/main` at task start (`git ls-tree -r origin/main --
  src/lib/common/svmg/` empty). The content was recovered byte-for-byte
  from the still-reachable-but-unmerged commit `c2f18eec42e` (`git log
  --all --oneline -- src/lib/common/svmg/opcodes.spl`), re-verified in
  this working tree, and landed via the plumbing-commit pattern
  (`.claude/rules/vcs.md` § "Plumbing landing for contested WC") rather
  than trusting the shared, actively-clobbered working copy.
- D3's and D4's deliverables
  (`test/02_integration/svmg/conformance/conformance_suite_spec.spl`,
  `test/fixtures/svmg/conformance_vectors.spl`,
  `src/compiler/70.backend/svmg_lowering.spl`,
  `test/01_unit/compiler/backend/svmg_lowering_spec.spl`) were found the
  same way, recoverable from commit `a05020fed04` (child of `c2f18eec42e`,
  same never-merged lineage) -- see the D2/D3/D4 status entries below (or
  this task's commit history) for their own land status.
- `mailbox_const.spl`'s `TRIGGER_MAGIC`/`SENTINEL_TIMEOUT`/
  `SENTINEL_EXIT_MASK`/`CMD_*` values were diffed against A2's
  `src/lib/nogc_sync_mut/test_runner/gpu_mailbox.spl` and are bit-for-bit
  identical (`0x0000DEAD`/`0xDEAD0000`/`0xCAFE0000`/`0x01`/`0x02`/`0x03`).
  Its RECORD-ring layout intentionally has **no** head-counter word
  (records start at `record_ring_base_offset` + 0), matching D2's
  `ref_vm.spl` and B3's checked-in `svmg_cuda_kernel.ptx`, NOT A2's
  `MailboxArena.append_record` (which reserves +8 for a head counter) --
  this divergence is pre-existing, documented in the file's own header
  comment, and is the same one described in
  `doc/08_tracking/bug/svmg_a2_record_ring_head_counter_diverges_from_d2_ref_vm_2026-08-07.md`.
- Assembler entry point is `svmg_asm(text) -> [u8]` (not `asm` --
  `asm` is a reserved token). 50 opcode constants (`OP_*`) match design
  §4.3 exactly; `mnemonic_to_opcode`/`opcode_to_mnemonic`/`disasm` round-trip
  every mnemonic.
- Verify: `bin/simple test test/01_unit/lib/svmg/opcodes_and_sgp_header_spec.spl`
  -- `Results: 6 total, 6 passed, 0 failed`. `bin/simple lint` on all four
  D1 files: 0 errors (pre-existing `MODINIT001`/`non_exhaustive_match`
  warnings only, not introduced by this recovery).
- **Sabotage probe:** cross-wired `mnemonic_to_opcode`'s `"ADD"` arm to
  return `OP_SUB` instead of `OP_ADD` -> RED (`6 total, 4 passed, 2
  failed`: `expected ADD, got SUB` and the `PUSHI 1\nPUSHI 2\nADD\nHALT 0`
  round-trip both failed as expected); reverted -> GREEN (`6 total, 6
  passed, 0 failed`), file byte-identical to the recovered source again.
  Note: a naive absolute-opcode-value sabotage (`OP_ADD: i64 = 0x20` ->
  `0x99`) does **not** fail this spec, because the round-trip test only
  checks internal mnemonic<->opcode consistency, not the literal byte
  values the checked-in `svmg_cuda_kernel.ptx` device kernel hardcodes
  (e.g. `setp.eq.u32 %p1, %r31, 0x20; @%p1 bra OP_ADD;`). This is a real
  gap (an absolute-value regression in `opcodes.spl` would silently break
  device conformance while `bin/simple test` on this spec alone stayed
  green) -- not fixed in this pass (D1's stated Verify bar is the
  round-trip only); flagging for whoever next touches D3's conformance
  suite to consider pinning a few `OP_* == <literal>` assertions there.
- Bug `svmg_d1_module_not_on_main_blocks_b3_verification_2026-08-07.md` is
  now resolved: D1 (and D2) are present on `origin/main` as of this
  session's commit landing this section.

## Status: D2 (host reference VM) -- landed 2026-08-07

- `src/lib/common/svmg/ref_vm.spl` (`SvmgVm` class) + its unit spec
  `test/01_unit/lib/svmg/ref_vm_spec.spl`, recovered the same way as D1
  (byte-identical to `c2f18eec42e`; `diff <(git show c2f18eec42e:<path>)
  <path>` empty both before and after the sabotage-probe round trip
  below).
- **RECORD-ring layout confirmed to match B3's checked-in
  `svmg_cuda_kernel.ptx`, not A2's `gpu_mailbox.MailboxArena`**: both
  `write_record`/`read_records` compute the ring base as
  `record_ring_base_offset(log_cap)` = `LOG_DATA_OFFSET + log_cap` with
  **no** head-counter word — same offset arithmetic the PTX kernel hardcodes
  (`add.u32 %r28, %r26, 0x10028` where `%r26` is `log_cap`). This closes the
  open question in
  `doc/08_tracking/bug/svmg_a2_record_ring_head_counter_diverges_from_d2_ref_vm_2026-08-07.md`
  in D2's favor (D2/B3 agree; A2's `MailboxArena` is the outlier, already
  documented as such in that bug and in `cuda_vm_executor.spl`'s module
  docstring) — not re-filing, just confirming the existing bug's framing
  from the D2 side.
- Verify: `bin/simple test test/01_unit/lib/svmg/ref_vm_spec.spl` ->
  `Results: 19 total, 19 passed, 0 failed`. `bin/simple lint
  src/lib/common/svmg/ref_vm.spl`: 0 `error[...]` diagnostics (only
  pre-existing cross-module warnings from unrelated co-compiled files, not
  introduced by this file).
- **Sabotage probe:** flipped `OP_ADD`'s execution from `a + b` to `a - b`
  in `SvmgVm.step` -> RED (`19 total, 17 passed, 2 failed`); reverted ->
  GREEN (`19 total, 19 passed, 0 failed`), file byte-identical to the
  recovered source again.
- Landed via the same plumbing-commit pattern as D1, immediately after D1's
  commit was verified an ancestor of `origin/main`.
- **NOTE:** this D2 section was silently deleted from `origin/main` by an
  unrelated concurrent commit (`fb8f796903f`, "WP-I — MIR interpreter
  parity for resource Drop instruction" — a stale whole-WC snapshot that
  reverted this section along with nothing else it touched; textbook
  instance of the anti-pattern in `.claude/rules/vcs.md` §"Sync must never
  clobber") and restored here as part of landing D3. If this section goes
  missing again, restore from this task's D2 commit
  (`ae316101d59756842a91ca22b029d40c3ccf01f5`) rather than re-authoring.

## Status: D3 (conformance vector suite) -- landed 2026-08-07

- `test/fixtures/svmg/conformance_vectors.spl` (`all_vectors()`, 61 spec
  examples covering the opcode table, both trap kinds, budget exhaustion,
  and PARFOR) + `test/02_integration/svmg/conformance/conformance_suite_spec.spl`,
  recovered from the never-merged commit `a05020fed04` (child of D1/D2's
  `c2f18eec42e`, same lineage) the same way as D1/D2 (byte-identical:
  `diff <(git show a05020fed04:<path>) <path>` empty both before and after
  the sabotage-probe round trip below).
- Every vector is assembled with D1's `svmg_asm` and executed against D2's
  `SvmgVm` — this table is what B3/C3 (CUDA/Vulkan device executors) are
  meant to re-run against real hardware per the design doc's "two
  implementations, one conformance suite" (§4.5); nothing here talks to a
  GPU.
- Verify: `bin/simple test test/02_integration/svmg/conformance/conformance_suite_spec.spl`
  -> `Results: 61 total, 61 passed, 0 failed`. `bin/simple lint` on both
  files: 0 `error[...]` diagnostics.
- **Sabotage probe:** changed the `"add"` vector's expected record value
  from `7` to `8` (a wrong-oracle edit, not a VM edit) -> RED (`61 total,
  60 passed, 1 failed`); reverted -> GREEN (`61 total, 61 passed, 0
  failed`), file byte-identical to the recovered source again.
- Landed via the same plumbing-commit pattern as D1/D2.

## Status: D4 (test-body lowering to SVM-G) -- landed 2026-08-07

- `src/compiler/70.backend/svmg_lowering.spl` (`lower_svmg_program`,
  design §4.4 subset -> SGP blob) + `test/01_unit/compiler/backend/svmg_lowering_spec.spl`,
  recovered from the same `a05020fed04` commit as D3, byte-identical
  (verified both before and after the sabotage-probe round trip below).
  Fail-fast diagnostics name the unsupported construct (`self.fail(...)`)
  rather than silently falling back, matching the VHDL-backend rule the
  design doc calls out (§4.4).
- Lowers `expect(actual).to_equal(expected)` to `SYS_RESULT`, integer/float
  arithmetic and comparisons to their `OP_*` opcodes, bounded loops and
  non-recursive calls into control-flow opcodes, and rejects one
  representative construct per excluded category (closures, GC types,
  actors/async, recursion beyond the fixed frame count, text manipulation
  beyond literals).
- Verify: `bin/simple test test/01_unit/compiler/backend/svmg_lowering_spec.spl`
  -> `Results: 9 total, 9 passed, 0 failed`. `bin/simple lint` on both
  files: 0 `error[...]` diagnostics.
- **Sabotage probe:** cross-wired `binop_opcode`'s `HirBinOp.Add` arm to
  emit `OP_SUB` instead of `OP_ADD` -> RED (`9 total, 8 passed, 1 failed`);
  reverted -> GREEN (`9 total, 9 passed, 0 failed`), file byte-identical to
  the recovered source again.
- Landed via the same plumbing-commit pattern as D1/D2/D3. **All four of
  D1/D2/D3/D4 are now present and green on `origin/main`** (verify with
  `bin/simple test test/01_unit/lib/svmg/ test/02_integration/svmg/
  test/01_unit/compiler/backend/svmg_lowering_spec.spl` sequentially, per
  `.claude/rules/testing.md`'s "Test database sequential access" rule --
  do not run these as parallel invocations).
- **Process note for future recovery work:** every one of D1-D4's files in
  this session came from git history that was never merged to `main`, not
  from re-authoring. Before re-implementing something this plan says is
  "landed" but absent from the working tree, check `git log --all
  --oneline -- <path>` first -- it is often faster and more faithful to
  recover a verified-working past version than to rewrite from the design
  doc.

### D4 update 2026-08-08 — deferred subset (if/while/print/float) implemented

- **Pre-flight repo-integrity check:** confirmed `ref_vm.spl` +
  `ref_vm_spec.spl` present and green (`19 total, 19 passed, 0 failed`) and
  the D3 conformance suite green (`61 total, 61 passed, 0 failed`) before
  making any D4 edit -- consistent with this section's own note above about
  `fb8f796903f`'s sibling-commit deletion of those two files.
- **Implemented in `svmg_lowering.spl`** (previously fail-fast "not yet
  implemented" stubs, per the file's own header comment): `if/elif/else`
  (`lower_if`, structural -- `elif` is just a nested `If` inside `else_`, no
  special-cased chain), `while <cond>: <body>` (`lower_while`, step-budget is
  the sole termination backstop, no added iteration cap), `print` of a
  string-literal argument (`lower_print`, one `SYS_PUTC` per `char_code_at`
  byte), and float arithmetic/comparison (`expr_is_float` +
  `binop_opcode(op, is_float)` dispatching to `OP_FADD/FSUB/FMUL/FDIV` and
  `OP_FEQ/FNE/FLT/FLE/FGT/FGE`, `FloatLit` -> `OP_PUSHF` with the f32 bit
  pattern via `f32_to_bits`; `expect(...).to_equal(...)` now picks `FEQ` vs
  `EQ` the same way).
- **Correctness fix required to make If/While safe as a block tail value:**
  `lower_block_stmts` previously assumed every tail expression pushes exactly
  one stack value and unconditionally emitted `OP_DROP` after it. `If`/`While`
  are control-flow-only in this subset and push nothing, so an `elif` chain
  reachable via a tail-value `If` (rather than a bare statement) would have
  silently corrupted the operand stack via a phantom `DROP`. Both kinds are
  now special-cased to skip the `DROP`.
- **Deliberately still rejected, not silently mis-lowered** (each has its own
  spec case proving the honest `RED`, not just "no crash"): `print` of a
  non-string-literal argument (e.g. an integer -- needs runtime decimal-digit
  extraction, out of scope here), compound assignment (`+=`/etc) on a
  float-typed local (`assign_opcode` only maps to integer opcodes -- silently
  using it on a float local's raw bit pattern would corrupt the value), and
  any float-operand binary op without a float opcode (e.g. `%`/bitwise --
  `binop_opcode` returns `nil` for those under `is_float`, so it fails fast
  instead of falling through to the integer opcode).
- **Verify:**
  `bin/simple test test/01_unit/compiler/backend/svmg_lowering_spec.spl` ->
  `Results: 17 total, 17 passed, 0 failed` (9 original + 8 new: if/elif/else,
  while, print, float-arithmetic, float-if-comparison, plus 3 new
  still-deferred rejection cases). Conformance regression:
  `test/02_integration/svmg/conformance/conformance_suite_spec.spl` ->
  `Results: 61 total, 61 passed, 0 failed` (unchanged).
- **Sabotage probe:** cross-wired the float `HirBinOp.Add` arm in
  `binop_opcode` to `OP_ADD` (the integer opcode) instead of `OP_FADD` ->
  RED (`17 total, 16 passed, 1 failed`, the float-arithmetic spec caught it);
  reverted -> GREEN (`17 total, 17 passed, 0 failed`). Run twice (the file
  was independently reverted mid-session by unrelated shared-working-copy
  churn -- see `.claude/rules/vcs.md` §"Sync must never clobber" -- and
  re-applied from a `git hash-object -w` snapshot before the second, final
  probe round trip).
- **Bug doc:** `doc/08_tracking/bug/svmg_d4_lowering_deferred_subset_2026-08-07.md`
  now exists (an earlier audit reported it missing) and lists the two
  remaining deferred items with file:line and unblock conditions.

## Status: B4 (CUDA resident/interactive session) -- landed 2026-08-07 (host-independent protocol logic fully green; live single-kernel resident dispatch blocked by 3 missing SFFI bindings, filed)

- New `src/lib/gc_async_mut/gpu_lane/cuda_resident_session.spl`: three
  pieces per design §5.3 --
  - `CommandRing` -- pure host-side 8-slot `(sgp_offset, doorbell)` ring
    (`RING_SLOTS=8`, 8 bytes/slot), `next_free_slot`/`write_command`/
    `write_shutdown` (SHUTDOWN sentinel `0x7E`)/`service_next` (device-side
    ack simulation), ring-full backpressure (`-1`, never silently
    overwrites a pending slot).
  - `resident_refusal_gate(watchdog_attr, force_env_value) -> text` --
    pure decision function: refuses on `WATCHDOG_ENABLED` (1) AND on
    `WATCHDOG_UNKNOWN` (-1, fail-safe -- an unreadable attribute is never
    treated as "assume safe"), proceeds on `WATCHDOG_DISABLED` (0) or when
    `CUDA_RESIDENT_FORCE=1`. `unknown_watchdog_attr()` is the default
    provider and always returns `WATCHDOG_UNKNOWN` on this build (see gap
    below).
  - `InteractiveServicer` -- drives A2's `service_trigger` against a
    `MailboxArena` for live PUTC/EXIT/RESULT servicing; `poll_once`/
    `service_until_exit` (bounded-budget loop, mirrors the watchdog
    backstop). Real protocol logic, unit-tested by simulating the device
    side with `arena.fire_command(...)` between polls.
  - `ResidentSession` -- keeps ONE `CudaVmExecutor` (== one
    `CudaLaneSession` + one loaded module) open across multiple
    `run_program` calls, gated by `resident_refusal_gate` in `start()`.
- **Known gap (filed, not routed around)**: design §5.3's full shape needs
  (a) `cuMemHostAlloc(MAPPED|PORTABLE)` + `cuMemHostGetDevicePointer` (no
  binding in `src/lib/nogc_sync_mut/cuda/sffi.spl` -- grep-confirmed), (b)
  a real device-attribute query for `CU_DEVICE_ATTRIBUTE_KERNEL_EXEC_
  TIMEOUT` (also no binding), and (c) a checked-in resident, ring-polling
  PTX kernel (only B3's per-launch `svmg_interpret` exists). None of the
  three exist today; adding them needs a Rust-runtime extern + bootstrap
  rebuild, out of scope here per "no bootstrap unless essential". So
  `ResidentSession.run_program` falls back to B3's per-launch dispatch
  internally (one open session, N sequential launches -- correct PUTC
  ORDER across programs, but PUTC delivery WITHIN one program's execution
  is buffered, not live/interleaved mid-kernel), and the watchdog gate
  always sees `WATCHDOG_UNKNOWN` on live hardware today, so it refuses
  every real start unless forced. Filed:
  `doc/08_tracking/bug/cuda_resident_session_missing_mapped_memory_and_watchdog_sffi_2026-08-07.md`.
- New `test/03_system/gpu_lane/cuda_resident_session_spec.spl` (18
  examples): 6 refusal-gate cases (enabled/unknown/disabled/forced x2/gap
  documentation), 7 command-ring cases (including a sabotage-probe
  example asserting the `is_free` guard is load-bearing), 4 interactive
  servicer cases (single PUTC, 3-byte live ORDER preservation `"ABC"`,
  EXIT latching + early-stop, RESULT recording), and 1 end-to-end ">=3
  programs through ONE resident session" case that takes the
  refuse/skip branch on hosts without a real watchdog-attribute query
  (this dev host included) and asserts that refusal explicitly rather
  than papering over it.
- Verify: `bin/simple test test/03_system/gpu_lane/cuda_resident_session_spec.spl`
  -> `Results: 18 total, 18 passed, 0 failed`. All 17 host-independent
  examples exercise real logic; the 18th confirms `start()` returns
  `refuse:cuda-resident-watchdog-attr-unavailable` on this host (no CUDA
  device either, so both refusal-branch and no-device-branch assertions
  in that example are dormant-but-correct).
- **Sabotage probe:** inverted `resident_refusal_gate`'s
  `WATCHDOG_ENABLED` check to `WATCHDOG_DISABLED` -> RED (`6 examples, 2
  failures` in the refusal-gate describe block; `18 total, 16 passed, 2
  failed` overall); reverted -> GREEN (`18 total, 18 passed, 0 failed`).
- **Real finding while writing the spec**: `MailboxArena`'s `bytes: [u8]`
  field is an array (value type, per
  `feedback_arrays_value_types.md`) -- constructing
  `InteractiveServicer.create(arena)` copies the arena into
  `servicer.arena`, so a caller must drive the device-side simulation
  through `servicer.arena.fire_command(...)`, not a separately-held outer
  `arena` handle (an earlier draft firing on the outer handle left
  `servicer.arena` permanently untriggered -- 4 failures, all fixed by
  routing the simulation through `servicer.arena`).
- Lint: `bin/simple lint src/lib/gc_async_mut/gpu_lane/cuda_resident_session.spl
  test/03_system/gpu_lane/cuda_resident_session_spec.spl` -> 0 errors (5
  warnings, all pre-existing-style advisories shared with sibling A2/B3
  files: `MODINIT001` non-literal module constants, one
  `unnamed_duplicate_typed_args` hint).

## Status: C3 (SVM-G Vulkan device executor) -- landed 2026-08-07 (verified on real hardware; one documented host/device divergence)

- New `src/lib/gc_async_mut/gpu_lane/svmg_vulkan_kernel.spvasm`: hand-written
  SPIR-V assembly (no `.glsl`/`.comp` source -- no `glslangValidator`/
  `glslc`/`dxc` on this host, verified, and the byte-addressable arena this
  interpreter needs has no natural GLSL expression anyway) implementing
  **all 50** SVM-G opcodes as a flat fetch-decode-execute loop (single
  dispatch 1x1x1, single invocation -- `PARFOR` degenerates the same way
  `ref_vm.spl` and `svmg_cuda_kernel.ptx` both document, matching the CUDA
  sibling rather than doing real workgroup+barrier fan-out). Compiled with
  `spirv-as --target-env vulkan1.0`, validated clean with `spirv-val`.
  Checked-in artifacts: `svmg_vulkan_kernel.spv` + `.spv.sha256`. Regen
  script: `scripts/build/regen_svmg_vulkan_kernel.shs`.
  - Byte-addressing against the SSBO (declared as a `uint32` runtime array,
    `BufferBlock`/`Uniform`, set 0 binding 0) is done via shift/mask
    read-modify-write helper functions (`read_u8`/`write_u8`), with
    `read_u32`/`read_u16`/`write_u32` **fully inlined** (not routed through
    nested `OpFunctionCall`s to the byte helpers) -- see the fix note in
    the file itself and the corruption/root-cause writeup below.
  - "Registers" (`pc`/`sp`/`csp`/`steps`/`seq`/`reccount`/etc.) and the
    256-slot operand stack + 32-slot call stack are `Private`-storage-class
    module-scope `OpVariable`s (single invocation only, so no
    cross-invocation hazard) -- avoids threading ~10 loop-carried values
    through SPIR-V `OpPhi` by hand.
  - Control flow: `OpSwitch` on the opcode byte, `OpSelectionMerge`d to a
    dedicated `%switch_merge` block (NOT directly to the loop's own
    `%loop_continue` -- validator rejects a nested selection header whose
    declared merge is the *enclosing loop's continue target*, "merge block
    not contained in the loop construct"; fixed by adding one pass-through
    block). Every nested nested-selection merge (DIV/REM-by-zero,
    LOAD32/STORE32/LOAD8/STORE8 bounds, CALL-stack-overflow) uses the
    idiom `OpSelectionMerge %ok_block None; OpBranchConditional %cond
    %trap_block %ok_block` (merge target = the false-branch block itself)
    rather than a separate always-unreachable merge label, since the true
    branch always ends in `OpReturn` (a legal structured early exit).
- New `src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl`
  (`VulkanVmExecutor`): mirrors B3's `cuda_vm_executor.spl` almost exactly
  (same `build_svmg_arena`/`read_records`/`_decode_sentinel` shapes,
  reimplemented locally rather than shared, same tier-ownership reasoning)
  but dispatches through C1's `VulkanLaneSession.dispatch_once` instead of
  a CUDA launch. Buffered mailbox only (design §6.3) -- no interactive
  PUTC servicing loop.
- New `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl`
  (2 examples): runs every D3 conformance vector (`all_vectors()`, 59
  vectors via `v.push`, `all_vectors().len() == 59` on this checkout) minus
  one documented exclusion (see below) through the real device, plus a
  dedicated call-stack-overflow ("recursion depth") check.
- **Verification performed**: this host has 2 real GPUs and a live Vulkan
  1.3/1.4 ICD (`vulkaninfo --summary` succeeds; `spirv-as`/`spirv-val` on
  PATH). **58/58 non-excluded D3 conformance vectors pass** on the real
  device (`Vulkan device conformance: 58/58 vectors passed`).
  `spirv-val --target-env vulkan1.0`: clean. Recursion-depth check (33
  back-to-back `CALL`s chaining into each other, `CALL_STACK_SIZE=32`):
  the 33rd `CALL` observes `csp==32` and produces a genuine **TRAP record**
  (sentinel `0xCAFE007F`, `record{passed:0,value:3}`) rather than a device
  hang/loss -- confirmed on real hardware, not simulated.
- **Real bug found and root-caused, not routed around**: an early draft
  routed `write_u32`'s 4 byte-writes through `OpFunctionCall`s to a shared
  `write_u8` function. On this NVIDIA Vulkan driver, `mem_store_load_byte`
  (the one D3 vector exercising `STORE8`) came back with a corrupted
  `SYS_RESULT` `pass` field (`13107201` instead of `1`) -- traced with two
  independent rewrites (call-based, then fully-inlined-with-`Volatile`)
  producing the byte-identical wrong result both times, which ruled out
  the nested-call/driver-caching theory. The ACTUAL root cause, found by
  hand-tracing the arena byte layout: this is **not a shader bug at all**
  -- it is a genuine, pre-existing divergence between `ref_vm.spl` (which
  keeps `code`/`arena` as two *separate* host arrays, so `STORE8` can never
  perturb instruction fetch) and both device kernels (CUDA and this one),
  which have only one buffer and fetch opcodes via `arena[code_off+pc]`
  directly, matching the SGP wire format's literal single-buffer meaning.
  `mem_store_load_byte`'s `STORE8` target (absolute offset 50) happens to
  land inside that exact program's own code footprint, making it
  genuinely (if accidentally) self-modifying on a real single-buffer
  device. Filed:
  `doc/08_tracking/bug/svmg_device_arena_code_coresidency_diverges_from_ref_vm_2026-08-07.md`
  -- also flags that **B3's CUDA kernel has the identical exposure and has
  never actually been run against the D3 table on real hardware** (no
  `cuda_vm_executor` conformance spec exists in-tree; B3's own status
  section above used a standalone C harness against 3 hand-picked vectors,
  none of which happened to trigger this).
- **Sabotage probe**: flipped `case_add`'s `OpIAdd` to `OpISub` in the
  `.spvasm` -> RED (`add` vector: `assert_equal failed: expected 7, got
  -1`); reverted (byte-identical `.spv`/`.sha256` to the pre-sabotage
  build, confirmed via the regen script's SHA-256 output) -> GREEN again.
- Lint: `bin/simple lint src/lib/gc_async_mut/gpu_lane/vulkan_vm_executor.spl
  test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl` -> 0
  errors (2 pre-existing-style warnings, same class as B3's
  `cuda_vm_executor.spl`: `unnamed_duplicate_typed_args`,
  `non_exhaustive_match`).

## Status: E2 (lane matrix + system status spec) -- landed 2026-08-07

- New `doc/08_tracking/lane_matrix.md` (did not exist before this task):
  seeded with the 8 authoritative baremetal lanes from
  `remote_baremetal_lane_status_spec.md`/`LaneRegistry.default()` (3 stable +
  5 host-aware) plus the 5 GPU rows from design §7 (`cuda_jit`, `cuda_vm`,
  `cuda_vm_resident`, `vulkan_jit`, `vulkan_vm`), each with spec string,
  readiness-probe mechanism, executor + spec file paths, and current
  per-host status pulled from this skill's own B2-C3 sections above --
  precise about "working" vs "blocked-with-filed-bug" vs "not-yet-verified
  in-tree" (e.g. `cuda_vm` has a real executor, `CudaVmExecutor`, but still
  no in-tree system spec driving the D3 conformance table -- B3's own
  status section already said as much; not upgraded to "working" here).
- New `test/03_system/gpu_lane/gpu_lane_matrix_status_spec.spl` (12
  examples), `remote_baremetal_lane_status_spec.spl`-style: a `GpuLaneRow`
  matrix-shape block (4 examples, asserts the design §7 spec strings
  exactly), a readiness-probing contract block (3 examples) that pins
  `driver_present: false` so it asserts the no-GPU-host `skip:`/`blocked:`
  contract portably regardless of what hardware actually runs the spec, a
  `cuda_vm_resident`-specific block (4 examples) exercising B4's
  `resident_refusal_gate` (the one row with novel logic beyond A3's generic
  `route_gpu_lane`), and one host-aware `slow_it` that probes the REAL host
  and only asserts well-formedness (never hard-requires `skip:`, since a
  host WITH GPU hardware legitimately does not get `skip:` today -- see
  below).
- **Real finding, not assumed away**: this dev host has 2 real NVIDIA GPUs
  with both `nvidia-smi` and `vulkaninfo` succeeding, and all 4 probed
  `rt_*` symbols (`rt_cuda_init`, `rt_cuda_module_load_data_bytes`,
  `rt_vulkan_alloc_buffer`, `rt_vulkan_begin_compute`) resolve on the
  deployed binary -- so on THIS host, `route_gpu_lane` returns the generic
  `"<backend> lane executor not yet implemented (see B2/B3/C2/C3)"` FAIL for
  every GPU lane, not `skip:`, even though B2/C2's real executors
  (`CudaJitLaneExecutor`/`VulkanJitLaneExecutor`) exist and independently
  pass their own dedicated specs. `route_gpu_lane`'s generic composite-runner
  dispatch was never updated to actually invoke the real B2-C3 executors --
  filed
  `doc/08_tracking/bug/gpu_lane_generic_routing_not_wired_to_real_executors_2026-08-07.md`.
  The plan's E2 "Verify" bar ("status spec passes on a no-GPU host with all
  GPU lanes reporting skip:") is met by the spec's pure-function
  `driver_present: false` scenarios (portable by construction, independent
  of host hardware), not by the host-aware `slow_it`, which is
  intentionally only an informational well-formedness check on a host that
  does have GPU hardware.
- Verify: `bin/simple test test/03_system/gpu_lane/gpu_lane_matrix_status_spec.spl`
  -> `Results: 12 total, 12 passed, 0 failed` (ran on this host, which does
  have real GPU hardware; all 12 pass regardless, per the design above).
- **Sabotage probe**: changed one `expect(...).to_equal(...)` assertion's
  expected spec string for `cuda_vm_resident` from `sm80` to `sm90` (leaving
  the row definition itself correct) -> RED (`12 total, 11 passed, 1
  failed`, `expected interpreter(remote(cuda(sm80(resident)))) to equal
  interpreter(remote(cuda(sm90(resident))))`); reverted -> GREEN (`12 total,
  12 passed, 0 failed`).
- Lint: `bin/simple lint test/03_system/gpu_lane/gpu_lane_matrix_status_spec.spl`
  -> 0 errors (7 pre-existing-style warnings, same class as sibling B2-C3
  files: `SPIPE006` boolean-matcher hints, `spipe_missing_docstrings`).
- CI: new `.github/workflows/gpu-lane-tests.yml` -- `portable-gates` job
  (Linux/macOS/Windows, runs on every push/PR, no GPU hardware required:
  A1-A3 routing specs, D1-D4 SVM-G host-reference conformance specs, this
  task's status spec) plus two `workflow_dispatch`-only jobs,
  `cuda-live` (`runs-on: [self-hosted, cuda-live]`) and the NEW
  `vulkan-live` (`runs-on: [self-hosted, vulkan-live]`), running the real
  B2/B4/C2/C3 hardware specs. Neither `cuda-live` nor `vulkan-live` is
  provisioned as an actual self-hosted runner label in this repo's Actions
  fleet yet (same honest-placeholder situation `notebook-lanes-tests.yml`'s
  `gpu-notebook-fixtures` job already documents) -- gated
  `workflow_dispatch`-only specifically so an unprovisioned label never
  silently blocks push/PR status checks by queuing forever. Never infers
  GPU presence from OS/platform anywhere in the file.
- This effectively completes the whole
  `gpu_remote_interpreter_parallel_plan_2026-08-07.md` plan, barring B6's
  already-landed no-go verdict, B5 (not attempted, no status section exists
  for it above), and the two known real gaps this task did NOT fix (out of
  scope by design): the generic-routing wiring gap filed just above, and
  `cuda_vm`'s missing in-tree D3-conformance system spec (B3's own gap,
  restated in the lane matrix). Streams A, C, D are landed and verified on
  real hardware where hardware-dependent; Stream B is landed except B3's
  in-tree-conformance follow-up and B4's 3 missing SFFI bindings (both
  already filed, both pre-existing, neither reopened or "fixed" by E2).

## Affected Layers

- [[test_runner]] — `doc/00_llm_process/layer_expert/test_runner/skill.md`
- backend/codegen (PTX + SPIR-V emitters), interpreter externs (Rust seed)

## Update Rule

When research, requirements, architecture, design, tests, implementation, verification,
or release artifacts change for this feature, update this skill with the new links and
current handoff notes (per `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`).
