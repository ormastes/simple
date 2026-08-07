# Feature Expert: GPU Remote Interpreter Test Lanes

## Role

Own feature-specific process knowledge for the `cuda`/`vulkan` remote test lanes
(`interpreter(remote(cuda(sm80)))` family): current docs, source entry points, known
constraints, and the pipeline artifacts to update as work progresses.

## Status (2026-08-07)

Tasks A1 (grammar), A2 (GMB-1 mailbox library), B0 (CUDA interpreter adapter),
and C1 (Vulkan lane session shell) landed. Remaining lane code (A3 routing,
B1-B6 CUDA, C2-C3 Vulkan, D1-D4 SVM-G, E1-E2 docs/CI) not started.

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
- `doc/08_tracking/lane_matrix.md` does not exist yet — plan Task E2 creates it;
  authoritative lane status today is
  `doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md`.

## Affected Layers

- [[test_runner]] — `doc/00_llm_process/layer_expert/test_runner/skill.md`
- backend/codegen (PTX + SPIR-V emitters), interpreter externs (Rust seed)

## Update Rule

When research, requirements, architecture, design, tests, implementation, verification,
or release artifacts change for this feature, update this skill with the new links and
current handoff notes (per `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`).
