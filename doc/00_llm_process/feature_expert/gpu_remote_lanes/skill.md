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
