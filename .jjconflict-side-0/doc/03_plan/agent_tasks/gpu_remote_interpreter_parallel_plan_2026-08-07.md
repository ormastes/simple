# GPU Remote Interpreter Lanes — Parallel Implementation Plan

**Date:** 2026-08-07
**Status:** Ready (research + design landed; paths verified 2026-08-07)
**Research:** `doc/01_research/runtime/gpu_remote_interpreter_research.md`
**Design:** `doc/05_design/runtime/gpu_remote_interpreter_architecture.md` (§ numbers below refer to it)
**Linked plan:** `doc/03_plan/agent_tasks/notebook_lanes_parallel_plan_2026-08-07.md` consumes A1/A3, B2–B4, C2–C3, SVM-G, GMB-1.
**Audience:** Written so Sonnet- or Haiku-class agents can execute each task independently.

## 0. How to read this plan

- **Streams A–E** are independent workspaces; tasks inside a stream are ordered, tasks
  across streams only depend on what `deps:` names. Anything with no unmet deps can start
  immediately, in parallel.
- Every task states: files touched, exact steps, and a **verify** command that must pass
  before the task is done. Agents must run the verify command and paste its output into the
  task report (session report under `doc/09_report/`).
- **Model routing:** `[haiku-ok]` = mechanical/spec-following, small blast radius.
  `[sonnet]` = requires design judgment or multi-file reasoning. When unsure, escalate.
- Repo rules that always apply: no placeholder/stub bodies (anti-dummy gate), file bugs in
  `doc/08_tracking/bug/` instead of silently working around, specs are executable SSpec
  under `test/…` with generated manuals under `doc/06_spec/…`.
- Path note: paths below were verified 2026-08-07. If a path drifts, locate the real one by
  grepping for the named symbol first and record the correction in the task report — do
  not create a parallel copy.

## 1. Dependency graph

```
A1 (grammar) ──┬─► A3 (runner routing) ──► B2/B3/C2/C3 (lane executors)
A2 (GMB-1 lib) ┤
D1 (SVM-G ISA + assembler) ──► D2 (host ref VM) ──► D3 (conformance vectors)
D1 ──► B3 (CUDA VM kernel)      D1 ──► C3 (Vulkan VM shader)
B0 (interp adapter bugfix) ──► B1 (CUDA session reuse) ──► B2, B3 ──► B4 (resident)
C1 (Vulkan session) ──► C2, C3
B2,B3,C2,C3,D3 ──► E2 (lane matrix + system specs)   E1 (docs) has no deps
B6 (cuda-gdb spike) independent, P3
```

## 2. Stream A — Grammar + shared protocol (unblocks everything)

**A1. Extend composite mode grammar with `cuda`/`vulkan` backends** `[sonnet]` `deps: none`
- Files: `src/lib/nogc_sync_mut/test_runner/test_executor_composite.spl` (extractors at
  L58–L104) **and** its duplicate `test_executor_composite_parse.spl` (L6–L48) — change
  BOTH; plus the unit spec. Also check the Rust seed driver's mode parser
  (`src/compiler_rust/driver/src/cli/test_runner/args.rs`) — if it enumerates backends,
  extend it too or file a bug (three-implementations trap; see memory
  `reference_three_implementations_not_two_seed_pure_simple_and_runtime_c`).
- Steps: add `cuda`, `vulkan` (and `cudagdb` token, parse-only) to the backend set; add
  `extract_gpu_submode(spec: text) -> text` returning `launch|resident|dispatch` per
  design §2.2; map arch tokens `smNN→ptx64`, `spvNN→spirv`; reject `resident` under
  `vulkan` with the exact diagnostic text `resident submode requires forward-progress
  guarantees; vulkan lanes are per-dispatch (see
  gpu_remote_interpreter_architecture.md §6.3)`.
- Add scenarios mirroring `remote_interpreter_backend_spec` for every row of the design
  §2.2 table, including the rejection case.
- Verify: `bin/simple test test/03_system/compiler/remote_interpreter_backend_spec.spl`
  (extended file) — all scenarios pass.

**A2. GMB-1 mailbox library (host side)** `[sonnet]` `deps: none`
- Files: new `src/lib/nogc_sync_mut/test_runner/gpu_mailbox.spl` + unit spec
  `test/01_unit/lib/test_runner/gpu_mailbox_spec.spl`.
- Steps: implement design §3.1 layout as constants + a `MailboxArena` view over a byte
  buffer: `decode_sentinel(u32) -> Exit|Timeout|Running`, `drain_log(...) -> text`,
  `drain_records(...) -> [ResultRecord]`, `service_trigger(...)` (interactive dispatch of
  PUTC/EXIT/RESULT, clearing TRIGGER), `write_sgp_header(...)`. Pure byte-buffer logic —
  **no GPU calls** — so it is fully unit-testable on any host.
- Constants must equal the GHDL doc values (assert `TRIGGER_MAGIC == 0x0000DEAD`,
  `SENTINEL_TIMEOUT == 0xDEAD0000`, exit mask `0xCAFE0000` in the spec).
- Verify: `bin/simple test test/01_unit/lib/test_runner/gpu_mailbox_spec.spl`.

**A3. Runner routing for GPU backends** `[sonnet]` `deps: A1, A2`
- Files: composite remote runner dispatch in `src/lib/nogc_sync_mut/test_runner/`
  (start from `test_executor_composite.spl`; locate the ghdl/t32 routing by
  `grep -rn "ghdl" src/lib/nogc_sync_mut/test_runner/`), new `gpu_lane_common.spl`.
- Steps: route `remote_backend in {cuda, vulkan}` to a `GpuLaneExecutor` trait
  (`prepare(session) / run_program(blob) -> ArenaSnapshot / teardown`), with host-aware
  probing: missing driver/ICD ⇒ `skip:` line format identical to existing lanes; honor
  `*_LIVE_REQUIRED` per design §7. Wire `GPU_LANE_TIMEOUT_MS` watchdog here (one place).
  Probing calls every required `rt_*` symbol once at session start and reports `unknown
  extern` as `blocked:` with the symbol name (prevents silent B0-style gaps).
- Verify: `bin/simple test <new routing unit spec>` plus a dry-run
  `bin/simple test test/03_system/... '--mode=interpreter(remote(cuda(sm80)))'` on a
  no-GPU host printing a well-formed `skip:` (capture output in report).

## 3. Stream B — CUDA

**B0. Fix `rt_cuda_module_load_data_bytes` interpreter adapter** `[haiku-ok]` `deps: none`
- Files: Rust seed `src/compiler_rust/compiler/src/interpreter_extern/mod.rs` (the
  registry currently registers only `rt_cuda_module_load_data` at mod.rs:932 →
  gpu.rs:1479; the `_bytes` variant is declared at `src/lib/nogc_sync_mut/cuda/sffi.spl:59`
  and `src/lib/nogc_sync_mut/gpu_driver/mod.spl:28`, codegen-registered at
  `src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:1729`). Bug doc:
  `doc/08_tracking/bug/rt_cuda_module_load_data_bytes_missing_interpreter_adapter_2026-08-05.md`.
- Steps: add the adapter following the exact pattern of the landed `rt_array_data_ptr_u8`
  fix referenced in the bug; update the bug doc to RESOLVED with evidence.
- Verify: `bin/simple test test/02_integration/os/crypto/x25519mlkem768_cuda_binary_execution_spec.spl`
  progresses past `unknown extern function` (PASS on CUDA hosts, contract-conformant
  SKIP/next-error elsewhere — paste both the before/after error lines).

**B1. CUDA lane session (reuse `cuda_session.spl`)** `[sonnet]` `deps: B0`
- Files: new `src/lib/gc_async_mut/gpu_lane/cuda_lane_session.spl` wrapping the existing
  `src/lib/gc_async_mut/crypto_accel/cuda_session.spl` init/JIT/alloc/launch/cleanup with
  the arena: device alloc + guard regions, HtoD/DtoH of the 128 KiB arena, entry
  resolution, first-error retention per `cuda_host_validation_2026-07-11.md`.
- Verify: new integration spec `test/02_integration/gpu_lane/cuda_lane_session_spec.spl`
  — on CUDA host: allocates arena, round-trips a pattern, guard regions intact; else SKIP.

**B2. `cuda_jit` lane executor** `[sonnet]` `deps: A3, B1`
- Steps: implement `GpuLaneExecutor` for `jit(remote(cuda(...)))` per design §5.1 — lower
  test kernel via existing PTX emitter, record PTX SHA-256/.target/entries in the lane
  log, launch, sync, drain via A2.
- Verify: system spec `test/03_system/gpu_lane/cuda_jit_hello_spec.spl` (vector-add +
  expected RECORD + sentinel 0xCAFE0000) passes on CUDA host; SKIP-clean elsewhere; all
  ten negative rows of the CUDA validation table produce FAIL not SKIP (add at least
  malformed-PTX and bad-entry cases).

**B3. `cuda_vm` per-launch executor (SVM-G on CUDA)** `[sonnet]` `deps: A3, B1, D1`
- Steps: build/emit the SVM-G interpreter module (PTX artifact checked in with SHA-256,
  regeneration script under `scripts/`); executor writes SGP blob (via A2 helpers),
  launches 1×1, syncs, drains. Step budget from `SVMG_STEP_BUDGET`.
- Verify: run the D3 conformance vectors through this executor on a CUDA host: all pass;
  budget-exhaustion vector yields sentinel `0xDEAD0000`.

**B4. Resident submode** `[sonnet]` `deps: B3`
- Steps: design §5.3 — mapped arena, 8-slot command ring, doorbell protocol, interactive
  servicer thread using A2's `service_trigger`, watchdog-device refusal gate.
- Verify: system spec runs ≥3 programs through one resident session with live PUTC order
  preserved; refusal path unit-tested by faking the device attribute.

**B6. cuda-gdb MI spike (P3, timeboxed)** `[sonnet]` `deps: none`
- Deliverable: `doc/01_research/runtime/cudagdb_semihost_lane_spike.md` with a go/no-go,
  MI transcript evidence, and — if go — a task list. No production code.

## 4. Stream C — Vulkan

**C1. Vulkan lane session** `[sonnet]` `deps: none`
- Files: new `src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl` reusing the existing
  Vulkan externs (interpreter adapters in
  `src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`, vendored `ash` bindings):
  instance/device/compute-queue selection, arena buffer (HOST_VISIBLE|HOST_COHERENT with
  staging fallback), descriptor set, pipeline cache file, fence-with-timeout helper
  mapping `VK_ERROR_DEVICE_LOST`/timeout ⇒ forced `0xDEAD0000`.
- Verify: `test/02_integration/gpu_lane/vulkan_lane_session_spec.spl` — arena round-trip +
  fence timeout path (tiny infinite-loop shader with 1 s timeout) on Vulkan host; SKIP
  elsewhere. Record deviceName/driverVersion in output.

**C2. `vulkan_jit` lane executor** `[sonnet]` `deps: A3, C1`
- Steps: design §6.1 — lower test kernel to SPIR-V via the existing emitter; run
  `spirv-val` on the emitted module when the tool is present (host-aware optional);
  dispatch, fence, drain. Loop lowering must thread the step budget (design §6.3) — add an
  emitter unit spec asserting the budget decrement exists in generated SPIR-V for a
  `while true` body.
- Verify: `test/03_system/gpu_lane/vulkan_jit_hello_spec.spl` mirrors B2's hello spec.

**C3. `vulkan_vm` executor (SVM-G shader)** `[sonnet]` `deps: A3, C1, D1`
- Steps: SVM-G as compute shader source + checked-in SPIR-V with SHA-256 + regeneration
  script; flat dispatch loop, arrays for stacks (design §4.1), buffered mailbox only;
  `PARFOR` via workgroup + barrier.
- Verify: D3 conformance vectors all pass on a Vulkan host; `spirv-val` clean; the
  recursion-depth vector traps with `TRAP` record rather than device loss.

## 5. Stream D — SVM-G core (pure host work, GPU-free, ideal early parallel work)

**D1. ISA spec + assembler** `[sonnet]` `deps: none`
- Files: SSpec source under `test/` (generated manual lands under `doc/06_spec/…`) +
  `src/lib/common/svmg/` (opcode constants, SGP header encode/decode, a tiny assembler
  `asm(text) -> [u8]` for tests).
- Steps: encode design §4.2–§4.3 exactly; assembler rejects unknown mnemonics fail-fast.
- Verify: unit spec round-trips every opcode and the SGP header.

**D2. Host reference VM** `[sonnet]` `deps: D1`
- Files: `src/lib/common/svmg/ref_vm.spl` — executes SGP blobs against an in-memory arena
  using A2's layout constants; deterministic; step budget honored.
- Verify: unit spec: arithmetic, control flow, bounds trap, budget timeout, PUTC/RESULT/
  EXIT land in the right arena offsets.

**D3. Conformance vector suite** `[haiku-ok]` `deps: D2`
- Files: `test/02_integration/svmg/conformance/` — ≥40 vectors as `(asm source, expected
  log text, expected records, expected sentinel)` covering every opcode, both trap kinds,
  budget exhaustion, PARFOR, and the design §4.4 lowered-subset patterns.
- Steps: generate blobs with D1's assembler; assert against D2. The same table is exported
  as data so B3/C3 re-run it on device.
- Verify: `bin/simple test test/02_integration/svmg/conformance/` — all pass on any host.

**D4. Test-body lowering to SVM-G** `[sonnet]` `deps: D1, D2`
- Files: lowering pass from the interpreter's checked AST for the design §4.4 subset →
  SGP blob; fail-fast diagnostics naming unsupported constructs.
- Verify: unit spec lowers representative SSpec bodies (`expect(add(1,2)).to_equal(3)`,
  bounded loop, array sum) and executes them on D2 with expected records; plus one
  rejection case per excluded construct.

## 6. Stream E — Docs, lane matrix, CI

**E1. Docs — landed with this plan** `[haiku-ok]` `deps: none`
- The research/design/plan split is DONE (this document set). Remaining: link the design
  from `doc/06_spec/03_system/hardware/remote_baremetal_lane_status_spec.md` notes and the
  GPU guide; refresh the llm wiki
  (`doc/00_llm_process/feature_expert/gpu_remote_lanes/skill.md`) as tasks land.
- Verify: doc link check passes.

**E2. Lane matrix + system status spec** `[sonnet]` `deps: B2, B3, C2, C3, D3`
- **Create** `doc/08_tracking/lane_matrix.md` (it does not exist yet) seeded with the
  authoritative baremetal lanes from `remote_baremetal_lane_status_spec.md` plus the five
  GPU rows from design §7; extend a `remote_baremetal_lane_status_spec`-style status spec
  with GPU lanes (readiness probing, `skip:`/`blocked:` semantics); add CI jobs: portable
  gates on all runners; live lanes on labeled runners (`cuda-live`, new `vulkan-live`)
  with explicit GPU capability requests — never infer GPU presence from the OS.
- Verify: status spec passes on a no-GPU host with all GPU lanes reporting `skip:`.

## 7. Suggested schedule (3 agents)

| Slot | Agent 1 | Agent 2 | Agent 3 |
|---|---|---|---|
| 1 | A1 → A2 | D1 → D2 | B0 → C1 |
| 2 | A3 | D3 → D4 | B1 |
| 3 | C2 | B3 | B2 |
| 4 | C3 | B4 | E2 (+E1 anytime) |

Critical path: A1→A3→{B2,C2} and D1→{B3,C3}. B6 is fill-in work.

## 8. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Desktop watchdog kills long dispatches/kernels | Device step budget is mandatory (design §3.3); resident mode gated on watchdog attribute; fence/`DEVICE_LOST` mapped to the existing timeout sentinel |
| Vulkan host polling of in-flight device writes is non-portable | Buffered mailbox is the only Vulkan mode; interactive servicing is CUDA-only |
| SPIR-V emitter gaps surface mid-stream | C2 depends only on the *existing* emitter path; gaps are filed as bugs (pattern already established) and the VM lane (C3) is unaffected since its shader is prebuilt |
| Divergent VM behavior between CUDA and Vulkan | Single conformance table (D3) executed on host-ref, CUDA, and Vulkan; any divergence is a FAIL with the vector id |
| Interpreter-extern gaps like the B0 bug recur for Vulkan symbols | A3's probing calls every required `rt_*` symbol once at session start and reports `unknown extern` as `blocked:` with the symbol name |
| Grammar drift between the two `.spl` extractor copies and the Rust seed parser | A1 explicitly touches both `.spl` files and audits the seed driver; the extended spec exercises every row so a missed copy fails the suite |
| No-GPU CI gives false confidence | Portable gates (D3 on host-ref, PTX/SPIR-V static validation, grammar/routing specs) are mandatory on all runners; live lanes on labeled runners only |
