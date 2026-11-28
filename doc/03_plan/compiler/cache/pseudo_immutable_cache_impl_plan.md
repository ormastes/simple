# Pseudo-immutable cache — implementation plan

**Design:** `doc/05_design/compiler/cache/pseudo_immutable_cache_async_build_design.md` (baseline 2026-10-26; sections 1-23 pending from author — re-map this plan when they arrive).
**Base:** `origin/release/1.0.0` @ 9c97b3cdcea (paths and lines observed there; the `release_phase3` working tree differs). **Tracker:** cache-build-tracker items 1-34.
**Rule:** correctness first, then no-change speed, then structure. Each PR: red→green spec, time + peak RSS before/after, workarounds tagged, Fable review, landed alone.

## 1. Decision → code map

| # | Design decision | Existing code (release/1.0.0) | Status |
|---|---|---|---|
| D1 | One engine, one cache protocol, one scheduling core; embedded compiler without BuildRunner | `src/app/build/scheduler/{broker,coordinator,planner,worker_request}.spl`, `src/app/build/providers/build_job_admission.spl`; per-file packages P-A..P-H (#4557-#4696, flag `SIMPLE_FILE_WORKERS`, default 0) | PARTIAL |
| D2 | TestRunner submits through the same scheduler, no compiler coupling | `src/app/test_runner_new` own governor (`governor_create/can_spawn`), `process_tracker.spl` spawns directly | GAP |
| D3 | Default op source→OBJ, fused, no forced intermediate save/reload; MIR persistence optional | `80.driver/cache/native_prelower_object_key.spl`; MIR merge `driver_build/incremental.spl:~1520`; legacy `.build/mir_cache` | PARTIAL |
| D4 | TLDR AST/HIR/MIR + optional OBJ independently reusable | packed AST #4391/#4397/#4436/#4445; generic TLDR view `00.common/cache_contract/generic_tldr_view_v1.spl`; whole-pipeline TLDR reuse absent | PARTIAL |
| D5 | Pseudo-immutable payload + write-once scalar / dense-array / sparse-hash slots; missing = data state | set-once TLDR table #4386 (item 6, ~30%); no dense/sparse slot type | GAP |
| D6 | Async only for real producers/waits/IO/processes/large CPU; fiber + process invokers share one interface | async reads #4417, IOCP #4430 (`src/runtime/platform/async_driver.c`) — not used by driver; test runner uses processes directly | PARTIAL |
| D7 | XXH3-128 trusted lookup only; cryptographic digest for persistent cache + untrusted imports; algorithm-tagged; no truncated-hash identity | registry `00.common/cache_contract/hash_algorithm_registry_v1.spl` (xxh3 marked `collision_resistant: false`); HIR key/TLDR/broker use sha256; `10.frontend/frontend.spl:228` xxh3-128 private parse key (P1 from Fable #4402: unverified xxh3 parse-key hit); import integrity `materialize_optional_sha512_integrity_receipt_v1` — call sites unconfirmed | PARTIAL |
| D8 | Collision-safe local 16/32-bit IDs | none found | GAP |
| D9 | Final-artifact-first: valid OBJ/BIN/LIB/SMF ⇒ no compile/link; missing dest ⇒ materialize from cache | object scope key `incremental.spl:634,663`; link receipts `70.backend/linker/link_engine_external.spl:281,318` (#4356); no pre-check, no materialize step | GAP |
| D10 | HIR target-neutral, optional OS/CPU with explicit compatibility; MIR selects target | `50.mir/mir_cfg_select.spl` (#4905, slice 1, uncalled); plan `doc/03_plan/compiler/hir_target_neutral_mir_target_plan.md` | PARTIAL |
| D11 | Cross-target HIR cache hazard | `80.driver/driver_hir_cache.spl:157-174` key has no target; `hir_cache_dir` (:125) partitions only by lane; parser strips arms `10.frontend/core/parser_preprocessor.spl:83-262` using `cfg_platform.spl:126-185` | **BUG** |
| D12 | Single-flight, cache limits | `cache_single_flight_v1.spl` (#4372), `cache/metadata/cache_limits.spl`, `cache/gc/admission.spl` (#4506) | REUSE |

## 2. PR order

### Wave A — correctness (land first)
- **C1 HIR key target fold.** Fold every preprocessor cfg input (os, arch, cpu, active feature set, the `cfg_env` OS/ARCH/CPU knobs; `cfg_eval_key_value` handles `cpu` and `feature`) into `hir_cache_key` and `_hir_cache_env_switches`. Red spec: same source with a `@when(os == ...)` arm, two targets, assert distinct keys. Interim fix; tagged `WA(hir-target-neutral)` until C5 makes HIR neutral, then the fold becomes the declared OS/CPU compatibility field.
- **C2 Untrusted-input digest gate.** Every persistent-cache read and import that crosses the trust boundary verifies an admitted cryptographic digest (registry `collision_resistant: true`); an xxh3 hit is a lookup hint, confirmed by exact bytes or crypto digest. Covers Fable #4402 P1 (unverified xxh3 parse-key hit). Red spec: forged xxh3-colliding entry ⇒ miss.
- **C3 Truncated-hash audit.** Static check that no cache identity compares a truncated digest; fail-closed script under `scripts/check/` plus a `config/check/must_check_gates.sdn` row and an exact dispatch case (a script alone enforces nothing).

### Wave B — no-change build (N3 first: N1 cannot pass for SMF/LIB without their receipts)
- **N3 Receipt for SMF/LIB** where missing.
- **N1 Final-artifact precheck.** Before compile/link: if destination OBJ/BIN/LIB/SMF exists and its receipt (LinkReceiptV1 / object scope key) matches current inputs ⇒ skip. Red spec: second identical build performs 0 compiles, 0 links.
- **N2 Materialize from cache.** Destination missing, cache entry valid ⇒ copy (temp+rename) from cache, no compile.

### Wave C — structure
- **C4 Pseudo-immutable slot type** (scalar / dense-array / sparse-hash write-once; absent is a state), extends #4386.
- **C5 Target-neutral HIR** — wire `mir_cfg_select` per the hir_target plan; HIR keeps all arms; drop C1's WA.
- **S1 Shared invoker interface** (fiber + process) and TestRunner submission through the scheduler core.
- **S2 Compact local IDs** with collision check on intern.
- **S3 Fused source→OBJ default** with optional persisted MIR; flip after per-file stage3 proof.

## 3. Open questions
- Author's sections 1-23 may re-scope R03+; re-map when merged.
- Resolved: cpu and feature are arm selectors, so C1 folds both.

## 4. Mandated refactor order (coordinator, 2026-10-26; design §19 being completed by Fable)
Wave C is executed in this order, small PRs each. Wave A/B correctness fixes may land standalone.
1. **Step 1 — async compile nodes:** parse/HIR/MIR/objgen nodes return futures (fiber-based); file IO returns async. Builds on #4417/#4430 and the FileFiber state machines.
2. **Step 2 — interfaces:** internal compiler interface + BuildRunner wrapper (same API embedded or managed); fiber/process invokers behind ONE interface — reuse the one-process-per-file lane's worker/invoker trait, do not add a parallel one. TestRunner submits through it (was S1).
   - **Alongside step 2 — multi-algorithm hash IDs** (after step 1): one record with ≥3 algorithm-tagged digests side by side, O(1) lookup by any admitted algorithm, unknown algorithm = miss; extends the #4421 registry/DigestV1. Full hashes shrink to compact 16/32-bit reference IDs guarded by a bloom filter (collision ⇒ full-digest fallback or a new ID; never an identity proof), scoped global / per-file / local, grouped by base file (was S2).
3. **Step 3 — pseudo-immutable storage:** empty fields, dense arrays, sparse-hash attribute slots (was C4).
C5 (target-neutral HIR) and S3 (fused source→OBJ default) follow step 3.

## 5. Generic instances on this engine (added 2026-11-28)

Design addendum: `doc/05_design/compiler/cache/generic_instance_tldr_trace.md`.
Stage rows and acceptance: `doc/03_plan/language/type_system/no_any_inference_plan.md`
S3-F1..F10 (S3-D is reframed there as a specialization query, not a pass).
Owner direction: generic specialization is an async task in this engine; it
adds no scheduler, cache protocol or registry (R01). Guide = Fable, Impl = lower
model unless marked.

| Generic stage | Wave slot here | Depends on (this plan) | Why |
|---|---|---|---|
| S3-F1 template `open_needs` | alongside step 3 | S3-1 write-once slot (may precede it by writing at publication) | the field is absent after parse and set once by typed HIR |
| S3-F2 `needed-instance\|` section | alongside step 3 | S3-1; A-2 digest gate | a second set-once slot on the module TLDR record; the section crosses the trust boundary |
| S3-F3 demand closure | end of step 1 | S1-3 `read_tldr_async`, S1-5 wake-on-publish | requests are lazy `(module_id, decl_id)` pointer fills; waiters must be woken on terminal failure |
| S3-F4 specialization task (Impl = Fable) | step 2 | S1-1, S1-2 async stage nodes; S2-1 `CompileInvoker` | the task is `compile(task)` for a different task kind, written once |
| S3-F5 keys and artifacts | alongside step 2, then step 3 | S2-6 key record; S3-4 `.sphb`, S3-5 ledger, S3-6 mmap writer; A-1 then P-1 | per-instance key record; packed blobs; target stays out of view and HIR keys |
| S3-F6 reverse-reference rows | after S3-F3 | none | producer for an existing family |
| S3-F7 invalidation | after Wave B and S3-F5 | B-1..B-3 no-change build; S3-7 invalidation inputs | zero instance tasks on an identical build |
| S3-F8 trace queries | after S3-F6 | none here | projection owned by the extreme-typing lane |
| S3-F9 remote action | after step 2 | S2-2 `ProcessInvoker`, S2-4 | same action key locally and remotely |
| S3-F10 coverage gate | from the start | A-3 pattern (script + manifest row + dispatch case) | a script alone enforces nothing |

Status check against `src` at `6b0b52f6f43` (`git grep`, not document status):
`parse_async`, `lower_hir_async`, `lower_mir_async`, `emit_object_async`,
`read_tldr_async`, `trait CompileInvoker`, `FiberInvoker`, `KeyRecordV2`,
`.sphb`, `.spmb` and a usage ledger are **absent**. Present:
`SourceReader.read_src_async`, `TldrTableV1.request_async`,
`tldr_table_fill_async_v1`, `CacheSingleFlightV1` (daemon and AOP match cache
only), `mir_cfg_select_arm`, `hir_variant_object_key_v1`, `.spab`. So S1-1,
S1-2, S1-3 (TLDR half), S2-1, S2-6, S3-1..S3-6 are not landed, and S3-F3 onward
cannot start before them. The target-neutral flag in code is
`SIMPLE_HIR_CFG_SELECT`, not `SIMPLE_HIR_TARGET_NEUTRAL` as the design says.
`tldr_async_owner_integration_2026-10-30.md` excludes mono semantics from its
slice and `tldr_caller_async_prerequisites_2026-10-30.md` lists five blocking
prerequisites for a real async caller; S3-F3 is such a caller.
