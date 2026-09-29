# Staged plan: give native-build step 5 real parallelism

**Date:** 2026-09-04
**Status:** PLAN. Nothing in P0-P3 below is implemented.
**Bug:** `doc/08_tracking/bug/native_build_step5_serial_threads_ignored_2026-09-04.md`
**Related:** `doc/03_plan/infra/unstable_mode_build_side.md`

This plan exists because the fix could not be landed safely in one change. Each
stage below names exact files and what it unblocks. The only thing landed with
this plan is the honesty line described under "Landed now".

---

## 1. What `compile_fn` actually captures — the crux

`ParallelBuilder.build(compile_fn)` is handed a partial application built at
`src/compiler/80.driver/driver_aot_native_output.spl:1259-1262` (was `:1233-1236`
before this session's +26-line honesty insert):

```
builder.build(_compile_frozen_module_capsule(
    capsules, effective_backend, native_target, is_release,
    driver_opt_level, provider_receipt_hash, backend_session, _1))
```

Two of those captures cannot cross a process boundary:

| capture | type | defined at | why it cannot cross |
|---|---|---|---|
| `capsules` | `FrozenNativeModuleCapsuleBatchV1` | `src/compiler/80.driver/driver_types.spl:115-118` | Its `capsules[i].mir_module: MirModule` (`driver_types.spl:80`) and `storage_snapshot: FrozenStorageModuleSnapshotV1` (`:81`) are live interpreter heap objects with **no wire format**. |
| `backend_session` | `BackendSession?` | consumed at `driver_aot_native_output.spl:1211-1214` | A stateful adapter with no reentrancy capability; threads are already forced to `1` when one is admitted. |

**There is no MIR decoder anywhere in the tree.** `src/compiler/50.mir/mir_json.spl`
(687 lines) and `src/compiler/50.mir/mir_serialization.spl` (35 lines) are
**encode-only** — every function in both is `serialize_*`, and
`src/compiler/70.backend/backend_plugin/transport.spl:145` uses
`serialize_mir_module` one-way onto a wire it never reads back. Round-tripping
`MirModule` + `storage_snapshot.sites`/`.evidence` is a new subsystem, not a
change.

The capsule is built by `CompileContext.freeze_native_module_capsules_v1`
(`driver_types.spl:1010`), which reads `self.mir_modules[...]` directly. So the
capture is the parent's whole in-memory MIR set, by reference.

---

## 2. Why each alternative loses

### (a) In-process THREADS — dead, for two independent reasons

1. **The interpreter runs "threads" synchronously.** Both native-build
   processes on this host run `src/app/cli/native_build_worker.spl` (verified
   2026-09-04 by `pgrep -a -x simple`), i.e. the interpreted worker path.
   In that interpreter, `spl_thread_create` is dispatched to
   `rt_thread_spawn_isolated_with_context`
   (`src/compiler_rust/compiler/src/interpreter_extern/mod.rs:2926-2930`), whose
   body at `src/compiler_rust/compiler/src/interpreter_extern/concurrency.rs:349-404`
   evaluates the closure **inline on the calling thread** and stores the result
   before returning a handle. `spl_thread_pool_spawn_worker` returns `0`
   unconditionally (`concurrency.rs:310-312`). Wiring `std.thread_pool` here
   would report N workers and deliver one core — the exact dishonesty this bug
   was filed about.
2. **The LLVM temp paths are process-wide, not per-module.**
   `llvm_debug_artifact_paths()`
   (`src/compiler/70.backend/backend/llvm_backend_tools.spl:26-29`) returns
   `{tmp}/simple_llvm_{getpid()}.{ll,bc,o}`, and `llvm_backend.spl:293-294`
   uses `{tmp}/simple_opt_{pid}.ll`. Two modules compiling concurrently in one
   process overwrite each other's IR. Confirmed on disk: `/tmp/simple_llvm_*.ll`
   is one file per pid, never per module.

### (b) Serialise the MIR capsule so `build_parallel()` becomes usable — out of bounds and largest

Needs a `MirModule` decoder plus decoders for `FrozenStorageModuleSnapshotV1`'s
`sites` and `evidence`, all of which live under `src/compiler/50.mir/**`. That
directory is out of scope for this work, and the encoders alone are 722 lines —
the decoder is a comparable subsystem with its own identity/round-trip gate.

### (c)/(d) Re-derivation shards (the parse/HIR model applied to codegen) — viable, but expensive and blocked on P0

The repo already ships this shape twice: `run_parse_shards` / `run_hir_shards`
(`src/app/cli/native_build_main.spl:452-518`, `:555+`). Each shard child re-runs
the pipeline, does work only for its own slice, publishes to an on-disk cache,
and is **non-fatal** — a dead shard just means a cache miss. That property is
what makes it safe.

It does not transplant cleanly onto step 5:

- **Publication races.** `build_cache_persist`
  (`src/compiler/80.driver/driver_build/incremental.spl:1050-1071`) is a
  **whole-file rewrite with no temp+rename** — `incremental_file_write_text`
  straight onto `cache.cache_path`. `driver_native_collect_capsule_result_v1`
  (`driver_aot_native_output.spl:395-400`) calls `update_entry` + `save()` per
  module. K children publishing concurrently is last-writer-wins plus torn
  reads.
- **Hits are manifest-driven, not receipt-driven.** Phase 1
  (`driver_aot_native_output.spl:1058-1077`) admits a cached object only via
  `build_cache.get_cached_outputs(cache_source)` **and**
  `build_cache_module_witness(build_cache, cache_source)`. A child that writes
  an object and a `.capsule-receipt` but no manifest entry produces **zero**
  parent hits. So shards need per-shard manifest fragments plus a parent merge.
- **K× front-end.** MIR lowering is not cached to disk, and the loop at
  `driver_pipeline_lowering.spl:262-311` runs a cross-module
  `prescan_module_struct_names` prepass, so each child must redo steps 1-4
  (~27 min and a large interpreter heap on the observed 102-unit build) to reach
  its slice. That multiplies CPU by K and heap by K for a step-5-only win.

Correctness is *not* the problem — `capsule.identity_valid()`
(`driver_types.spl:104-108`) makes a mismatched child fail closed to a parent
recompile, never to a wrong object. Cost and the P0 race are.

### (e) IR-split — the smallest real win, and the recommendation

`LlvmBackend.compile_module` (`src/compiler/70.backend/backend/llvm_backend.spl:256-320`)
already ends at a **process boundary of its own**:

1. MIR opt + `MirToLlvm.translate_module` -> LLVM IR **text**, in-process (`:268-286`).
2. `opt` on a `.ll` file — **subprocess** (`:289-302`).
3. `compile_ir_to_object(llvm_ir, ...)`
   (`src/compiler/70.backend/backend/llvm_backend_tools.spl:110-113`) — "Writes
   IR to a temp file, invokes llc, reads back the object bytes" — **subprocess**.

So for the built-in `llvm` lane the expensive tail already takes a *file* as its
input. Splitting `compile_module` into `emit_ir(module) -> text` and
`ir_to_object(ir_path) -> obj` lets the driver emit every module's `.ll`
serially (unchanged, deterministic) and then drive K concurrent `opt`/`llc`
children through the **existing, already-written** `build_parallel(spawn_fn,
collect_fn)` (`parallel.spl:567`). No MIR crosses a boundary; the IR file is the
wire format and it already exists. No front-end duplication, no heap
multiplication.

**Scope note:** the split itself edits `src/compiler/70.backend/**`, which was
outside this session's assigned file set. It is named here as the primary
recommendation rather than reached into silently.

---

## 3. Staged implementation

### P0 — atomic manifest publication *(prerequisite for every later stage)*
`src/compiler/80.driver/driver_build/incremental.spl:1071`. Replace the direct
`incremental_file_write_text(cache.cache_path, ...)` with write-to-temp +
rename. Unblocks: any concurrent writer of `build_cache.sdn`; also removes a
latent torn-manifest-on-crash bug that exists today with zero concurrency.
Gate: a check that a manifest is never observed partially written.

### P1 — per-module LLVM temp paths *(prerequisite for P2)*
`src/compiler/70.backend/backend/llvm_backend_tools.spl:26-29` and
`llvm_backend.spl:293-294`. Key the `.ll`/`.bc`/`.o` temp paths on
`{pid}_{module_name}` instead of `{pid}`. Unblocks: more than one codegen in
flight at a time, by any mechanism. Standalone correctness value: two
concurrently-running `simple` processes that share a pid namespace slot cannot
collide.

### P2 — IR-split + wire `build_parallel()` *(the actual fix)*
1. `70.backend`: split `LlvmBackend.compile_module` into `emit_ir` and
   `ir_to_object`; keep `compile_module` as the composition so every existing
   caller is untouched.
2. `driver_aot_native_output.spl` phase 2 (`:1160-1250`): for the built-in
   `llvm` lane only, emit all uncached modules' `.ll` in the current serial
   loop, then call `builder.build_parallel(spawn_fn, collect_fn)` where
   `spawn_fn(name)` launches `llc` on that module's `.ll` via
   `rt_process_spawn_async` and `collect_fn(code, name)` runs the existing
   receipt/identity/cache logic on the produced object.
3. **Scope the lane explicitly.** An admitted `BackendSession` owns codegen and
   must stay serial — keep the existing `provider_threads = 1` clamp at
   `:1211-1214`. `llvm-lib` drives the LLVM C API in-process via DynLib
   (`llvm_lib_backend.spl:1-9`) and is **not** covered by this stage.
4. Raise the `effective_threads()` auto-detect cap of 8 (`parallel.spl:137`)
   only after this lands, guided by `shard_mem_clamp` as the parse/HIR shards
   already are.

### P3 — codegen shards *(only if P2's win proves small)*
Mirror `run_parse_shards` in `src/app/cli/native_build_main.spl`: a
`--native-shard=i/N` flag with the same recursion guard, `shard_threads_mem_cap`
budget, non-fatal reclaim, and per-shard manifest fragments merged by the parent
before phase 1. Depends on P0. Take this only if measurement shows interpreted
`MirToLlvm.translate_module` — not `llc` — dominates step 5, because it is the
only option that parallelises translation, at K× CPU and K× heap.

### Filed separately — step 4/6 (MIR lowering) stays serial
`driver_pipeline_lowering.spl:262-311` shares one mutable `MirLowering` whose
`.symbols` is reassigned per module after a cross-module prepass. Parallelising
it needs `src/compiler/50.mir/**` changes and MIR serialisation. Out of scope
for all of the above; tracked in the bug record.

---

## 4. Landed now: honest concurrency reporting only

`driver_aot_native_output.spl:1218-1243`, at phase-2 entry, prints one
unconditional line: the uncached-module count, `concurrency=1`, and the
RESOLVED thread value together with the invariant that no value above 1 takes
effect. It does not change `log_build_progress`'s format and does not claim
parallelism.

Every clause is unconditionally true, which is why it does NOT say "requested
threads=N is not honoured": `provider_threads` is the resolved value, not the
user's `--threads` — `driver_native_build_threads()` returns 0 when
`SIMPLE_NATIVE_BUILD_THREADS` is unset (`:248-255`) and an admitted
`BackendSession` clamps it to 1, so that phrasing would be false at 1 and
meaningless at 0.

This preserves the correction already made at `parallel.spl:480-497` (the
`[PARALLEL]` print no longer asserts concurrency) and extends it to the default,
non-`--verbose` path — which is where the >1h33m silent phase was observed.

---
## 5. Unproven — do not cite these as measured

- **The llc-vs-translate split within step 5.** A 6-sample × 25 s probe on
  2026-09-04 saw **zero** live `llc`/`opt` children, but both running builds
  were in the front-end at the time (`phase2:surface:file:*` and
  `[bootstrap-error-count] source_idx=2` in their logs), so the probe observed
  the wrong window and settles nothing. P2's payoff is proportional to the
  `opt`+`llc` share of step 5 and that share is **unmeasured**. Measure it
  before committing to P2 over P3: sample for live `llc` children during a real
  step-5 window.
- **Whether the originally observed >1h33m stall was step 4 or step 5.** The bug
  record hedges this and no log was retained. P2 addresses step 5 only.
- **The interpreter heap multiplier** behind the K× memory objection to P3 —
  the bug record marks it code-reading inference, unmeasured.
- Nothing in P0-P3 has been run. No bootstrap or native-build was executed for
  this plan (two long builds owned the machine).
