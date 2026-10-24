# Per-module stream-to-object for the Phase 3 / Phase 4 bootstrap builds (v1)

Request (2026-10-24): "build src to obj in phase3. not hir, mir, obj. fix
default phase3 and 4 build setting." Plus: the default must USE THE CACHE and
GO TO END (every producible object, every failure named, no fake success).

Phase 3 = `native-build --entry-closure --entry src/app/cli/bootstrap_main.spl`
(1471 modules); Phase 4 = the same for `src/app/cli/main.spl`
(`SIMPLE_BOOTSTRAP_STAGE4=1`). Both are whole-program, phase by phase today:
parse all, HIR all, mono, MIR all, borrow all, codegen all. The native runtime
has no collector, so every phase's output stays resident until exit.

## 1. Which phases can stream per module today

| Phase | Per module today? | Why / what blocks |
|---|---|---|
| parse, HIR, type-check | Per module, cached (`SIMPLE_FRONTEND_CACHE`, `SIMPLE_HIR_CACHE`), and shardable into warmer processes (`SIMPLE_PARSE_SHARDING`, `SIMPLE_HIR_SHARDING`). The resident HIR set is still whole-program. | Mono needs every HIR module. |
| mono | **No.** Whole-program by construction: generic specialization needs every call site. | The "slim summary" idea exists as `SIMPLE_MIR_SHARD_EXPORT_SUMMARIES` / `SIMPLE_MIR_SELECTIVE` (driver_mir_selective_*): today they decide *admission* only ("Lowering still reads the full post-mono HIR", `aot_compile_mir_shard_v1`). Running mono over signatures + generic call sites and lowering bodies afterwards is a frontend redesign, not a driver change. Post-mono streaming is the realistic target. |
| MIR lowering | Per module already (`lower_module_transient_scoped`: the lowering arena is reclaimed per module; the promoted `MirModule` is what stays). | Flat `_bootstrap_*` registries under `SIMPLE_BOOTSTRAP=1` make the scope fall back to plain lowering (module_lowering.spl). |
| MIR verify | Whole set per call (`verify_lowered_mir_v1` walks `ctx.mir_modules`); fatal findings are not attributed to a module. | Batch-granular under staging (section 3). |
| borrow check | Per module, scoped (`borrow_check_module_scoped_v1`), and per-module failure absorption under go-to-end (evicts the failing module, records it). | — |
| optimize / weave / debug-trace | Per module (rules come from HIR advices, not MIR). | — |
| codegen + cache | Per module: cache witness (own MIR + HIR surfaces), frozen capsule, object emission, cold-HIR receipt. The link consumes object paths only. | A cache hit needs the module's lowered MIR for the witness (`driver_native_shadow_witness_v1(ctx, name, ctx.mir_modules[name], ...)`), so a hit saves codegen only, never MIR or borrow. The pre-lowering cache (`SIMPLE_NATIVE_PRELOWER_CACHE=1`) is the only MIR-skipping mechanism and it is all-or-nothing, marked UNQUALIFIED, and refuses staging, sharding and `SIMPLE_BOOTSTRAP`. |

Two existing mechanisms stream MIR -> borrow -> codegen -> release after mono:

1. **In-process staged codegen** (`driver_build/native_staged_codegen.spl`,
   `native_staged_codegen_flush_v1`): every `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH`
   modules the lowering loop verifies, borrow-checks, runs the pass chain,
   emits objects into the native cache (`compile_to_native` in flushing
   mode) and evicts the batch's MIR. Link inputs, outcomes, receipts and
   counters persist in `NativeStagedCodegenStateV1`; the final
   `compile_to_native` call handles the tail batch, verdict and link.
   **It does not lower peak RSS**: `evict_mir_module` only drops a reference
   (no collector; probe P0 reclaimed 0 of 2001 allocations). It bounds the
   MIR that later stages *see*, and it lands objects incrementally.
2. **Process-level MIR shards + fork children** (`native_mir_shard.spl`,
   `native_mir_fork_v1.spl`, coordinator `src/app/cli/native_build_main.spl`):
   after the HIR warm generation, one root worker reaches post-mono state and
   forks N copy-on-write children; each claims up to `ceil(n/N)` ledger rows,
   lowers, borrow-checks, emits, publishes PASS terminals and **exits** — the
   one reclaim that works. The link child admits the sealed ledger.

## 2. Which "Phase 3" runs which lane (this is the crux)

- **Managed script** (`scripts/bootstrap/bootstrap-from-scratch.sh`): Stage 3
  sets `SIMPLE_BOOTSTRAP=1 SIMPLE_BOOTSTRAP_STAGE3=1` with `--entry`, so
  `bootstrap_main.spl` routes to `run_exact_stage3_focused_capsule`
  (`bootstrap_focused_native_build.spl`), which calls
  `aot_native_project_with_backend_fixed` **in process**: no coordinator, no
  HIR/MIR sharding, no fork. It demands `--mode dynload` as an admission
  string but the fixed API compiles with `output_format = native`
  (one-binary semantics; the dynload SMF side artifact is never produced).
  Stage 4 (`SIMPLE_BOOTSTRAP_STAGE4=1`) is the same shape via
  `run_exact_stage4_focused_capsule`. Backend default `llvm-lib` (resident).
  The Stage 3 process runs under `env -i` with the explicit env vector only
  (`command-snapshot.shs:512`), so an exported `SIMPLE_CACHE_SCOPE` never
  reached it (scope was `default`).
- **Ad-hoc Phase 3** (the live `phase3-ref` run-18 read from `/proc`): no
  `SIMPLE_BOOTSTRAP`, `--backend cranelift --mode one-binary --go-to-end
  --cache-dir <stable> SIMPLE_CACHE_SCOPE=phase3-ref SIMPLE_MIR_SHARDING=1
  SIMPLE_MIR_FORK_WORKERS=20 SIMPLE_PARSE_SHARDING=1 SIMPLE_HIR_SHARDING=1
  SIMPLE_HIR_CACHE=1 SIMPLE_FRONTEND_CACHE=1`. This is the coordinator lane
  with fork children: it already streams post-mono at child-share
  granularity (74 modules per child at N=20).

Eligibility (`native_staged_codegen_eligible_reason_v1`) for the managed
lanes with `llvm-lib`: Stage 3 passes every check (the bootstrap-flat
refusal is `not resident_backend and ...`), Stage 4 passes. The only reason
staging was off is `NATIVE_STAGED_CODEGEN_DEFAULT_BATCH_V1 = 0` with the
script never setting the env. The bootstrap-flat refusal (non-resident
backend + `SIMPLE_BOOTSTRAP=1` without STAGE4) stays: that lane lowers
only the entry module and emits ONE object through
`bootstrap_compile_context_to_native_local` (`ctx.bootstrap_entry_mir`,
which `evict_mir_module` would clear) — it is a degraded single-object lane,
not a per-module one, and admitting staging there is unsafe without routing
it to `compile_to_native` and running the pass chain it skips.

## 3. The default (this change)

Script (`bootstrap-from-scratch.sh`), Stage 3 (both invocation copies: the
args-hash vector and the transcribed run, which must stay byte-identical) and
Stage 4 (`bootstrap_native_build_main`):

| Env | Stage 3 | Stage 4 | Opt-out |
|---|---|---|---|
| `SIMPLE_NATIVE_STAGED_CODEGEN_BATCH=32` | added | added | `SIMPLE_BOOTSTRAP_STREAM_OBJECTS=0` (-> 0), `SIMPLE_BOOTSTRAP_STREAM_BATCH=<n>` |
| `SIMPLE_NATIVE_GO_TO_END=1` | added (env: the focused capsule does not parse `--go-to-end`; the driver reads the env) | added | `SIMPLE_BOOTSTRAP_GO_TO_END=0` |
| `SIMPLE_CACHE_SCOPE` | `stage3` added to the `env -i` vector (was `default`) | `${SIMPLE_CACHE_SCOPE:-stage4}` (already exported by `prepare_native_cache`) | — |
| `SIMPLE_FRONTEND_CACHE/_DIR`, `SIMPLE_HIR_CACHE/_DIR` | already set | added (`${native_cache_dir}/{frontend,hir}`; the stage4 cache payload already claimed them) | — |
| `--cache-dir` | `stage3_cache_absolute` (stable) | `prepare_native_cache stage4` (keyed by producer sha; stable per producer) | — |

The shell knobs are not exported; the compiler only sees the `SIMPLE_NATIVE_*`
values, and both are excluded from the native cache identity
(`cache/native_build_environment_identity.spl`): `SIMPLE_NATIVE_GO_TO_END`
was NOT excluded before this change although `go_to_end.spl` claimed it was,
so a go-to-end run's objects lived in a scope a plain run never hit.

Go-to-end verdict: the driver returns `CodegenError(verdict)` after writing
`<output>.go-to-end.sdn`; the focused capsule exits 1; Stage 3's
`stage3_status` and Stage 4's `run_logged` fail the stage. Every good object
is already in the native cache (`build_cache.save()` runs per batch, before
the verdict).

The manifest verifier (`scripts/check/lib/bootstrap-stage3/manifest-verify.shs`,
Stage 3 focused branch) reconstructs the expected vector and now accepts the
three rows exactly when the transcript carries the batch row (ordered, after
`SIMPLE_STAGE3_STREAMING_SURFACES=0`); pre-default transcripts still verify.
`resume-stage3-from-admitted.sh` and `lib/stage3-native-build-worker.sh`
carry their own (managed-resume) vector and are unchanged.

Compiler (`driver_aot_pipeline.spl`):

- `aot_compile` prints `[staged-codegen] refused batch=N reason=...` when a
  requested batch is refused (it used to fall back silently).
- `native_staged_codegen_flush_v1` under go-to-end: absorbs the per-module
  MIR failures the lowering loop already recorded (else the
  `error_count_value == 0` gates withheld every object of a batch that merely
  contained a failed module); a MIR-verify failure withholds and records the
  **batch** (the verifier names no module; invalid MIR must not reach a
  backend) and later batches continue; the verify verdict is no longer
  sticky across batches. Borrow and codegen absorption were already per
  module (`borrow_check`, `module_outcomes` -> `go_to_end_finish_v1`).

Per-stage absorption in streaming mode: HIR per module (pre-MIR,
`go_to_end_recover_hir_v1`), MIR per module, borrow per module, codegen per
module, MIR verify per batch (gap, see 6).

## 4. Combining with fork workers

In the coordinator lane each child is already "stream post-mono, exit": the
share is the batch. To get closer to per-module release, bound a child's
claims (`native_mir_shard_claim_cap_v1` -> min(ceil(n/N), `B`)) and make
`native_mir_fork_shards_v1` re-fork a share whose child finished cleanly
while rows are unclaimed (new owner generation `~g<k>`, distinct from the
`~r<k>` retry owners; stop when a clean round claims nothing). Then peak
private memory per child is B modules, N children run on N cores, and the
root's post-mono heap is shared copy-on-write once. In-process staging inside
a child buys nothing for RSS and is left off there (`begin(0)`).

The managed lanes cannot use this today: the focused capsules are
single-process by admission. Bringing it to them means either routing Stage
3/4 through `run_bootstrap_native_build_coordinator` (what the ad-hoc lane
does; the provenance gate, args-hash transcript and planner admission are
built around the focused capsule) or forking after mono inside the focused
capsule with an in-process ledger. Both are route changes for the owner,
not env defaults.

## 5. Expected peak RSS

- Managed Stage 3/4 with this default: **unchanged peak** (post-mono state
  25-29 GB + every promoted MirModule, measured 83 GiB at module 1187/1302
  before transient scoping; the batch does not free). What changes: objects
  land in the cache per batch, a failed module costs itself (or its verify
  batch), and a rerun hits those objects.
- Coordinator lane with N fork children: shared post-mono ~25-29 GB once +
  N x private(share). The fork design estimated 2-5 GB per child at N=16
  (60-110 GB total). **Unmeasured here**: no fork child was alive during
  this session (the live `native_build_worker` processes with 5.5-6.3 GB
  `Private_Dirty` were spawned HIR/parse warmers of another lane, not COW
  children). With a claim cap B the private part becomes B x per-module
  MIR+codegen residue instead of ceil(n/N) x.
- Cores: unchanged by staging (one process); the fork lane uses N cores
  (`--threads 20`, `SIMPLE_MIR_FORK_WORKERS=20` live), bounded by
  `SIMPLE_MIR_SHARD_WORKER_KB` and the tree-RSS watchdog.

## 6. Gaps recorded (not closed here)

1. Cache hit cannot skip MIR/borrow (witness needs lowered MIR); the prelower
   cache is the only route and is unqualified and refused in these lanes.
2. MIR verify is batch-granular under go-to-end (no module attribution in
   `verify_lowered_mir_v1`); a verify failure costs 32 modules' objects.
3. Sharded go-to-end: children name failures on stderr and seal FAILED
   terminals, but the coordinator stops with "MIR shard aggregate failure"
   and writes no `<output>.go-to-end.sdn`; `aot_compile_mir_shard_v1`'s
   borrow failure path is per module via `borrow_check`, but a child-level
   codegen error withholds that child's whole share.
4. Rolling re-fork with a claim cap (section 4) is designed, not implemented.
5. Mono over slim summaries: frontend redesign; selective/export lanes are
   admission-only today.
6. Manifest under-report in two staged go-to-end shapes: a MIR-verify failure
   in the TAIL batch, or an all-excluded tail (excluded modules `continue`
   before `staged_pending` grows, so the last flush can leave an empty tail),
   takes `lower_to_mir`'s false path into `go_to_end_finish_v1(0, [])` --
   `object_count: 0, built: []` although earlier batches emitted their
   objects (they are in the cache; the verdict is still FAIL). Fix: pass
   `native_staged_codegen.object_files.len()` / `module_outcomes` into
   `go_to_end_finish_v1`.
7. One-time cold caches: Stage 3's scope moves `default -> stage3` and Stage
   4 gains `SIMPLE_HIR_CACHE` / `SIMPLE_FRONTEND_CACHE` (semantic identity
   fields), so the first run after this change misses everything it built
   before. Nothing found reads Stage 3 objects by the old scope, but
   Phase-2 -> 3 (`M3`) reuse and the `SIMPLE_PHASE3_COMPATIBILITY_CACHE_ROOT`
   consumers are unverified under the new scope.
8. Nothing here was executed: no compiler binary is deployed in the worktree
   and builds are forbidden this session. The unit spec addition is marked
   UNEXECUTED; `scripts/bootstrap/tests/stage3-invocation-consistency-test.py`
   passes (shell stubs); `stage3-focused-provenance-test.py` fails identically
   at baseline (exit 90 precondition), so it is not a signal either way.

## 7. Review of release safety (item 3 of the request)

After a batch is evicted nothing re-reads it: the link consumes
`object_files`; cold-HIR receipts are recorded per module at codegen and
persisted from the receipt maps; the package index and `runtime/std`
emissions (`publish_runtime_std_mir_emissions_v1`, the late `ctx.mir_modules`
readers in `driver_runtime_std_compile_native_*`) run only under
`runtime_std_full_inventory_selection`, which the eligibility refuses; SMF
/ self-contained / both formats (the aspect-pack readers) are refused;
`bootstrap_entry_mir` is only read by the refused flat lane; the storage
registry is frozen for the whole schedule at the first flush.
