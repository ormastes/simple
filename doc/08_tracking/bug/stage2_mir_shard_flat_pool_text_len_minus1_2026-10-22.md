# Stage2 MIR shard: flat-pool encode of MIR artifact sees invalid text handle (rt_string_len == -1), worker stack-overflows

Date: 2026-10-22
Lane: bootstrap-from-scratch, stage2 gate (attempt 36)
Tree: release/1.0 @ a868480a973 (includes PR #4162 HIR crash fixes)

## Symptom

`candidate_frontend_smoke: p2_add-build failed (raw rc=125)` at the stage2
sanity gate. The stage2 candidate compiles `p2_add.spl` through HIR
successfully, then fails while serializing the MIR artifact:

```
flat pool encoder string builder append failed site=text.value item=0 input_length=-1 result=0
[mir-shard] owner=0/1@0 status=CRASH exit=-1073740791 claimed=0 sealed=0 finished=false
[mir-shard] inventory incomplete rows=-1 policy_fail_fast=false
[mir-shard] completed_workers=0 failed_workers=2 failed_modules=0 unfinished=-1
[mir-shard] outcome=fallback exit=1 ... falling back to in-process unsharded MIR
error: native-build worker exited with code -1073740791.
... (fallback, in-process) ...
error: native-build worker terminated with Windows native status 0xC0000409 (fail-fast termination)
```

exit=-1073740791 == 0xC00000FD (stack overflow) in the MIR shard worker.
The subsequent 0xC0000409 is the in-process fallback dying on the same
corrupt state.

## What the diagnostic proves

`flat_pool_builder_push` (src/compiler/10.frontend/core/flat_pool_codec.spl:454)
panics with this message only when `rt_string_builder_push` rejects the
append, and then reports `rt_string_len(value)` of the rejected input.
`input_length=-1` means the `value` text handle is INVALID (foreign /
dangling) at encode time — `rt_string_len` returns -1 for it.

- site=3 (`text.value`), item=0: the FIRST element of the FIRST text pool
  of the MIR artifact is corrupt.
- The encoder itself is unchanged and was reliable before; this is value
  corruption upstream of encoding, not an encode-logic bug.
- HIR phase is clean on this tree: `[hir-shard] done shard=0/1 lowered=1`,
  `failed_workers=0`, `hir-cache stores=1 selfchecked=1`. The corruption
  appears in (or before) MIR artifact pool construction.

## Suspects

1. Interaction between the new dict-literal-typed `HirLowering` fields
   (8a447adbdb4 "declare HirLowering dict fields with literal types, not
   aliases") and the MIR artifact handoff: a field that previously rode an
   alias type may now be stored/extracted differently, leaving a non-text
   word in a text pool.
2. MIR-side pool construction storing a garbage/foreign handle into a text
   pool for values it never validated (module names, string literals,
   symbol spellings). p2_add is tiny (a single `print` of an integer add),
   so the first text pool is likely string-literals or symbol/module names.

## Repro (deterministic, ~10s)

```
CAND=.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected
env SIMPLE_HIR_SHARDING=0 SIMPLE_LIB=$PWD/src SIMPLE_BOOTSTRAP= SIMPLE_FRONTEND_CACHE=0 \
  "$CAND" native-build --entry src/compiler/bootstrap_admission/p2_add.spl \
  --runtime-bundle core-c-bootstrap --entry-closure --mode one-binary \
  -o /tmp/p2_add_probe.exe
```

(shard-off repro hits the same path via the in-process fallback.)

## Notes

- The refusal instrumentation from d9fd506b9b9 / a868480a973 works: the
  refusal print appears and is flushed.
- `[frontend-cache] store failed: cannot write under .../stage2-tmp/...`
  (`dir_create_all=true`) appears in the same window; modules reparse.
  Looks like a benign tmp-dir IO race, noted separately from this defect.
- Not yet verified on: any tree after a868480a973.

## Update 1 (2026-10-22, same day) — exact-env repro, io-write side-channel, policy-gate datapoint

### Exact-environment repro (9 seconds, reproduces the crash)

The generic repro in the section above does NOT reproduce this crash — it
takes a different path and dies earlier at a policy gate (see below). The
gate's delegated environment is required:

```
CAND=$PWD/.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected
env SIMPLE_BINARY="$CAND" SIMPLE_BIN="$CAND" SIMPLE_BOOTSTRAP_DRIVER="$CAND" \
    SIMPLE_FRONTEND_DELEGATE="$CAND" SIMPLE_FRONTEND_DELEGATED=1 \
    SIMPLE_NO_STUB_FALLBACK=1 SIMPLE_NATIVE_BUILD_FORCE_WORKER=0 \
    SIMPLE_BOOTSTRAP=0 SIMPLE_LIB=$PWD/src \
    "$CAND" native-build --backend llvm --runtime-bundle core-c-bootstrap \
    --entry-closure --entry src/compiler/bootstrap_admission/p2_add.spl \
    --cache-dir <fresh-temp>/cache --mode one-binary --output <out>
```

With this env the full crash chain reproduces in ~9s: flat-pool panic,
mir-shard worker 0xC00000FD, fallback 0xC0000409. (SIMPLE_HIR_SHARDING=0 in
the original repro also matters: without delegation the build reaches MIR
through a different route.)

### Side-channel: every hir-cache store fails io-write (both processes)

Immediately before the panic, the DRIVER logs:

```
[hir-cache] hits=0 misses=1 stores=0 refused=0 io_failed=1 reason=io-write dir=<home>/.cache/simple/v1/projects/7dcf…/native-build/v1/default/hir ... selfchecked=1 selfcheck_failed=0 store_failures=1
```

- The encode + selfcheck SUCCEED (artifact bytes valid); only the FILE WRITE
  fails (`rt_file_write_text` at driver_hir_cache.spl:478).
- The directory tree is created successfully all the way down (verified on a
  fresh HOME); the file write itself is rejected.
- Reproduces on any cache root (user cache, fresh temp HOME, lane
  stage2-home), so it is not stale-dir state or permissions.
- All candidate writes route through the SECURITY runtime
  (src/compiler_rust/runtime/src/security_runtime.rs: rt_file_write_text is
  policy-gated; `registry().is_allowed(...)` / LAST_POLICY_ALLOWED). Next
  probe: whether the sandbox write policy's allowlist excludes these cache
  roots; a deny would explain the universal io-write.
- The store failure is designed non-fatal ("a cache that cannot store is a
  slow build, not a wrong one"), and the mir worker then runs in
  `hir-recovery` mode (ledger dir `hir-recovery/mir-queue-*`). The invalid
  text appears in a recovery-mode artifact encode — the two failures are
  likely causally linked (recovery path encodes a text it does not own).

### Datapoint: non-delegated env fails EARLIER at a policy gate

Without the delegate env (plain `SIMPLE_HIR_SHARDING=0` repro), the build
dies at:

```
[ERROR] MIR error: MIR final repository policy or emission schedule differs
```

i.e. `lower_archived_to_mir_v1` (driver_pipeline_lowering.spl:612-615):
archived `MonoArchiveFinalRepositoryV1` has force_all_sources /
allow_bootstrap_shortcuts / bootstrap_mode / empty emission_rows mismatching
the caller's expectation. With SIMPLE_BOOTSTRAP=0 the archived
`bootstrap_mode == "1"` arm matches; whether that is intended admission
policy or part of the same regression needs the archived repository's
provenance.

### Next probes (ordered)

1. Security-runtime write policy: log the deny decision for
   `rt_file_write_text` (or inspect the allowlist) — confirms/refutes the
   io-write root cause.
2. Print-marker the recovery-mode artifact encode in the mir shard worker:
   which record's first text field is encoded, and its provenance (scope
   owner).
3. If (1) confirms a policy deny: fix the allowlist (or route hir-cache
   under the admitted cache root), then re-run the 9s repro to see whether
   the invalid-text panic disappears with the recovery path.

## Update 2 (2026-10-22, later) — probes 1-3 results: io-write mechanism narrowed, cache-off differential

### Probe results

1. **Security capability gate: EXONERATED as the write blocker.** The sandbox
   capability check (`rt_security_sandbox_capability_allowed`,
   security_runtime.rs:370) only denies when a sandbox lowering with a
   capability list is ACTIVE; no compiler/lib source declares a sandbox
   lowering that ships in the candidate (only a baremetal RISC-V PMP test
   spec and PayPal "sandbox" booleans match the keywords). Weaver-inserted
   `rt_security_enter_sandbox` only wraps declared `HirSecurityGate`s, and
   none gate the hir-cache path. Moreover the SAME RUN successfully writes
   frontend-parse-cache (`.fpc`), ledger `BLOCKED`/`*.claim` files, and
   queue dirs — so candidate file writes generally WORK; only the hir-cache
   store fails.
2. **Path length: EXONERATED.** Repro with `HOME=/c/h` (total store path
   ~130 chars) still fails io-write identically. The long stage2-home lane
   paths exceed MAX_PATH and are a secondary hazard worth fixing, but not
   this failure.
3. **`SIMPLE_HIR_CACHE=0` differential: the failure MOVES, it doesn't
   clear.** With the cache disabled the flat-pool panic count drops 2→1
   and the build instead fails at:
   ```
   [ERROR] NOGC-POLICY-001: .../p2_add.spl: cached HIR ownership policy disagrees with its declaring source
   ```
   (driver_hir_pipeline_support.spl:341: freshly-lowered HIR module's
   `nogc_strict` disagrees with the surface registry's `nogc_strict` for
   the same canonical path, or two surfaces for that path conflict.) So
   the candidate carries an ownership-policy metadata inconsistency that
   different gate paths surface differently: cache-on → store fails →
   hir-recovery → invalid-text panic; cache-off → NOGC policy refusal.

### Current model

- The invalid-text panic and the io-write are probably BOTH symptoms of the
  same metadata inconsistency (recovery path encodes a half-constructed
  artifact; the store itself may fail because its encoded header/path folds
  a scope/ownership value that isn't valid in the storing context).
- Next probes: (a) print `nogc_strict` (surface vs HIR module) for p2_add
  in both the passing pre-regression tree and this one — the delta names
  the regression commit; (b) patch `rt_file_write_text` to surface the
  io::Error string (one-line Rust change; rebuild candidate ~35 min) —
  the errno will likely be ERROR_PATH_NOT_FOUND from a component that is
  a FILE or an invalid handle path, naming the exact bad path component.

## Update 3 (2026-10-22, later still) — localized: seed by-value transport of the 30-limb ParserModule, pre-`new()` hops unbound

The NOGC datapoint localizes the corruption precisely:

- `nogc_strict` is set ONLY by the `@no_gc(strict)` marker
  (`module_assembly.spl:955-958`, `var module_nogc_strict = false` at :364).
  p2_add.spl and its SCV snapshot carry NO marker, so a correct parse yields
  `false` on both sides of the NOGC check
  (driver_hir_pipeline_support.spl:341: `matched and actual.nogc_strict != strict`
  fires only if the SURFACE's `nogc_strict` reads non-false — garbage).
- The surface's `nogc_strict` is copied field-by-field in
  `ModuleSurfaceParserOwner.new` (module_surface_declarations.spl:269), the
  struct 205ea9e92a1 flattened to handle-sized limbs because its
  `owner.value.name.len() == -1` — THE SAME -1 SIGNATURE AS THIS BUG.
- 65d9f2afadc added the typed local-bind INSIDE `new()` (ctor's own
  param→field copy), fixing that ONE hop. But the module still crosses
  THREE earlier by-value hops in the same call chain, none bound:

  ```
  me add_parsed(module: ParserModule, ...)                (module_surface_registry.spl:180)
    → me add_parsed_canonical(module, ...)                (:184)
      → fn module_surface_from_module(module, ...)        (module_surface_declarations.spl:611)
        → ModuleSurfaceParserOwner.new(module)            (fixed internally, 65d9f2afadc)
  ```

  If ANY earlier hop corrupts the 30-limb aggregate, `new()` binds and
  stores garbage: `name.len() == -1` (the flat-pool invalid text) and a
  non-zero `nogc_strict` (the NOGC-POLICY-001 mismatch) are two reads of
  the same corrupt owner — one mechanism explains both symptoms.

### Next action for the fixer

Per the established workaround family (65d9f2afadc, c62893c28fc): typed
local-bind `ParserModule` at the ENTRY of `add_parsed` (and/or convert the
chain to pass the owner, not the raw module), then verify with the 9s repro
(probe chain in Update 1) — expect the flat-pool panic AND the NOGC refusal
to clear together, and the hir-cache stores to start succeeding (the
io-write may be a third read of the same corrupt owner: the store key/path
folds a module field). The proper repair remains the seed's aggregate
by-value transport (see 205ea9e92a1 commit message).

## Update 4 (2026-10-22, attempt 37) — binds merged: io-write CLEARED; crash narrowed to the worker's frontend-cache store

Landed the Update-3 binds (PR #4168: typed local binds at add_parsed /
add_parsed_canonical / module_surface_from_module / add_surface_canonical /
add_surface_canonical_identity). Lane attempt 37 on the fix tree:

- **hir-cache stores now SUCCEED**: `[hir-cache] stores=1 ... io_failed=0`
  (was io_failed=1 in every prior attempt). The surface-registry transport
  binds fixed the store path — one symptom cleared, binds kept.
- **The flat-pool panic persists, unchanged**: `site=text.value item=0
  input_length=-1` inside the MIR worker, now precisely localized by the
  log ordering:
  1. worker re-parse: `[frontend-cache] hits=1` (module comes from the
     `.fpc` DECODE, not a fresh parse);
  2. worker store attempt: `[frontend-cache] store failed: cannot write
     under <probe-cache>/default/frontend (dir_create_all=true)`;
  3. flat-pool encoder panic on the store's artifact — the FIRST text pool's
     first item is an invalid handle.
  So the panicking encode is the **frontend parse-cache (.fpc) store of the
  DECODED ParserModule**: the `.fpc` decode path yields a module whose first
  text field is invalid in the storing scope. Suspects, in order:
  (a) `.fpc` decode registering text pool items in a scope that ends before
  the re-store encode (owner/scope bug, same family);
  (b) `.fpc` decode field mis-read (aggregate decode of the 30-limb struct).
- **The `dir_create_all=true` failure on a fresh tmp tree is a second,
  independent defect**: some subsystem lays `frontend` down as a FILE while
  the store path expects a DIRECTORY (or vice versa) — the driver's queue
  dirs and `.fpc` files coexist under `cache/default/` in preserved repro
  trees. A file/dir layout race between driver and worker processes would
  produce exactly this. Worth its own probe: stat the path at store time.

Next probes: (1) print the first text pool's item-0 provenance in the .fpc
store encode (which ParserModule field, decoded from which pool row);
(2) stat `cache/default/frontend` at store time in both processes;
(3) if (a): bind the decode scope owner across the store; if (b): fix the
decode field offset.

## Update 5 (2026-10-22, later) — store-path reading corrected; file/dir race exonerated; capture-blob + emission-record suspects

Two corrections to Update 4's model, from reading frontend_parse_cache.spl
and frontend.spl:

1. **The stored blob is NOT a re-encode of the decoded module.** The parse
   path encodes DURING the fresh parse: `flat_pool_capture_arm()` before
   `parse_and_build_module_scoped(...)`, `flat_pool_capture_take()` after;
   `frontend_parse_cache_store(key, captured_blob)` just writes those bytes
   (frontend.spl:166-171, frontend_parse_cache.spl:174-190). So the panicking
   flat-pool encode is whichever encode runs at that point in the worker —
   and the log places the panic at the START of the worker's hir phase
   (right after `[bootstrap-error-count] point=entry`), i.e. NOT the parse
   capture. Prime suspect: the **HIR emission-record publication**
   (`RuntimeStdMirModuleEmissionV1`, driver_pipeline_lowering.spl:540-604
   family) whose first text field (module/source identity) is invalid in the
   worker's scope.
2. **The `frontend` file/dir race is exonerated.** All preserved repro trees
   (`/tmp/p2g3`, `/tmp/p2gate2`, `/tmp/p2g4`) show `cache/default/frontend/`
   as a consistent DIRECTORY holding the `.fpc` file, queues, and BLOCKED
   markers. `dir_create_all` returned true in the failure message; the write
   itself failed (`file_write_exact`, io_runtime.spl:278 — one-shot write via
   `file_write_bytes`). With pid-unique tmp + rename, a same-key concurrent
   store from the driver process (sharing violation on tmp create, or
   file_write_bytes' internal policy) is the remaining explanation for the
   store-failed line — a cache-efficiency defect, not the crash.

### Next probes

1. Print the emission-record text fields (module_identity, source_identity)
   at publish time in the mir worker — which one is invalid and where it was
   built (driver-side receipt? worker-side re-parse? queue-file read?).
2. If driver-side: the receipt/emission texts cross into the worker via the
   mir-queue ledger files — check the decode of those rows (same aggregate
   decode family as the .fpc suspicion).
3. The store-failed line: `file_write_bytes` status for the pid-unique tmp
   under concurrent same-key stores (driver + worker share one cache dir by
   design — "shard workers of step 4 run in parallel processes over one
   cache dir", frontend_parse_cache.spl:170-172).

## Update 6 (2026-10-22, later still) — unsharded differential: corruption is worker-side; parent is clean

Ran the canonical repro with `SIMPLE_MIR_SHARDING=0` (fresh `/tmp/p2g5`,
attempt-37 rejected candidate, which carries the merged binds):

- The panic STILL fires (once instead of twice) — a native-build worker
  process stack-overflows (`worker exited with code -1073740791`) and the
  flat-pool panic prints from the worker boundary. So the corruption is NOT
  an artifact of MIR sharding.
- The PARENT's own pipeline is fully clean: parse OK, surface OK, hir
  `done=1` with post-lowering/diagnostics/store all `count=0`, then
  `[hir-shard] done shard=0/1 lowered=0 claimed=1` — the shard CLAIMS p2_add
  and lowers NOTHING (recurring signature across attempts). Everything the
  WORKER process touches is corrupt; everything in-process is fine.
- The worker re-acquires the module via the shared parse cache
  (`frontend_shared_parse_load_v1` → `build_module_from_flat_pool_blob`) —
  the parent's private `.fpc` store FAILED in this run, so the worker's hit
  can only have come from the SHARED store (`frontend_shared_parse_store_v1`,
  frontend.spl:170) — making the SHARED BLOB DECODE the prime suspect for
  the invalid first text field.
- io-write reopened: the SAME attempt-37 binary stores fine in the lane
  (driver `stores=1 io_failed=0`, long stage2-home path) but fails in the
  repro (`store failed at write`, short C:\h path). Same binary, different
  env: the lane sanity sets `SIMPLE_FRONTEND_CACHE=0` (suppresses the
  frontend store entirely — masking the write failure class) and the
  route/shard envs (`SIMPLE_HIR_SHARD_OWNER/QUEUE`, ABI/LINKER vars) that
  feed `native_build_environment_identity`. The hir-store write failure is
  therefore env/identity-dependent, NOT fixed by the binds per se; the lane
  masks it. Treat the io-write as still open with a narrower suspect set
  (environment-identity-derived scope/path).

### Refined next probes

1. Decode a captured shared-parse blob standalone and print the first text
   pool item's field name + validity (answers the shared-decode suspicion
   without a rebuild, using the seed or the `.fpc` on disk).
2. In the worker: print the module name/source identity immediately after
   `build_module_from_flat_pool_blob` returns (before any use) — if invalid
   at that point, the decode is proven corrupt.
3. For the store write: run the repro with `SIMPLE_FRONTEND_CACHE=1`
   explicitly and diff `hir_cache_dir()`/store path against the lane's.

## Update 7 (2026-10-22, latest) — mechanism found: pool-backed decode lifetime vs re-encode

`build_module_from_flat_pool_blob` (module_assembly.spl:1412-1465) decodes
via the LEGACY REFERENCE provider:

```
reset_all_pools()
parser_init_with_path(source, path)
flat_pools_restore_all(blob)     # module texts LIVE IN THE POOLS
flat_ast_to_module(path)         # module references pool-backed texts
```

The restored ParserModule's text fields are pool-owned references, not
independent copies. Any later `reset_all_pools()` (next decode, next parse
capture arm, pool maintenance) frees those texts; a later flat-pool ENCODE
of anything holding them then reads dangling handles —
`rt_string_len == -1`, `site=text.value item=0` — exactly this crash, and
the worker's extra reset/claim cycle explains why the parent survives and
the worker dies. This also finally unifies the whole evening: every symptom
(io-write key computation, NOGC strict read, emission-encode panic) is a
read of a pool-backed or by-value-transported text at a point where its
owner scope has ended — one bug family, three faces.

### Fix directions (choose with the seed/compiler owner)

1. **Promote on decode**: after `flat_ast_to_module`, deep-copy the module's
   identity/path texts into caller-owned storage (the "retained scalar
   owners" pattern the streaming commit already documents). Cheap, local,
   matches the workaround family.
2. **Extend the pool lifetime**: keep the module's pools pinned until the
   module is dropped (refcount or arena membership) — durable but touches
   the pool allocator.
3. **Stop re-encoding decoded modules**: the worker only needs the module
   for lowering; if nothing re-encodes it, the dangling texts are never
   read. Audit which worker path re-encodes (the emission publish / claim
   row) and give it owned copies instead.

Probe that proves it without a rebuild: watch `reset_all_pools` call sites
between `flat_pools_restore_all` and the panicking encode in the worker
(gdb breakpoint or an env-gated counter print on reset).

## Update 8 (2026-10-22, proof) — decode-dangle PROVEN; policy gate is the next blocker

Canonical delegated repro + `SIMPLE_FRONTEND_CACHE=0` (no private cache →
no decode path; every parse is fresh):

- **ZERO flat-pool panics** (every cache-enabled run had 1-2).
- The build runs parse/surface/hir/MIR-start cleanly — worker included —
  and stops at the NEXT gate: `[ERROR] MIR error: MIR final repository
  policy or emission schedule differs` (lower_archived_to_mir_v1,
  driver_pipeline_lowering.spl:612-615; archived `bootstrap_mode == "1"`
  vs the smoke's `SIMPLE_BOOTSTRAP=0`).

Conclusions:

1. The pool-backed decode is the sole source of the invalid-text panic.
   With no decode, the same binary/worker/flow is clean through MIR.
2. The stage2 gate therefore has exactly TWO remaining defects, ordered:
   (a) the decode-dangle (this doc) — crashes with the cache enabled,
       which is the gate's default;
   (b) the archived-repository policy mismatch (bootstrap_mode=1 archive
       vs bootstrap=0 smoke) — the next blocker, visible only once (a) is
       fixed. Attempt 30 (pre-regression) passed sanity, so the
       archive/smoke contract held before the regression range — one side
       changed; bisect from `final_repository.bootstrap_mode` assignment.
3. The re-encode site for (a) is NOT the module re-store (hit paths don't
   store): it is an encode of a structure that HOLDS decoded pool-backed
   texts — prime candidate the HIR emission record
   (`RuntimeStdMirModuleEmissionV1(module.name, ...)`,
   runtime_std_mir_emission_v1.spl:105) built at hir entry from the
   decoded module and serialized later. Fix shapes: promote the decoded
   module's texts (owned copies at decode or at record construction), or
   pin the pools across the module's lifetime.

## Update 9 (2026-10-22) — defect (b) mapped: archive records raw SIMPLE_BOOTSTRAP; route engagement is the regression

The policy check reads `MonoArchiveFinalRepositoryV1.bootstrap_mode`,
assigned at issuance (hir_mono_final_repository_v1.spl:307) as the RAW env
value: `bootstrap_mode: env_get("SIMPLE_BOOTSTRAP")`. The lane builds the
candidate/archive under `SIMPLE_BOOTSTRAP=1` → archive carries "1"; the
smoke runs the candidate with `SIMPLE_BOOTSTRAP=0`
(candidate_frontend_admission.shs, CANDIDATE_FRONTEND_BOOTSTRAP default) →
`lower_archived_to_mir_v1` (driver_pipeline_lowering.spl:614, "only issued
by the real full0 production owner", fatal on mismatch) rejects. The
mismatch is SEMANTICALLY real (bootstrap_mode changes lowering,
module_build.spl:313+), so blind normalization is wrong.

The regression is ENGAGEMENT, not the check: attempt 30 (pre-regression)
passed sanity, so the p2_add smoke previously never reached the archived
route — no final repository existed in its fresh probe cache. Now something
publishes a MonoArchiveFinalRepository that the p2_add smoke can see (build
phase leaking into probe-visible cache, or the mono-final route newly
engaging for tiny builds). Bisect from the mono/archive lane
(dc7e9136bf1, 8a447adbdb4 family) — the parallel session owns it.

### Ordered critical path to a green stage2 gate

1. (a) decode-dangle (Update 8) — crash with cache enabled (gate default).
2. (b) this — policy mismatch, visible once (a) clears.
Both fixes are in lanes the parallel session is actively landing; adopt
theirs or land mine with the 9s repro (Update 1) + lane as verification.

## Update 10 (2026-10-22) — fix-shape analysis for (a); why a blind edit is deferred

Investigated the three documented fix shapes against the source:

1. **Promote decoded texts** (`rt_transient_heap_promote`, collections.rs:2858):
   SHALLOW per-object retag. A ParserModule's texts live in separate heap
   objects (struct fields, Dict keys/values, import rows) — a correct
   promote needs enumeration of ~30 fields plus nested containers, and
   `reset_all_pools()` frees the POOLS, not just tagged objects; pool
   blocks the decoded strings point into may not even be registry
   objects. High effort, moderate risk blind.
2. **Pin pools across the module lifetime**: the bridge is pool-backed by
   design (flat_ast_to_module, module_assembly.spl:286 — "legacy reference
   provider"); pinning changes the arena contract. Too big for an
   unverified edit.
3. **Owned copies at the panicking encode site**: cheapest, but the site is
   inferred (emission record), not confirmed. One 35-min lane per guess.

Mechanism note for the gdb pass: `rt_string_builder_push` rejects the text
because the bytes are DANGLING (pool freed), so `rt_string_len` reads
garbage → -1. In the parent the same encodes succeed because its parse
scope is still alive; the worker's hir phase runs after the worker's parse
scope ended (or after a second `reset_all_pools`). The discriminating
breakpoint: `reset_all_pools` between `flat_pools_restore_all` and the
panic, in the worker process.

**Standing offer**: if the parallel session confirms the encode site (gdb)
or lands the pool-lifetime repair first, this doc's repros (Update 1) and
differentials (Update 8) verify it in 9 seconds plus one lane.

## Update 11 (2026-10-22) — delegation structure + trace-level sequence; store-failure is flaky

Env-gated traces (SIMPLE_PARSE_PHASE_PROFILE=1,
SIMPLE_FRONTEND_CACHE_BOUNDARY_PROFILE=1, SIMPLE_FLAT_POOL_ROUNDTRIP=1) on
the canonical repro yield the exact sequence (one log, processes
interleaved):

1. Driver: PARSECACHE load bytes=0 (miss) → FLATROUNDTRIP reset=true
   ok=true stable=true (capture selfcheck SUCCEEDS) → dump 4582 →
   PARSECACHE store stored=TRUE (the frontend store succeeded under trace
   env — the "store failed" line in prior runs is FLAKY/nondeterministic,
   likely a timing race, and is NOT the crash) → desugar.
2. Delegate child (the same candidate re-exec'd via
   _cli_run_frontend_delegate, cli_ops.spl:392-395, loop-guarded by
   SIMPLE_FRONTEND_DELEGATED): PARSECACHE load bytes=4582 (HIT) →
   PARSECHEHIT init=0 restore=0 bridge=0 total=1ms (decode SUCCEEDS, module
   built cleanly) → desugar → **flat-pool panic at the following hir phase**.

Refined mechanism: the crash is in the DELEGATED FRONTEND child. The
decode itself is clean (1ms, PARSEHIT ok); the module's texts are
pool-backed and something between the decode and the hir-entry encode
frees them. Candidates for the freeing event: a second
`reset_all_pools()` (module_assembly.spl:1430 runs at EVERY decode entry —
any second parse/decode in the child dangles the first module), or the
child's parse-scope end before hir. The child's parse set for p2_add is
minimal, so instrumenting `reset_all_pools` (call-site counter print under
an env gate) in ONE candidate build discriminates these definitively.

Also confirmed: `hir-shard done lowered=0 claimed=1` co-occurs — the shard
claims and lowers nothing because the delegated child's lowering never
completes.

## Annotation 2026-10-23 (lane A, macOS aarch64): crash backtrace + progression note

Independent reproduction on the stage-2 sanity gate
(`bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2`,
release/1.0 @ ab07dfa3) after landing the reverse-reference publish
workaround (stage2_sanity_reverse_reference_publish_refused_2026_10_22):
the sanity p2_add build now reaches the flat-pool crash instead of the
publish refusal — progression, same bug.

macOS crash report (`~/Library/Logs/DiagnosticReports/simple-2026-10-23-003331.ips`):

```
SIGABRT  byProc=simple
  abort <- std::process::abort <- rt_panic
  <- compiler__frontend__core__flat_pool_codec__flat_pool_builder_push
```

So the panic fires inside `flat_pool_builder_push` itself (encode side),
consistent with the "texts freed between decode and hir-entry encode"
mechanism above. The driver-side log ends at `phase=hir current=...p2_add`
with no diagnostic text — the aborting frame is in the delegated child.

## Annotation 2026-10-23 (lane A, macOS): env-knob discrimination + pool instrumentation

Owning lane quiet >6h; lane A took over the discrimination per the crash
cycle cap. Repro (10 s, no rebuild needed):

```
CAND=$PWD/.simple/storage/build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected
env SIMPLE_BINARY=$CAND SIMPLE_BIN=$CAND SIMPLE_HIR_SHARDING=0 SIMPLE_LIB=$PWD/src \
  SIMPLE_BOOTSTRAP= "$CAND" native-build --entry src/compiler/bootstrap_admission/p2_add.spl \
  --runtime-bundle core-c-bootstrap --entry-closure --mode one-binary -o /tmp/p2_add_probe
```

Results on candidate ab07dfa3-era (with rr-publish workaround):
- `SIMPLE_FRONTEND_CACHE=0` (no decode): NO crash — clean, later,
  unrelated failure (`MIR final repository policy or emission schedule
  differs`, exit 1). So the crash REQUIRES the parse-cache decode path.
- Cache on + `SIMPLE_FRONTEND_DELEGATED=0`: still SIGABRT, same locus
  (`rt_panic <- flat_pool_builder_push`, byProc=simple.rejected). So the
  panic is in the candidate's own encode, delegation-independent.
- Conclusion: the dangling-text window is the decode-hit rebuild
  (`build_module_from_flat_pool_blob`) and the hir-entry encode.

Instrumented (SIMPLE_POOLDBG=1, env-gated): a reset counter print inside
`reset_all_pools` plus a pool-state probe (`flat_pool_debug_state_v1`) at
decode-built, in compiler.core.types. Sequence discrimination: a reset
line between `decode-built` and the push panic => second-reset theory
(module_assembly decode entry); no reset => scope-teardown reclaim theory.

## Annotation 2026-10-23 (lane A, macOS) — DISCRIMINATED: silently-lossy child-side restore

Instrumentation (SIMPLE_POOLDBG=1, landed 02766366496) trace on the 10 s
repro, candidate = stage2 rejected binary built from 02766366496:

```
[pooldbg] reset_all_pools n=1                      <- decode-entry reset
[pooldbg] decode-built resets=1 tok_text=0 sym_names=0 spans=78
[build] phase=hir ... current=compiler.bootstrap_admission.p2_add
[pooldbg] reset_all_pools n=2                      <- HIR-entry re-parse reset
```

Facts established:
1. The stored blob DOES contain the token texts (`grep -c print` on the
   .fpc under build/bootstrap/native_cache/default/frontend = 4 hits,
   4939 bytes). Capture side is complete.
2. The blob is FRESH — written by this same candidate moments earlier
   (frontend cache was wiped first), so no producer/version skew.
3. `build_module_from_flat_pool_blob` returned Some (restore reported
   TRUE) yet `tok_pool_text.len()==0` and `sym_names.len()==0` right
   after `flat_ast_to_module`, while `span_pool_start.len()==78`.
   This is exactly the "successfully-restored empty parse" shape this
   codec's contract forbids — the text/symbol pool sections restore into
   nothing readable, in the delegated child.
4. Parent-side roundtrip selfcheck (other lane's trace) reports
   reset=true ok=true stable=true — so in the PARENT the same restore
   population works; the loss is specific to the child context.
5. The reset at HIR entry (n=2) is the driver's legitimate re-parse; it
   is not the dangling cause. With cache off (no decode) the build does
   not crash (it fails later at an unrelated MIR repository policy
   check), confirming the corruption enters via the decode path.

Prime suspect: binding duplication in the dynload candidate's delegated
child — the section restore for the parser-state pools (tok_pool_text,
sym_names) writes one copy of the process-global pool arrays while
`flat_ast_to_module` reads another (same baked-vs-loaded family as the
shard-worker stale-code finding, c53a65fe). Spans survive because the
decl-pool section resolves to the same binding on both sides.

Discriminating next probe (one candidate build): print
`tok_pool_text.len()` at the end of `flat_parser_state_restore` (and
which section restore owns it) plus the module's first text len inside
`flat_ast_to_module`; a write/read split confirms the duplication and
names the sections. Lane A stops here (cycle cap); cure is either a
restore-path binding fix or the runtime class-layout repair.

## Correction 2026-10-23 (lane A follow-up): probe was on the wrong pools

Two corrections to the binding-duplication suspicion above:
1. `reset_all_pools n=2` at HIR entry is the legitimate streaming
   re-parse: it comes from `parse_and_build_module_with_scope_owner`
   (module_assembly.spl:1511), the HIR phase's per-module surface
   re-parse. It is followed by a fresh parse that repopulates pools.
2. `tok_pool_text`/`sym_names` are lexer/parser scratch; a
   decode-restored module legitimately has them empty (the module graph's
   texts live in the decl/expr pool text sections, which my probe did not
   watch). So tok_text=0 at decode-built is expected, NOT evidence of a
   lossy restore, and the binding-duplication theory is weakened.

Sharper facts for the next probe: the panicking pool is the MIR ARTIFACT
text pool (encode side, site=text.value item=0), a different pool set from
the frontend scratch pools. Target probes: (a) decl/expr pool text lens at
decode-built vs after the HIR re-parse reset (n=2) — if the artifact's
texts are taken from the decode module rather than the re-parsed module,
the n=2 reset + no-rebridge is the dangler after all; (b) the cache-off
companion failure `MIR final repository policy or emission schedule
differs` (exit 1, no crash) points at the artifact EMISSION SCHEDULE being
computed and validated across the parent/child boundary — check whether
the schedule carries process-local text handles.

## Annotation 2026-10-23 (lane D, x86_64-pc-windows-msvc): reset-sequence trace CONFIRMS the n=2-reset window

Independent MSVC confirmation with an env-gated `reset_all_pools` counter
(committed as 92c7630d2fa on work/pool-reset-trace-20261022, base
01de698b310; lane 38 candidate preserved at
.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected).
Repro: the 9 s p2_add native-build repro with `SIMPLE_POOL_RESET_TRACE=1`
(SIMPLE_FRONTEND_DELEGATED=1, cache dir fresh; crash deterministic).

Trace, crash run (frontend-cache HIT):

```
[pool-reset] n=1                      <- decode-entry reset (module_assembly.spl:1430)
[frontend-cache] hits=1 misses=0      <- decode path taken
[build] phase=hir current=...p2_add
[pool-reset] n=2                      <- HIR borrowed-scope re-parse reset (module_assembly.spl:1511)
flat pool encoder string builder append failed site=text.value item=0 input_length=-1
```

Companion miss-path run (store-failed -> reparse): n=1 -> parse -> n=2 ->
HIR SUCCEEDS. So the n=2 reset is present in BOTH paths; only the
decode-hit path panics. The miss path survives because its module was
promoted out of the transient scope (rt_transient_heap_promote,
module_assembly.spl:1612) before the n=2 reset; the decode-hit module
(build_module_from_flat_pool_blob, no scope, no promote) keeps texts that
die at the n=2 reset and the MIR artifact encode reads the dead handle.

This confirms correction-note probe target (a) on the second platform:
the artifact's texts come from the decode module and the HIR-entry
re-parse reset + no-rebridge is the dangler. The n=2 reset originates
from the HIR phase's borrowed-scope per-module re-parse
(driver_hir_pipeline_lowering.spl:606/822 ->
parse_and_build_module_in_borrowed_scope). rt_string_len == -1 means the
text slot is not a valid string object at encode time (dead handle), not
merely an empty string.

Fix-shape consequence: whatever owns the decode-hit module's texts must
match the miss path's ownership before the module is handed to HIR/MIR —
either own/promote them inside build_module_from_flat_pool_blob, or
re-acquire them after the HIR re-parse reset. Encoder-side probes
(91c2a192363 family) still needed to name the exact dead pool element
before the binding fix lands.

## Identification 2026-10-23 (lane A): panic pool fingerprinted

enc_pool_head probe (8396828489 / 9b3968dd8a1) trace, repro4:

```
enc_pool_head n=5  item1='private'      \
enc_pool_head n=56 item1=''              | same 11-pool tail in BOTH
enc_pool_head n=56 item1='ok'            | dump passes (parent AND
enc_pool_head n=10 item1=''             / child each panic once)
flat pool encoder append failed site=text.value item=1 input_length=-1  (x2)
enc_pool_head n=5 item1='1' / '' / 'tag_text' / 'private' ...
```

- The panic pool is a 2-element text pool whose item0 is valid and
  item1 is the dangling handle (its enc_pool_head was skipped because the
  head probe itself measured item1 len=-1).
- Sibling pool contents ('private', 'tag_text', 'ok', 56-element pools)
  are lexer/parser token pools of runtime-lib sources (tag_text appears in
  src/lib/nogc_sync_mut/imap/build.spl et al.), placing the fingerprint in
  the delegated frontend's parse-state region of the dump tail
  (parser_state/extend/pending sections) — consistent with the
  delegate-child locus.
- Both passes encode identical pool tails, then both die on the same
  element: the dangling handle survives from the decode-era module state
  into the post-HIR-reparse capture.

Fix shapes recorded for implementation: (A) sanitize-and-refuse-capture —
validate text handles at capture time and abort the cache store (blob="",
treated as a miss) instead of rt_panic, preserving the codec's
"lossy restore must miss, never crash" contract; (B) name-and-fix-owner —
tag pool vars at the ~40 dump call sites and repair the scope/lifetime
owner of the identified pool. (A) unblocks stage2 immediately; (B) is the
proper cure and needs the owner lane's runtime context.

## Annotation 2026-10-23 (lane D, x86_64-pc-windows-msvc, lane 44 @ 32c50742629): panic -> graceful refusal -> AV; refusing pool unnamed

Lane 44 = first full-jobs gate run over the landed ownership fixes
(1b8136dd6ce decl-pool promote, b326b1b93f8 extend/pending-pool promote,
70424d1ec9c scope-memo promote, ff1f69fd931 publish-deadlock fix). Gate red
(exit 2) but the failure SHAPE CHANGED, which localizes the remaining defect:

- The encoder panic is GONE. flat_pool_builder_push now refuses gracefully:
  `[flat-pool] capture refused: invalid text handle site=text.value item=0
  input_length=-1; cache store skipped` (flat_pool_codec.spl:495-499).
- The invalid text handle at site=text.value item=0 STILL EXISTS, in the same
  window: decode-hit (frontend-cache hits=1) -> hir-entry re-parse
  (reset_all_pools n=2 per the pooldbg counter) -> the RE-PARSE's capture dump
  hits a text pool whose elements are ALL rt_string_len == -1 (probe printed
  item 0..4 len=-1 for the refusing pool; neighbouring pools in the same dump
  are the same size n=5 with all-empty or all-valid elements).
- Consequence chain: refused capture -> mir-shard worker exits ->
  0xC0000005 access violation (rc 139) in the fallback path. The AV is a
  SECONDARY defect exposed by the graceful skip (downstream code derefs what
  the skipped/poisoned capture left behind).
- Companion store failures persist on the miss path: frontend-cache store
  "cannot write under <dir> (dir_create_all=true)" and hir-cache
  "store failed at write ... reason=io-write" even to a private cache dir.

Discrimination value: on the miss path the SAME capture dump is clean (all
elements valid/empty) — only the decode-hit path produces the all-(-1) pool.
So the refusing pool is one that (i) flat_pools_restore_all populated at
decode, (ii) the hir-entry re-parse's reset does NOT clear, (iii) the fresh
re-parse does NOT repopulate, and (iv) the capture dump encodes. It is NOT one
of the pools the landed promotes cover. Next probe: print the refusing pool's
DUMP POSITION (text-pool ordinal within flat_pools_dump_all) — the fixed
section order names it without runtime introspection; or print pool identity
at the enc_pool_head site.

Repro (9 s, deterministic, candidate preserved at
.simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/simple.exe.rejected):
the standard p2_add native-build repro with SIMPLE_POOLDBG=1; full trace with
per-element lens preserved at the lane's stage2-sanity frontend-failure log.

## Annotation 2026-10-23 (lane D, lane 45 probe candidate @ c85b6b5de55 + probes): refusing pool located to dump_all's tail; unified mechanism hypothesis

Probe candidate (pooldbg VALUE prints + storedbg) repro discriminated further:

- The crash dump is `flat_pools_dump_all`'s TAIL: the refusing pool is one of
  the last text pools of the whole dump (extend/pending section), immediately
  after the final parser_state pool (the n=2 LOG001 warning pool, which is a
  useful landmark). On the hit path its 5 elements are all dead (-1); the
  pools dumped before it are clean. On the miss path the same-ordinal pool is
  n=5 all-empty.
- The n=5 size on BOTH paths for tail pools that p2_add (no enums, no
  @unsafe, no extends) would leave EMPTY strongly suggests these pools carry
  STALE content from a previously-parsed module in the same worker, not from
  p2_add's own parse.

Unified mechanism hypothesis (fits every observation including the lane-44
monomorphize-phase second crash):
1. `_fab_capture_pools` (module_assembly.spl:1388) is armed only by
   frontend.spl:162 and managed_parse_group.spl:146; flat_pool_capture_take
   disarms. SOME path leaves it armed across a later
   parse_and_build_module_with_scope_owner, whose capture dump
   (module_assembly.spl:1584-1609) then dumps pools that do not belong to the
   module just parsed.
2. On the decode-hit path the hir-phase re-parse reaches the dump with pools
   still holding decode-restored elements whose strings died at the hir-entry
   reset/scope boundary -> all-(-1) -> sanitize refusal -> poisoned capture
   -> downstream 0xC0000005 AV.
3. The io-write store failures are a SEPARATE defect (storedbg probe queued):
   cache-ON-only, candidate-internal, dir_create_all succeeds, manual writes
   to the same dir succeed; failure is inside file_write_exact (codec,
   encode, or tagged-native write - the probe splits these).

Next probe (one candidate): trace events for arm/take/dump with caller tags
(print at flat_pool_capture_arm/take and at the module_assembly.spl:1584 dump
gate: "armed-by" module path + which parse_and_build entry
scoped|borrowed|reference_checked + cache hit/miss). That names the arming
path and settles whether the dump belongs to the parsed module. The proper
cure then is one of: (a) bind the capture to the parse that produced it (dump
only pools the just-finished parse populated; skip dump when this call did
not run parse_module_body), or (b) extend the promote coverage to the
identified tail pools. (a) is preferred: re-caching a cache-hit module is
wasted work even when the pools are valid.

## Annotation 2026-10-23 (lane D, lane 46 capture-trace candidate): TWO distinct defects separated

SIMPLE_CAPTURE_TRACE=1 + SIMPLE_POOLDBG=1 repro on the lane-46 candidate
(preserved at .simple/storage/build/bootstrap/stage2/x86_64-pc-windows-msvc/
simple.exe.rejected) prints arm/take/dump-gate per parse. Sequence per process:

```
arm
dump-gate p2_add armed=1 stream=false borrowed=true  -> dump_all path
take bytes=4582                                    <- VALID blob (borrowed path works)
arm
dump-gate p2_add armed=1 stream=false borrowed=false -> dump_for_cache path
take bytes=-1                                      <- INVALID BLOB (rt_string_len -1!)
arm
dump-gate p2_add armed=1 stream=false borrowed=false -> dump_for_cache path
[flat-pool] capture refused site=text.value item=0 (pools dead at this gate)
take bytes=0
```

Defects separated:
A. The UNSCOPED capture path (module_assembly.spl:1619-1622 else-branch ->
   flat_pools_dump_for_cache) can produce a blob whose OWN handle is invalid
   (take reads len=-1) even with NO sanitize refusal in that dump - the
   serialization-scope wrap (dump_for_cache:1289-1302: begin scope, dump,
   pause, promote, end) loses the blob. The borrowed/transient path
   (dump_all direct) is clean (4582 bytes). An unscoped caller that actually
   consumed that -1 blob would crash or store garbage.
B. A later dump gate sees dead pools (the original all-(-1) refusal) - stale
   or scope-killed pool elements at an unscoped gate after the hir-entry
   boundary, matching the armed-capture hypothesis from the lane-45 note.

Next actions: (1) name the unscoped caller(s) (extend the dump-gate print
with a caller tag or a stack probe); (2) fix A by either making
flat_pools_dump_for_cache return an owned blob verified by rt_string_len >= 0
(retry without the serialization scope, or promote via a checked copy) or
skipping unscoped captures; (3) fix B by binding the dump to the parse that
populated the pools (skip when this call did not run parse_module_body).
Repro: the 9 s p2_add repro with SIMPLE_CAPTURE_TRACE=1.

## Annotation 2026-10-23 (lane D, lane 48b): root cause family identified - transient-scope reclaim of live-referenced strings (heisenbug)

With fix A (unscoped capture -> dump_all) plus a blob-built len print, the
capture trace shows:
- dump#1 borrowed: blob-built 4582, take 4582 (valid).
- dump#2 unscoped: blob-built 4582, take 4582 (valid - take=-1 GONE).
- dump#3 unscoped: sanitize refusal mid-dump -> poisoned -> take 0 (correct).

The take=-1 disappearance is HEISENBUG: the only delta from lane 47c (which
showed take=-1 with the identical fix A and no read) is the blob-built eprint
reading _fab_captured_blob.len() between assignment and take. An intervening
read/allocation changes scope-reclaim timing and keeps the blob alive. The
blob's bytes are a joined string independent of the pools; its HANDLE dies,
so a scope reclaim between build and take frees live memory.

Pool values at the refusing gate (lane 48b): the dump begins with six n=5
pools whose contents match p2_add's own desugared if/and chain
([0,1,2,3,"4,5,6,9"] = arm/body payload indices), i.e. they ARE this parse's
pools; the 6th pool's five elements are dead handles whose strings were
reclaimed between population (parse_module_body) and the dump, in the same
call. Conclusion: the runtime transient-scope/GC reclaim frees strings that
remain referenced from live pool arrays (arrays' element slots not honored as
roots, or scoped arrays reclaimed despite external references). This is the
runtime class-layout/scope-scanning family; compiler-side copies or read-
keeping are timing workarounds, not cures.

Owner-lane next actions: (1) runtime: audit transient-scope reclaim root
scanning for array-element text slots (decl/extend/pending pools) and string
payload promotion (rt_transient_heap_promote must copy payload, not just the
header - lane-46 dump_for_cache take=-1 shows header-only promotion);
(2) compiler mitigation until then: bind the capture dump to its parse (skip
when this call did not run parse_module_body) to stop dumping reclaimed
pools; (3) the io-write store failures are lane-env-specific (stage2-home
sandbox) and lower priority.

## Annotation 2026-10-23 (lane D, lane 49): capture dedup real but incomplete - refusing arm is another site

The per-process capture dedup (frontend_parse_or_restore skips arm/take for an
already-captured path) landed and is correct, but the stage2 sanity still
refuses: the crash dump is armed by a DIFFERENT call path. In the crash block
the frontend cache HITs (worker shared cache), so the worker's refusing dump
is not the frontend.spl miss path - it is the worker's own first parse+store
cycle (its store fails with the lane-env io-write defect, so its hir re-parse
misses again and arms), or the managed_parse_group arm
(managed_parse_group.spl:146), which the dedup does not cover.

Next cycle: (1) caller-tag both arm sites (flat_pool_capture_arm gains a tag
argument: frontend-miss | managed-group) and one lane to name the refusing
armer exactly; (2) extend the per-process dedup to ALL arm sites (keyed by
path, shared _fab_captured_paths) so a path is captured at most once per
process no matter which subsystem parses it; (3) the store io-write defect
(lane-env, stage2-home sandbox) remains the reason the worker re-parses at
all - fixing it collapses most repeat-capture traffic.

## Annotation 2026-10-23 (lane D, lane 50g): dedup verified - exposure reduced 3x, runtime reclaim confirmed as the cure

Lane 50g (all-sites capture dedup, #4229) sanity ran 587 s with ZERO refusals
through the early phase (previous lanes crashed within ~200 s), then 4
refusals deep in the sanity. The dedup eliminated the repeat-capture crash
cycles exactly as designed; the remaining refusals are FIRST captures in
fresh worker processes (dedup is per-process) hitting the transient-scope
reclaim heisenbug nondeterministically. This is the expected signature of
the doc-#4228 diagnosis: compiler-side mitigation reduces exposure; only the
runtime scope-stamp reclaim / promote-payload fix removes it. The stashed
caller-tag arm trace (work/release-tip-20261023 stash "caller-tag-trace")
names any remaining armer in one lane if the owner wants it.

## Annotation 2026-10-24 (lane D, lanes 52-54): containment exhausted - runtime mid-scope reclaim of globals-referenced strings is the sole cure

Lane 52 fixed the companion defects: hir-cache stores now succeed
(stores=1 io_failed=0, first time in 15+ lanes) and the miss path is fully
clean. The caller-tagged capture trace (lane-52/54 candidates) named the last
refusing armer: tag=frontend-miss in the DELEGATED WORKER's first p2_add
parse. Fixes landed and verified in-lane: (1) the loading-path parse streams
(driver_source_pipeline_loading:176), (2) the hir bootstrap_entry reparse
streams (driver_hir_pipeline_lowering:1916). Lane 54's trace confirms both
took effect - the worker's refusing dump-gate now prints stream=true -
yet the refusal PERSISTS at the same pool/site/item.

Conclusion: the pool strings die DURING the parse, inside the parse's own
transient scope, before the dump and before any scope end or promote. The
only mechanism left is the runtime's allocation-triggered transient reclaim
freeing strings that are referenced exclusively from module-global pool
arrays (the scope GC roots the stack, not the globals - matching the
lane-48b heisenbug where one extra allocation flipped survival). This is not
compiler-fixable: containment (dedup, dump_all, blob promote, streaming at
every identified site) is now complete and the crash persists.

Owner-lane cure (runtime, src/runtime/runtime_native.c): the transient
scope's reclaim/GC must treat module-global array slots as roots (or the
decl/expr/stmt/extend/pending pool arrays must be registered as root
owners), so scope-referenced strings survive until promote/scope-end.
Repro: the 9 s p2_add repro on any lane-52+ candidate; the refusal fires
deterministically in the delegated worker regardless of scope mode.

## Annotation 2026-10-24 (lane D, runtime lead): string reclaim ignores scope_id

Reading rt_core_reclaim_transient_immortal (src/runtime/runtime_native.c:2274)
with the lane-54 evidence (stream=true gates still refuse): the STRING branch
computes reclaim solely from the object's flags -
  reclaim_string = (reserved & RT_CORE_STRING_FLAG_TRANSIENT) != 0 &&
                   (reserved & RT_CORE_STRING_FLAG_SHARED) == 0;
- and the scope_id check (`*object_scope != scope_id`) applies ONLY to
arrays/dicts/enums/closures/floats. A string is therefore reclaimed by ANY
scope end, including a scope that did not create it, whenever its TRANSIENT
flag is still set (i.e. it was never promoted). Transient scopes cannot nest
(begin() returns 0 while one is active), so within a single parse no other
scope end runs - but the worker's dump reads pool strings whose TRANSIENT
flag survived from an EARLIER scope in the same process (an earlier module's
parse, or the driver's scope that handed off the decode), and any subsequent
scope end frees them regardless of ownership.

Owner-lane fix candidates (runtime): (a) stamp strings with their creating
scope id and check it in the reclaim loop (mirror the array branch); or
(b) clear RT_CORE_STRING_FLAG_TRANSIENT at allocation time for strings that
outlive their creating scope via registry transfer. Verify with the 9 s
p2_add repro: the delegated worker's first frontend-miss dump must stop
refusing with stream=true gates.

## Annotation 2026-10-24 (lane D, lane 55): pool-family promotes succeed; refusal persists - runtime-only

Lane 55 restored the lost blob promote AND added parser/decl/extend/pending +
type pool-family promotes to the parse scope (the full promote-reachability
gap). Result: NO "pool promote incomplete" warnings (all promotes succeeded),
yet the delegated worker's capture refuses identically. The promote-
reachability hypothesis is refuted as the cause; with dedup + dump_all +
blob promote + streaming + pool promotes all in place, the dead pool handles
can only come from the runtime reclaim itself (scope-GC / string-flag
interaction documented above). The parse-scope promote coverage is kept: it
is correct hardening and removes one entire death class, but the gate cure
is the runtime reclaim fix alone.

## Annotation 2026-10-24 (lane D, ABI finding): reserved has no free bits - the scope stamp needs a struct field

RtCoreString.reserved (runtime_native.c:1445) is fully allocated: bit 0 =
RT_CORE_STRING_FLAG_SHARED (deliberately overlaps the cp-count field, see the
rt_string_char_code_at note at :3934), bits [29:0] = cp-count, plus
RT_CORE_STRING_FLAG_TRANSIENT (bit 1) and SIMD_CACHE_FLAG_IS_ASCII. There is
NO spare bit field for a creating-scope id, so cure candidate (a) cannot be a
bit-pack; it requires adding `uint32_t transient_scope_id` to RtCoreString
(safe within one build - the runtime is compiled into the seed and the
candidates together, no cross-version ABI - but it shifts data[] and touches
the hottest struct in the runtime). Candidate (b) (per-scope tracked-object
lists instead of the single global rt_core_transient_heap_scope_objects) is
the layout-preserving alternative. Both are owner-lane runtime changes; the
compiler side remains fully contained as of lane 55.

## Annotation 2026-10-24 (lane D, lane 56): scope-correct reclaim REFUTED as the sole cure

Implemented the per-entry scope-stamp reclaim (parallel side-table, compaction,
layout-preserving - work/scope-correct-reclaim-20261024) and verified in a full
lane with the rebuilt Rust seed: the refusal is unchanged. The cross-scope
reclaim-free theory is refuted. Combined with lanes 54-55 (refusals inside a
single scope, pool promotes succeeding), the dead pool arrays/strings die with
NO reclaim running - the remaining mechanisms are heap corruption (a buffer
overwrite in the codec/restore path clobbering the pool array backing or string
headers) or never-valid slots (i64 tags written into text slots at decode).
Both require runtime heap debugging (guard instrumentation at the refusal
site) - owner-lane work with runtime tooling. The scope-correct reclaim branch
is preserved on origin for the owner: it fixes a real cross-scope ownership
defect per code reading, but it is not the stage2 gate cure. All compiler-side
hypotheses (14 PRs) and the two reclaim hypotheses are now tested and refuted
or fixed; the blocker needs heap-level diagnosis.

## Annotation 2026-10-24 (lane D, empirical narrowing): candidate codegen defect, differential seed-vs-candidate

Build-free findings this cycle:
- The stored frontend-cache blob is VALID: the would-be-refusing pool (6th text pool
  of the tail, ordinal established in lanes 45/48b) is 5 EMPTY strings in the blob
  (/tmp/p2blob repro, blob lines 43-48); neighboring content pools are intact.
- The reader path is source-clean end to end: FlatPoolReader.next returns empty
  lines as ""; flat_pool_unescape("") returns ""; dec_text/dec_text_into push
  through clear+push with no uninitialized slots.
- The seed (bin/simple.exe) runs the exact split probe
  ("5\n\n\n\n\n".split("\n") + per-field len) CORRECTLY - all empty fields len=0.
  So rt_string_split / rt_string_new(0) in runtime_native.c are correct.
- The stage2 CANDIDATE cannot compile the same probe: full probe AVs
  (0xC0000005); the minimal "a\n\nb".split("\n") probe fails HIR aggregation.
  The seed and the candidate diverge on this exact construct class.

Conclusion: the -1 pool elements on the decode-hit path are the candidate's
miscompiled read of valid blob data - a stage2 candidate CODEGEN defect in the
text-split / text-array / empty-field handling family, not heap corruption and
not a runtime C bug. The seed-vs-candidate differential probe
(build/scratch/splitprobe.spl pattern, run via any bootstrap_admission fixture
temporarily) reproduces it in ~25 s. This is owner-lane codegen debugging with
a now-minimal reproducer; the fixture was restored clean after probing.

## Correction 2026-10-24 (lane D): probe conclusions retracted - refusal is entry- and construct-independent

Control experiments invalidated the previous annotation's codegen claim:
- The ORIGINAL hello_world.spl AVs under the same non-delegated invocation as
  the split probes - the probe AVs were the NON-DELEGATED path crashing on ANY
  entry (a separate second defect), not split miscompilation.
- With the full delegated env, split probes (with and without empty fields)
  fail with the SAME capture refused as p2_add - the refusal is entry- and
  construct-INDEPENDENT. Any admitted entry + delegated env + warm cache
  (second build = frontend-cache hit) reproduces the -1 refusal.
What stands from the prior narrowing: the stored blob is valid (empty pools
intact), the reader path is source-clean, and the seed runs the split-empty
probe correctly. The defect is the candidate-compiled DECODE read of blob
empty-field slots producing -1 handles - module-independent, hit-path-only.
Minimal repro: build any bootstrap_admission entry twice with the delegated
env; the second (cache-hit) build refuses at site=text.value item=0.

## Addendum 2026-10-24 (lane D): seed-AOT differential blocked by pre-existing seed defects

Attempted to complete the JIT-vs-AOT differential seed-side by seed-native-building
the split probe: blocked twice by pre-existing seed issues, not this bug -
(1) the seed's own native-build entry jit-fails on "Cannot infer field type:
struct 'TextSpan' field 'end'" in src/app/cli/native_build_main.spl (JIT
fallback to interpreter), then (2) SCV-E-ADMISSION derived-composition-identity-
mismatch on the ad-hoc entry. So the seed-JIT-correct / candidate-AOT-broken
differential stands but cannot be cheaply closed seed-side; the owner can
complete it after the TextSpan/SCV seed nits, or debug the candidate-AOT
decode read directly (candidate + the minimal warm-cache-hit repro above).

Crash pattern (lane B log, 4 events): the SIGBUS site MOVES with each
generation -- gen0 claimed=212 near lib.common.json.tokenizer /
lib.common.ui.action; gen1 claimed=2 near app.ui.render.capability /
gpu.engine2d.backend; gen2 claimed=84 near compiler.common.native_output_intent
/ compiler.backend.feature_caps_types; gen3 claimed=24. No single
reproducible module: consistent with accumulating heap corruption (the
crash address follows allocation state, not a fixed bad access). HIR
progress is monotonic regardless (1877+/2934 after 4 crashes) because the
hir-cache stores each completed module before the next crash.

## Restoration 2026-10-24 (lane D): rebase-dropped evidence restored

The release-branch rebase onto release-phase3 dropped three lane-D addenda
from this document. They are decision records for the active bisection; the
full original text survives in the history of work/bisect-probe2-20261024.
Restored in compact form:

1. Lane 58 split-field probe: all 160 blob.split("\n") fields of the p2_add
   frontend-cache blob are VALID (10 len=0 empties, 146 len=1, 2 len=26,
   2 len=7; ZERO len=-1) and the capture refusal still fires. blob.split, the
   reader, and empty-field handling are innocent; the -1 handles are created
   between flat_pools_restore_all's write and the capture dump's read, ~100
   source lines apart, no pool reset, no scope end. Also: fixture-probing
   pollutes build/scv's snapshot index (snapshot-index-drift); clear and
   rebuild to recover.
2. Debugger prevention: five cdb approaches all produced ZERO refusals
   (allocation-order-sensitive defect; debug-thread injection perturbs the
   heap enough to prevent it), while 160 extra prints still reproduced.
   Close-path = debugger-free print-bisection, ~2-3 lane cycles. cdb facts:
   refusal literal VA 0x14163caec; attach to the SECOND simple.exe (worker ==
   parent binary; ~2 s lifetime).
3. Lane 59 bisect probe 1: sanitized dump immediately after parse_module_body
   shows parses 1-2 CLEAN (4582 bytes), parses 3-4 POISONED (4588/4352) in the
   same worker process; refusal and AV follow. Kill is INSIDE
   parse_module_body, heap-context-dependent, building across repeated parses.

## Annotation 2026-10-24 (lane D, lane 60 bisect probe 2): poisoned BEFORE decl-0's parse

Probe-2 candidate (in-parser dumps at decl-loop i==1 and i==3, env
SIMPLE_BISECT2=1; committed on work/bisect-probe2-20261024) on the 30 s
warm-cache repro (verbatim, four parses of p2_add):

    parse 1: [bisect2] after-decl i=1 bytes=820 poisoned=false
             [bisect2] after-decl i=3 bytes=1348 poisoned=false
             [bisect]  post-parse bytes=4582 poisoned=false
    parse 2: (identical, all false)
    parse 3: [bisect2] after-decl i=1 bytes=823 poisoned=true
             [bisect2] after-decl i=3 bytes=1346 poisoned=true
             [bisect]  post-parse bytes=4349 poisoned=true
    parse 4: (identical to parse 3, post-parse 4351)
    refusals: 8, RC=139

Interpretation: the decl loop increments i, probes at the TOP of iteration
i==1, and only then parses decl 0 (tag_bool). parse_module_body's own
prologue between entry and the loop is inert (var declarations only). So on
parse 3 the pool arrays are ALREADY poisoned before the first declaration is
parsed: the corruptor acts in the inter-parse window (post-parse-2 dump was
CLEAN), in the hit-path restore, or in the caller tail between restore and
the loop. The bisect moves out of the parser body to the restore/inter-parse
boundary. Deterministic shape: parses 1-2 always clean, 3-4 always poisoned.

## Coordination 2026-10-24 (lane D): branch move + worktree lanes

Lane D's work moved to work/bootstrap-tip-v2, based on the rebased
origin/release/1.0 (per owner directive). Probe 3 (lane 61, branch
work/bisect-probe3-20261024) instruments four env-gated (SIMPLE_BISECT3) dump
sites with a per-process sequence counter: A = miss-path entry before
reset_all_pools (inherited pools), B = immediately after parse_module_body,
C = after the transient-scope pause (promote boundary), D = hit-path
immediately after flat_pools_restore_all. Result matrix: A poisoned ->
inter-parse teardown; D poisoned -> restore write; A/D clean, B poisoned ->
parse fill; all clean until refusal -> caller-tail/frame corruption.

Lane-environment note: the shared checkout D:/dev/simple now carries a live
parallel agent's uncommitted restructure, and the stage3 authority guard
(scripts/check/lib/bootstrap-stage3/authority.shs:5220) requires a fully
clean tree incl. submodules (gitlink-dirty abort). All lane-D lanes therefore
run in isolated clean worktrees off the pushed work branches; the shared
checkout is left untouched for the parallel agent.
## Lane B convergence update 2026-10-24 (afternoon): crash-after-store rhythm

Eleven SIGBUS restarts in, the lane's behavior stabilized into a productive
rhythm: each coordinator life completes one giant module and stores it to the
hir-cache BEFORE crashing -- so completed giants never re-process.
engine2d.backend, engine2d.framebuffer, and engine2d.virtio_gpu all completed
this way; HIR reached 2377+/2934 (81%) with monotonic progress. The SIGBUS
still fires at ~6-7 GB RSS shortly after each giant's store, consistent with
the accumulating-corruption model: the fault follows total allocation volume,
not a specific module. Net: the wrapper-restart + hir-cache design converts
the admitted candidate's heap-corruption crashes from blocking to
slowdown-only. Cure remains the owner lane's runtime reclaim work.


## Annotation 2026-10-24 (lane D, lane 61 probe 3 + crash catch): frontend exonerated as WRITER; deterministic HIR-worker AV caught

Probe-3 candidate (four env-gated dump sites: A=miss-path entry, B=post-parse,
C=post-scope-pause, D=hit-postrestore; branch work/bisect-probe3-20261024) on
the 30 s repro, TWO consecutive runs, identical shape:

    [bisect3] seq=1 site=A-entry   bytes=460  poisoned=false   (driver parse)
    [bisect3] seq=2 site=B-postparse bytes=4589 poisoned=false
    [bisect3] seq=3 site=C-postpause bytes=4589 poisoned=false
    [bisect3] seq=1 site=D-postrestore bytes=4589 poisoned=false (hit restore)
    [hir-shard] owner=0/1@0 status=CRASH exit=-1073741819 claimed=1 sealed=1
    RC=1, refusals=0

Facts established:
1. The frontend writes the pools CLEAN at every measured boundary (entry,
   post-parse, post-pause, post-restore) in the configuration that crashes.
   The frontend/restore path is exonerated as the corrupting writer; the
   refusal observed in other configurations is the sanitize fallback reading
   corruption whose origin is elsewhere (HIR/MIR phase or inter-phase).
2. PERTURBATION LAW (heap-allocation-order sensitivity, quantified across
   three candidates): the 2-dump candidate refuses at parse 3/4 in the
   frontend; the 4-dump candidate keeps the frontend fully clean and crashes
   deterministically (2/2) in the HIR worker; the unprobed build refuses in
   the frontend AND crashes the MIR shard (rc=139). Every measurement moves
   the surface; the corruptor has never been directly observed.
3. SCRIPTED cdb CATCH of the deterministic crash (SIMPLE_BISECT3=1; the
   debugger does NOT prevent this manifestation): full register + disasm in
   /tmp/p2cdb/cdb.log of the lane-D session, summary:
     rip=simple_exe+0x16c37f  mov rax,[r14]  with r14=0 (AV read of NULL)
     r14 = return of call simple_exe+0x125796d(ecx=edi, rdx=0); loop scans
     r15=0xa3 (163) entries (inc rbx / cmp r15,rbx), per entry:
     unmask [entry] (~7), read [header+38h], call simple_exe+0x12abfb7(rcx=that,
     edx=3), test/jne-exit. X(0) returned 0 on the FIRST iteration and the
     result is dereferenced unchecked. Post-seal, delegated HIR worker.
   This is a nil-lookup-result dereference in a bounded table scan in the HIR
   worker - hardening candidate for the gate blocker.
4. The BASELINE manifestation (no BISECT3) is debugger-prevented: 240 s under
   cdb -o produced no AV (consistent with the lane-58 debugger finding).
5. WER never fires for these worker crashes: no Event 1000/1001 despite valid
   HKCU LocalDumps keys for simple.exe.rejected (WerSvc stopped is not the
   cause; kernel GPU watchdog events at 9:03 were unrelated). Crash capture
   requires scripted cdb with a MULTI-g command file - cdb -o consumes one
   command per child attach-break (git spawns at candidate startup), so a
   single -c "g" exits on stdin EOF (the doc's 'session exits early').
6. The stage2 gate's actual blocker (lane 61 verdict): candidate_frontend_smoke
   p2_add-build raw rc=139 = the worker AV; the capture refusal is the
   graceful fallback, not the blocker.

Next: (a) lane 62 gate-check on lane B's stage2-fixes + mir-mem-fixes-r10
base; (b) source-level identification of the 0x16c37f scan loop for a nil
guard; (c) if the r10 base still crashes, cdb-catch on it and diff the site.
