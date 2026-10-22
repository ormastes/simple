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
