# Native object cache invalidates the whole build on scoped compiler changes

- **ID:** `native_object_cache_whole_build_fingerprint_granularity_2026-08-02`
- **Status:** DEFERRED BY POLICY, NOW FENCED (2026-08-08) — audited by
  `pure_parser_close` on 2026-08-02; independently re-confirmed 2026-08-08.
  Not "blocked" in the sense of someone actively working it: it is a
  deliberate design tradeoff per `.claude/rules/bootstrap.md` ("Dependency
  tracing intentionally over-invalidates around AOP/MDSOC weaving, loader
  ABI... Do not narrow this to import edges until the AOP and loader
  contracts expose stable cache keys") and explicitly deferred pending that
  AOP/loader-ABI work in
  `doc/03_plan/compiler/bootstrap/stage3_native_cache_incrementality_2026-08-07.md`
  ("Layer 2"). A regression canary now exists:
  `scripts/check/check-native-object-cache-granularity.shs`.
- **Severity:** High (Stage 3 rebuild amplification)

## Reproduction and measured result

The reported Stage 3 refresh after scoped compiler edits compiled **727** modules
and reused **0** cached objects. Source tracing reproduces the invalidation
decision deterministically:

1. `native_build_compiler_identity()` incorporates a hash of every
   `src/compiler/**/*.spl` file.
2. `driver_native_build_cache_scope()` embeds that identity in the base scope.
3. `driver_native_sources_fingerprint()` hashes the complete loaded source
   closure, and `compile_to_native` adds it as a `sources-*` sub-scope.
4. Per-object `BuildCache.update_entry` records `dependencies: []`.

Therefore one compiler edit selects a new directory before any of the 727
per-source fingerprints can be considered: 0/727 hits is the designed outcome
of the current key structure.

## Why the apparent one-line fix is unsafe

Dropping the compiler or closure aggregate would reuse an unchanged source's
object even when a changed compiler pass changes its generated code, or when an
imported type/interface changes its layout. The cache has neither a canonical
post-lowering MIR hash nor per-module dependency interface hashes on this path.
The existing empty dependency list cannot prove reuse safe.

## Required safe fix

Use a two-level key:

1. stable backend/target/options plus executable producer ABI identity;
2. per module, a canonical MIR fingerprint and ordered direct-dependency
   interface hashes.

Then a private scoped change should produce 726 hits / 1 miss in the reported
727-module fixture, while a producer transformation or public interface change
must invalidate every actually affected module. Until those fingerprints exist,
the measured safe delta remains **0 additional hits**; preserving correctness
requires the coarse refresh.

This audit does not touch HIR aggregate or module-surface files.

## Independent re-verification (2026-08-08)

Re-confirmed from both source reading and a fresh, isolated fixture, as part of
`doc/09_report/infra/aot_lane_regression_fence_audit_2026-08-07.md` row 6.

**Source reading** (`driver_aot_native_output.spl`): `compile_to_native` builds
`cache_scope_root = base_cache_scope_root/sources-{sources_fingerprint}`
(line 266), where `sources_fingerprint = ctx.native_sources_fingerprint` comes
from `driver_native_sources_fingerprint()` (line 101) — one hash over the
concatenated `path|module_name|content_hash` rows of every loaded source in
the closure, not per file. The per-module cache-hit check
(`driver_native_build_filter_scoped_outputs`, called at line 331) requires a
cached object's path to start with the CURRENT `cache_scope_root`; since one
edited file changes the whole-closure hash, `cache_scope_root` changes for
every module in the build, so `all_in_scope` is false everywhere and
`build_cache.remove_entry` fires for every module (lines 331-348) regardless
of whether that module's own `FileFingerprint.content_hash` was still fresh.

**Empirical repro**: 3-module fixture
(`test/fixtures/native_object_cache_granularity/{mod_a,mod_b,main}.spl`),
`env -u SIMPLE_BOOTSTRAP SIMPLE_COMPILER_TRACE=1 SIMPLE_NO_STUB_FALLBACK=1
bin/simple native-build --source <fixture> --entry <fixture>/main.spl
--cache-dir <stable-dir> -o <out>`, receipt read from the driver's own
`[NATIVE] cache: N hits, M misses` trace line. Correction to an earlier draft
of this note: `SIMPLE_NATIVE_INCREMENTAL` / `[native-incremental] N reused /
M rebuilt` DOES exist — but only in the **Rust seed's** native-build pipeline
(`src/compiler_rust/compiler/src/pipeline/native_project`,
`src/compiler_rust/driver/src/cli/native_build.rs`), per
`.claude/rules/bootstrap.md`'s own "Follow-up (not yet done)" note. The
**pure-Simple self-hosted driver** (`bin/simple`, `src/compiler/80.driver`) —
the one this row and this fixture exercise, and the one `.claude/rules/CLAUDE.md`
mandates as default tooling — has no such receipt or per-module reuse path;
its only signal is the `[NATIVE] cache: N hits, M misses` trace line used
above. A same-day plan doc,
`doc/03_plan/compiler/bootstrap/stage3_native_cache_incrementality_2026-08-07.md`,
independently reaches the identical conclusion (calls it "Layer 2") and
states explicitly it is "a documented, deliberate design choice, not a bug,"
citing the same AOP/MDSOC-weaving/loader-ABI over-invalidation rationale in
`.claude/rules/bootstrap.md` lines 80-83. This session's fixture-scale repro
corroborates that doc's reasoning with fresh numbers rather than discovering
something new:

| build | change | receipt |
|---|---|---|
| 1 (cold) | none (first build) | 0 hits, 3 misses (cache populated) |
| 2 (warm, ad hoc single run) | none | 3 hits, 0 misses |
| 2b (warm, scripted rerun minutes later) | none | 0 hits, 3 misses — see caveat below |
| 3 (one file edited) | `mod_b.spl` body changed | **0 hits, 3 misses** |

Editing exactly one of three modules invalidated all three objects —
CONFIRMED, matching the 2026-08-02 audit's 727/0 finding at fixture scale.
Wall-clock for the three sequential builds (`time`, not through a pipe, to
avoid the pipe-truncation trap): cold 82.82s elapsed, warm (build 2) 105.14s,
one-file-edit (build 3) 130.06s. **Warm was NOT faster than cold at this
3-module scale** — cache reuse only skips per-module codegen, and for a
fixture this small the interpreter-driven frontend/compiler-load overhead
(observed via the `src{hash}` computation over ~3,097 compiler source files
every invocation) dominates wall time regardless of cache hits. The
"any one-file edit silently turns every incremental build into an hours-long
cold build" cost claim is inherited from the 2026-08-02 audit's real
727-module/0-hit measurement, not reconfirmed at that scale this session —
this session's contribution is confirming the mechanism still applies
unchanged, not remeasuring the magnitude.

Also observed: in a *second* run of builds 1→2 with no fixture change,
`native_build_compiler_identity()`'s `src{hash}` component (hashing all of
`src/compiler/**/*.spl` on every invocation) differed between the two builds
seconds apart, even though this session made no edits to `src/compiler` —
consistent with concurrent sibling-session activity in this shared checkout
(`git status` showed ~1,590 pending changes under `src/compiler` at the time).
This is a second, coarser invalidation layer on top of the one this row
targets, and it makes the "unchanged rebuild fully reuses" comparison
unreliable as a hard CI assertion in a shared/parallel-agent checkout — noted
as a WARN, not a FAIL, in the new fence script below.

**Not fixed this session.** The 2026-08-02 audit's reasoning still holds and
was not contradicted by anything found today: the existing per-object
`BuildCache` entries carry `dependencies: []`, so there is no cross-module
dependency-interface hash to fall back on — dropping the whole-closure
fingerprint to get per-file granularity would let a module's object be reused
even when an upstream module's public shape changed (a correctness
regression), which is exactly the "apparent one-line fix is unsafe" trap
already documented above. The real fix (per-module canonical MIR fingerprint
+ ordered dependency-interface hashes) is infrastructure that does not exist
yet and is a redesign, not a contained patch — out of scope for a single
session per the audit's own fence-cost estimate ("Medium — needs two builds +
cache timestamp/rebuild-count assertions, not a simple stdout diff").

**Fence added**: `scripts/check/check-native-object-cache-granularity.shs`
(known-open canary — asserts today's 0/3-reuse-after-one-file-edit behaviour
as `KNOWN-OPEN` (exit 0) and, if a one-file edit ever starts reusing objects,
**hard-fails** (nonzero exit, `FAIL (promote-me)`) instead of silently
passing, so a future real fix — or an unsafe regression that starts reusing
objects without the missing dependency-interface hashing — gets a human
looking at it rather than being silently absorbed. Sabotage-verified: fed the
script's own hit-count parser a fabricated `hits > 0` receipt line and
confirmed it flags `fail=1`).

## Final clean-run verification (2026-08-08, last pass this session)

One uncontended, foreground, end-to-end run of the finished script
(`scripts/check/check-native-object-cache-granularity.shs`, after fixing the
scope-dir discriminator to a count comparison instead of a lexical
`sort | tail -1`, which an earlier draft got wrong):

```
PASS — unchanged rebuild fully reused the cache: [NATIVE] cache: 3 hits, 0 misses
KNOWN-OPEN — a one-file edit reused 0/3 objects ('[NATIVE] cache: 0 hits, 3 misses'):
             whole-build fingerprint granularity confirmed still present.
EXIT=0
```

**Verdict: CONFIRMED** — whole-build (whole-loaded-source-closure) fingerprint
granularity, at the `driver_native_sources_fingerprint()` / `cache_scope_root
= .../sources-{fingerprint}` layer (`driver_aot_native_output.spl:101,266`).
An unchanged rebuild reuses 100% of objects (3/3); changing exactly one of
three modules reuses 0% (0/3) — every object rebuilds, not just the changed
module. This is not stale/already-fixed, and it is not unverified: a
trustworthy receipt (the driver's own `[NATIVE] cache: N hits, M misses`
trace line — there is no `[native-incremental]` line for this pure-Simple
driver path, see correction above) was obtained for all three build
variants in this final pass.

**Load caveat**: this repo's host was running other agents' full-stdlib
native-builds concurrently throughout this session (observed via `pgrep`:
separate `native-build` invocations from other session IDs against
`test/fixtures`, `src/lib`, etc.). Wall-clock numbers reported anywhere in
this doc (82.82s / 105.14s / 130.06s) are therefore **upper bounds under
contention, not clean single-tenant timings**, and should not be read as a
precise measurement of the cache's per-build savings — only the **hit/miss
receipt counts** (which reflect cache-directory logic, not scheduler
contention) are treated as reliable evidence for the granularity verdict
above. No further timing measurement was attempted under this load, per
guidance to stop chasing clean timings on a contended host.

