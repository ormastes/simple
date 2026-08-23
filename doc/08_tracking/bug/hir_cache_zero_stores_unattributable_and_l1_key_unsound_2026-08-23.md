# HIR cache: zero stores were unattributable, and the briefed L1 key is unsound as written

**Date:** 2026-08-23
**Status:** L2 FIXED (receipt landed, proven). L1 BLOCKED — see §3.
**Lane:** phase1 build duration, brief L2 then L1
(`doc/03_plan/compiler/bootstrap/phase1_build_duration_plan_2026-08-23.md`)

## 1. What was actually wrong (L2)

The brief recorded the HIR cache as "structurally incapable of hitting, and
stores nothing at all": no `hir/` directory in `native_cache/run21|run23/`, and
no `[hir-cache]` line ever emitted.

The store path was in fact wired correctly at both call sites
(`driver_hir_pipeline_lowering.spl:361` streaming, `:822` non-streaming). The
real defect was that the cache **could not be observed**, in two ways that
compound:

1. `hir_cache_store` returned a bare `false` for three different causes — the
   codec refusing the module (`hir_module_encode` -> `""`), the temp write
   failing, and the rename failing. None was counted, none was named. The
   design note "a module the codec refuses is simply not stored: a cache that
   cannot store is a slow build, not a wrong one" is right about correctness
   and wrong about observability: it makes total refusal indistinguishable from
   total success.
2. The receipt was printed only `if hir_cache_enabled()`. A cache that was OFF
   and a cache that was ON and stored nothing therefore produced the *same*
   evidence — no line at all. An absent line was read as "the cache stored
   nothing"; it equally meant "the cache never ran".

**Fix.** Refusals and I/O failures are counted separately, the most recent
refusal is named via the already-existing `hir_module_encode_reason`, and the
receipt is printed unconditionally — stating `disabled reason=...` when off.
`SIMPLE_HIR_CACHE=0` is the kill switch and is now pinned by test.

## 2. The premise did not survive measurement

Measured on a private 3-module closure (`SIMPLE_CACHE_SCOPE=hc1`, seed
native-build, `--threads 1`):

| run | receipt | wall |
|---|---|---|
| cold | `[hir-cache] hits=0 misses=3 stores=3 refused=0 io_failed=0` | 212.19s |
| warm | `[hir-cache] hits=3 misses=0 stores=0 refused=0 io_failed=0` | 115.34s |

Output was **byte-identical** across cold and warm
(`sha256 cbfa0304428aa31cf05dc578ca7e6f0d12ba793c154a0160aa938878b44b51a4`).

So the cache stores, hits, and is output-neutral on a real closure with the
code as it stood. The two "no `hir/` directory" observations are better
explained by sampling: `stage1-clean24/build/bootstrap/native_cache/run23/`
was measured at `frontend=138` entries of 688 — that build was still in the
PARSE phase and had not reached HIR lowering at all. `default/` in the same
tree has `frontend=1, hir=1`, i.e. a completed small build did store.

Codec refusal is also unlikely to be a mass cause: `reject()` has exactly two
sites (`hir_codec_support.spl:113,134`) — an optional parser `Expr` inside a
HIR type, and `CustomBlock` with a non-text `BlockValue` — both reachable only
from single generated encoder sites (`generated/hir_codec.spl:5729,2370`) and
only for non-nil payloads.

This does not mean the phase-1 HIR cost is imaginary; it means the *reason* was
never established. The receipt is the instrument that settles it on the next
688-module run, without anyone having to `ls` a cache directory mid-build.

## 3. Why L1 (per-module interface-digest key) is BLOCKED, not merely unfinished

The brief asks to replace the whole-closure surface digest with a per-module
interface digest, wiring `interface_digest_of` and `simple.sdn` traversal. The
standing constraint is that a key change must be **strictly more precise**.
As written, L1 would be strictly **less** precise, and would silently
miscompile.

HIR lowering's observable inputs are not confined to a module's import closure:

- `build_surface_decl_index` (`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl:365-384`)
  builds `surface_decl_owners` by looping over **every** frozen surface and
  indexing the names of its classes, structs, enums, traits, type aliases and
  constants. `surface_decl_owner_indices(name)` (`:387`) is then queried by
  NAME during lowering.
- Re-export materialization walks package siblings that are not import edges.

So an edit to a **non-imported sibling** that adds a same-named declaration
changes what a module lowers to, while leaving that module's import-closure
interface digest untouched. A per-import-closure key would serve a stale entry
for exactly that edit. The existing comment in `driver_hir_cache.spl` already
states this; measurement confirms the mechanism is live, not hypothetical.

**Precondition for L1, in order:**
1. Bound or eliminate the whole-closure `surface_decl_owners` dependency — make
   name resolution during lowering consult only the import closure plus a
   declared, digestible sibling set.
2. Only then is a per-module key sound, and it must fold that sibling set's
   digest alongside `interface_digest_of` of the import closure.

Shipping L1 before step 1 trades a slow build for a wrong compiler. It was not
done here for that reason.

## 4. Landed

- `src/compiler/80.driver/driver_hir_cache.spl` — refusal / I/O-failure
  counters, `hir_cache_last_refusal`, `hir_cache_status_line`, richer summary.
- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl` — receipt printed
  unconditionally at both phase ends.
- `test/01_unit/compiler/driver/hir_cache_store_roundtrip_spec.spl` — 4/4 pass.
  Fails pre-fix by construction: none of `hir_cache_status_line`,
  `hir_cache_store_refusals`, `hir_cache_store_io_failures` or
  `hir_cache_last_refusal` exists at `origin/main` (verified: 0 occurrences in
  `git show origin/main:src/compiler/80.driver/driver_hir_cache.spl`).

## 5. Neighbour sweep

Caches carrying hit/miss/store counters: `frontend_parse_cache.spl` (healthy,
`hits=688 misses=0`), `driver_source_pipeline_parsing.spl`,
`incremental_builder.spl`, `99.loader/smf_cache.spl` (x2),
`70.backend/build_native.spl`, `99.loader/loader/jit_instantiator.spl`,
`99.loader/module_resolver/resolution.spl`, `90.tools/duplicate_check/*`.
None was audited for the same "silent refusal" shape here; the HIR cache was
the one with a measured cost attached. `smf_cache` and `incremental_builder`
are the two most likely to repeat the pattern and should get the same
unconditional-receipt treatment before anyone reasons about their hit rates.

## 6. Handover

The §3 argument is the load-bearing input to a follow-on lane taking the
incremental-build work forward: phase-by-phase checkpointing first, then a
soundness study of the `build_surface_decl_index` cross-surface dependency
BEFORE any per-file keying. The concrete question that study must answer is
narrow and stated here so it is not re-derived: *can name resolution during HIR
lowering be confined to (import closure + a declared, digestible sibling set),
such that no non-imported surface can change a module's lowered output?* Until
that is answered YES with a mechanism, any per-module HIR cache key is less
precise than the current whole-closure digest and must not ship.
