# Cache v2 / interface-compat first milestone — known gaps NOT fixed

**Date:** 2026-08-10
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 00).
**Landed work:** commits for C1 (tier router), C3 (GC/leases), A3 (CompileInterfaceDigest), C7 (fixtures).
**Plans:** `doc/03_plan/compiler/cache/semantic_incremental_build_v2_plan_2026-08-09.md`,
`doc/03_plan/compiler/build_system/targeted_build_interface_compat_minimal_bootstrap_2026-08-10.md`

These are deliberate first-milestone limitations found during higher-model review of
agent output. None of them is a silent shortcut: each is typed, commented at the call
site, and listed here.

---

## 1. `abi_interface_digest` / `compile_semantic_digest` / `link_export_digest` are placeholder domains

**Where:** `src/compiler/35.semantics/interface/module_identity.spl`

All three fields exist with the right types, but each is the compile-interface part set
re-hashed under a distinct `.../placeholder-v0` domain tag. There is **no real ABI,
layout, CTFE, or link-export analysis** behind them.

**Consequence:** these three digests must NOT be used to make a reuse decision. Only
`compile_interface_digest` and `implementation_digest` carry meaning today.

**Unblock:** ABI needs field offsets/sizes/alignment/enum representation/vtable slot
ordering from the backend layout layer (plan §7.2). Semantic needs macro + CTFE +
AOP-selection roots. Link needs the export table.

## 2. `ApiSurface` lacks generic arity/constraints, effects, and param passing modes

**Where:** `src/compiler/90.tools/api_surface.spl` is the input to A3's extractor.

The frozen interface spec (plan §7.2) requires generic arity + constraints, effects and
capabilities, and parameter passing modes in `CompileInterfaceDigest`. `ApiSurface` does
not carry them, so they are absent from the digest.

**Consequence:** a change to a generic bound or a declared effect may NOT change the
compile interface digest — an **under-invalidation** risk. This is why A3's output stays
compute-and-log and is wired into no build decision.

**Unblock:** a typed-HIR interface extractor that reads the semantic layer directly
rather than the ApiSurface summary. Blocks the plan's Wave 2 (`.sreq` per-consumer
requirements) from being sound.

## 3. `normalize_module_source` comment-stripping is not string-literal aware — FIXED 2026-08-10

**Where:** `src/compiler/35.semantics/interface/module_identity.spl` (not
`compile_interface.spl` — that was a stale reference in the original filing;
`normalize_module_source` and the new `strip_trailing_comment` helper live in
`module_identity.spl`).

**Was:** a `#` inside a text literal was treated as a comment start when
normalizing source for `implementation_digest` (naive `index_of("#")` +
`substring`), so two genuinely different modules could normalize to the same
text if they differed only inside a literal containing `#` (e.g.
`"tag#1"` vs `"tag#2"` both truncated to `"tag`, colliding on the same
`implementation_digest` — an under-invalidation risk for reuse decisions built
on that digest).

**Fix:** `strip_trailing_comment` now scans each line char-by-char tracking
`in_string` state (toggled on unescaped `"`, with `\` escape handling inside
the literal) and only cuts at `#` when not inside a string literal. Still
line-based (does not track multi-line/triple-quoted literals spanning lines —
same scope limit as before; not addressed by this fix).

**Evidence:** `test/01_unit/compiler/interface_compat/compile_interface_spec.spl`,
new case `"hash inside a string literal is not treated as a comment start (no
false collision)"` — two sources differing only after `#` inside a string
literal now produce distinct `implementation_digest`s. Sabotage-verified: with
the old naive `index_of("#")`+`substring` stripping restored, this case fails
(`8 total, 7 passed, 1 failed`, `✗ hash inside a string literal...`); with the
fix, `8 total, 8 passed, 0 failed`. Full spec file also reconfirmed green
end-to-end after restoring the fix. Verified against `bin/simple` (currently
the Rust seed per its `--version` banner — see gap 7; not separately verified
against the self-hosted binary).

## 4. GC `min_free_ratio` is scoped to the cache budget, not host disk free space

**Where:** `src/compiler/80.driver/cache/gc/admission.spl`, `metadata/cache_limits.spl`

Design §18.2 requires a **filesystem** free-space reserve that triggers emergency GC even
when cache-accounted bytes are under `max_bytes`. No `rt_` symbol exposes host free bytes,
so the reserve is currently computed against the cache's own `max_bytes` budget.

**Consequence:** the cache cannot detect that the *disk* is nearly full from a cause
outside the cache. The "never fill the filesystem" goal of §18.1 is only partially met.

**Unblock:** a runtime symbol for host filesystem free bytes (statvfs-equivalent).

## 5. Stale-lease reclaim falls back to a 6h timeout when liveness cannot be proven

**Where:** `src/compiler/80.driver/cache/lease/lease.spl`

Dead-process detection uses `rt_process_exists` where available; otherwise a conservative
6-hour timeout plus generation check.

**Consequence:** on a platform without process-liveness detection, a crashed process's
lease pins its artifacts for up to 6 hours. This is the SAFE direction (false miss, never
dangling hit) but wastes storage.

**Unblock:** portable process-liveness check across Linux/macOS/Windows/SimpleOS.

## 6. AOP and block-level groups remain SPEC-FORWARD

Restated from plan §2b so it is tracked as a gap, not just as planning prose:

- No pointcuts exist — matching is an untyped `WeavingRule.predicate_text` string.
- Weaving mutates MIR in place; there is no per-target weave artifact to cache.
- `BlockId` is a transient integer and must never be serialized into a cache key.
- No dataflow lattice/worklist framework exists to attach block reuse to.

**Unblock:** each is a prerequisite implementation task, listed against Phases 6 and 7 of
the migration sequence.

## 7. All verification used the Rust seed binary

Every spec verdict cited in the landed commits was produced by `bin/simple`, which is
currently the **Rust seed** (its own `--version` banner says so). The pure-Simple
self-hosted binary was not separately verified for any of this work.

**Consequence:** GREEN here does not prove self-hosted correctness. Per
`.claude/rules/bootstrap.md` the self-hosted binary is the default tooling target.

**Unblock:** re-run the cache_v2 and interface_compat specs under
`bin/release/<triple>/simple` once a bootstrap deploys.

## Re-verification 2026-08-17 (fleet lane C, by CONTENT)

STILL-OPEN and correctly labelled; the only correction is PATH DRIFT in the triage row.
Both named files exist:
- `src/compiler/80.driver/cache/gc/admission.spl` (112 lines) — present
- `src/compiler/80.driver/cache/lease/lease.spl` — present (triage looked for it at
  `cache/gc/lease.spl`, which does not exist)

Neither file carries a `TODO`/`stub`/`not implemented` marker, so the unfinished GC-admission
and lease work is not flagged in source — the gap list lives only in this doc. That is itself
worth fixing: an unmarked gap is invisible to every scan. Recommend adding TODO markers at the
specific unimplemented call sites so the backlog is greppable.

No patch attempted: this is scoped, deliberately-deferred milestone work, not a defect.
