# Host-shared cache: bounded L2 GC never runs, and cas_store has no project-namespace guard

- **Date:** 2026-09-07
- **Status:** SUPERSEDED (2026-11-11, lane rt3) — the cache tier was redesigned
  after this record; both capabilities now exist under the new architecture.
  See the 2026-11-11 addendum at the end.
- **Found while:** repairing the three blockers PR #319 shipped unfinished
  (follow-up PR to `e0fa5ef45e2`).

## What was actually wrong, and what was not

The blocker as handed over read: "`cache_root.spl`, `fast_gc.spl`,
`cache_limits.spl`, `negotiation.spl` now ship with no callers — delete them per
`NEVER add unused code`, and delete `host_shared_cache_gc_lifecycle_spec.spl`
which asserts the reverted wiring."

**Three quarters of that premise is false at `e0fa5ef45e2`, and deleting those
modules would have broken `main`.** Measured, not assumed:

| module | callers |
|---|---|
| `src/compiler/80.driver/cache/cache_root.spl` | 10 — incl. `driver_pipeline_lowering.spl`, `driver_aot_native_output.spl`, `driver_orchestration.spl`, `driver_hir_cache.spl`, `src/app/compiler_entrypoint/admission.spl` |
| `src/lib/common/plugin/negotiation.spl` | 9+ — incl. `src/compiler/90.tools/lint/lint_rule_api.spl`, `src/compiler/99.loader/module_loader_compat.spl`, `src/lib/common/aspect_pack.spl`, `src/lib/nogc_sync_mut/sffi/dynamic_versioned.spl` |
| `src/compiler/80.driver/cache/metadata/cache_limits.spl` | used by `cache/gc/admission.spl` and `cache/gc/fast_gc.spl` |
| `src/compiler/80.driver/cache/gc/fast_gc.spl` | no *production* caller, but imported by `test/01_unit/compiler/cache_v2/gc_spec.spl` (`gc_fast_sweep`, `gc_expire_tmp`, `gc_delete_trash`), which is `main`'s own behavioural GC spec |

All four are therefore **kept**. Note `cache_root.spl` does not delegate to
`std.env.platform.get_cache_location`; `tier_router.spl:46` does. They are two
distinct roots by design (machine-wide cache root vs. the cache-manager tier
root), not the hybridisation the handover feared — but that is worth a second
look if a third root ever appears.

## What IS real

`test/01_unit/compiler/cache/host_shared_cache_gc_lifecycle_spec.spl` (deleted in
this change) was a five-block *text-grep* spec. Three blocks were true. Two
asserted wiring that `main`'s cache tier does not have and, on the evidence of
the #319 conflict resolution, deliberately does not want in that shape:

1. **The bounded L2 GC never runs.** The spec expected
   `tier_router.spl` to contain `gc_run_if_needed(l2, cache_limits_load())`.
   It does not, and no production module calls into `cache/gc/**` at all —
   `fast_gc.spl`'s watermark eviction (`DEFAULT_HIGH_WATERMARK 0.90` /
   `DEFAULT_LOW_WATERMARK 0.75` against a 10 GiB `DEFAULT_MAX_BYTES`) is
   reachable only from tests. The host-shared L2 cache is therefore unbounded in
   practice.

2. **`cas_store.spl` has no project-namespace fail-closed guard.** The spec
   expected `stored_project.trim() != project_namespace`; the string
   `project` does not occur in `cas_store.spl` at all. `tier_router.spl:59`
   calls `cas_open(l2)` without the `if not cas_open(l2)` fail-closed form the
   spec expected.

The spec was deleted rather than repaired because a text-grep spec that asserts
a rejected design is not a requirement — it is a claim that the tree is
something it is not, and it would have to be rewritten from scratch against
whatever design does land. The behavioural coverage of the GC primitives
themselves is unaffected: `test/01_unit/compiler/cache_v2/gc_spec.spl` still
exercises `gc_fast_sweep` / `gc_expire_tmp` / `gc_delete_trash` /
`gc_mark_and_sweep` / `admission_check` directly.

## What has to happen next

Both items need a design decision on `main`'s cache tier, not a re-application of
the #319 wiring:

- Decide where (if anywhere) bounded GC is triggered from on the
  `get_cache_location` / fail-closed-L2 tier, and wire `fast_gc` there — or
  delete `cache/gc/**` and `cache_limits.spl` together with their two specs if
  bounded GC is not wanted at all. Leaving it half-present is the current state
  and is the worst of the three.
- Decide whether the L2 CAS needs a project-namespace guard. If yes, it belongs
  in `cas_store.spl` with a fail-closed `cas_open` contract in `tier_router.spl`.

Neither is a self-contained fix, which is why they are recorded here rather than
attempted blind — no test suite, bootstrap, or cargo build was run in the session
that produced this record.

---

## 2026-11-11 — Lane rt3 triage verdict: SUPERSEDED

This record demanded "a design decision on `main`'s cache tier, not a
re-application of the #319 wiring". That design decision has since been
implemented as a **redesign of the cache GC tier**; the two specific gaps are
now closed under the new architecture (not by wiring `gc_run_if_needed` into
`tier_router` or adding a project string to `cas_store`, which this record
rightly rejected as the #319 shape).

1. **Bounded GC now runs in production.** `src/compiler/80.driver/cache/gc/`
   has grown (`fast_gc`, `mark_sweep`, `admission`, `cache_eviction_plan_v1`,
   `disk_cache_bound_v1`, `reader_pin_gc_guard`,
   `verified_generation_reachability_v1`) and is driven by a production cache
   daemon — `src/app/cache_daemon/main.spl` plus
   `src/compiler/80.driver/cache/daemon/cache_daemon_main.spl`, which imports
   `CacheRetentionLimitsV1` from `cache/metadata/cache_limits.spl`, keeps a
   per-artifact usage ledger, and executes bounded eviction in
   `evict_artifacts()` (`cache_eviction_plan_v1(usage, limits)` → removed
   artifact paths). `tier_router/tier_router.spl` still does not call
   `gc_run_if_needed` itself — bounded GC is daemon-driven now, which is the
   "where is GC triggered from" decision this record asked for.

2. **Namespace isolation for GC now exists.** The CAS store
   (`cas_store.spl::cas_open`) still has no project-string field — that
   specific guard was not added — but namespace-scoped GC isolation is now
   provided at the gateway/authority layer by
   `cache/gateway/cooperative_namespace_gc_begin_authority_v1.spl` (a
   descriptor-bound, host-namespace-issued root-union bridge) together with
   `cooperative_namespace_host_prerequisite_v1`, `semantic_scope_*`, and
   `cache_daemon_host_authority_v1`. This is the "does the L2 CAS need a
   namespace guard" decision, answered with a cooperative-namespace mechanism
   rather than an in-`cas_store` string check.

**Verification (seed-smoke, seed build 46fe8f6b6def):**
- `test/01_unit/compiler/driver/cache_eviction_plan_v1_spec.spl` 8/8 PASS.
- `test/01_unit/compiler/driver/cache_daemon_queue_v1_spec.spl` 8/8 PASS.
- Supporting green coverage also present: `cache_v2/disk_cache_bound_spec`,
  `fast_gc_candidate_order_contract_spec`, `fast_gc_trash_move_roundtrip_spec`,
  and the formal `test/00_formal_verification/compiler/cache_eviction_neutral_bounded_spec.spl`.

**Residual:** the literal `tier_router` `gc_run_if_needed` call and the
in-`cas_store` project guard were deliberately not added; the capabilities are
provided by the newer daemon/gateway/namespace architecture instead.
