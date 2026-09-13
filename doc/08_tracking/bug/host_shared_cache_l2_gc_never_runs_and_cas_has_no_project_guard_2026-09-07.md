# Host-shared cache: bounded L2 GC never runs, and cas_store has no project-namespace guard

- **Date:** 2026-09-07
- **Status:** OPEN — two capabilities are genuinely absent from `main`'s cache tier.
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
