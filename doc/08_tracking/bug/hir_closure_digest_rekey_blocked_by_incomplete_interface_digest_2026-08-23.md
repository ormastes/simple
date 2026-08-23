# HIR closure digest re-key BLOCKED: textual interface digest under-captures struct fields

**Date:** 2026-08-23
**Status:** OPEN — re-key deliberately NOT performed
**Area:** compiler / 80.driver / cache
**Severity:** perf (0% incremental HIR cache hit rate) — blocked on a correctness gap

## The waste

`hir_cache_closure_digest` (`src/compiler/80.driver/driver_hir_cache.spl:84`)
folds every surface's raw file `content_hash`. A single comment or function-body
edit anywhere in the closure therefore invalidates **all 687 HIR cache entries**.
The incremental hit rate is **0% by construction** on a phase costing ~60 minutes;
the cache only pays for byte-identical repeat builds. Source:
`doc/09_report/cache_effectiveness_audit_2026-08-23.md` (`de7c994627e`).

## Proposed fix and why it is NOT applied

Re-key the closure digest onto `interface_digest_of_source`
(`src/compiler/80.driver/cache/action_key.spl`), so only INTERFACE changes
invalidate dependents. That is only safe if the extractor is COMPLETE with
respect to downstream-visible surface. **An under-capture becomes a stale cache
HIT — a silently wrong compiler binary.** Over-capture merely over-invalidates
and is safe.

A differential spec was written first —
`test/01_unit/compiler/driver/interface_digest_differential_spec.spl` — one
interface-only edit and one paired body/comment-only edit per construct. It ran
**RED at 6 of 12** on the pre-fix extractor.

| construct | interface edit changes digest? | verdict |
|---|---|---|
| `extend` decl (retarget, methods identical) | was NO | **fixed** — `extend ` header now captured |
| re-export alias (`use m.{a as b}` + `export b`) | was NO | **fixed** — `use ` lines now captured (over-invalidates on a plain import edit; safe direction) |
| `impl` block (implementing type change) | YES | already covered |
| trait default method (signature change) | YES | already covered; default-body edit correctly does not change it |
| **struct/class FIELD retype or addition** | **NO** | **BLOCKING — not fixable in a line-prefix extractor** |

## The blocker

Fields are arbitrary indented `name: Type` lines. A line-prefix extractor cannot
separate them from body statements, match arms, dict literals or named
arguments; capturing all such lines would over-capture so aggressively that the
digest approaches the content hash and the win evaporates, and it would still
not be a *proof* of completeness against the full grammar. Field layout
(offsets, size) is directly downstream-visible, so this gap is exactly the
stale-hit class.

Per the correctness-before-speed rule, the closure digest was **left keyed on
`content_hash`**. An unfixed 0% cache is vastly better than a stale hit producing
a wrong compiler.

## Unblock path

The semantic replacement already exists and already covers fields:
`src/compiler/35.semantics/interface/compile_interface.spl`
(`simple/compile-interface/v1`, encodes `FieldSignature`), but it is
compute-and-log only and needs typed HIR / `ApiSurface`, not raw source. The
re-key becomes available once that digest is wired as the closure key. Note it
still lacks generic arity+constraints, effects, parameter passing modes and
public constants — each must be added, with a differential row here, before it
can gate a cache.

Related, out of scope here: `dep_iface_gate_*`, `needs_recompile` and
`smf_manifest_entry_verifies` have zero external callers, and nothing traverses
`src/lib/simple.sdn` `dependencies:` — no dependency-aware rebuild exists at all.
The re-key does not depend on that wiring and does not make it worth doing until
the digest is complete.

## Guard

Row `interface-digest-differential` in `scripts/check/check-perf-regression-tests.shs`
pins the spec, so a future re-key cannot land while the field gap is open.
