# Counterpart: the matrix engine hardcodes `ConversionLoss.identity`, so the exactness gate is unreachable end to end

- **Date:** 2026-08-09
- **Lane:** F9 (foundation red-team), Counterpart Conformance Wave 1
- Status: FIXED
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Severity:** High. The Exactness acceptance gate is enforced in the relation
  engine but can never fire from the real entry point.

## The defect

`src/lib/nogc_sync_mut/spec/evidence/counterpart/matrix_compare.spl:177-178`:

```
val input = matrix_relation_input(comparison, left, right,
    ConversionLoss.identity)
```

`matrix_build()` — the only path from a `CounterpartPlan` to a set of comparison
cells, and the path `evaluate_matrix()` uses — passes a literal
`ConversionLoss.identity` as the route loss for **every** cell. It never
consults `ConverterRegistry` / `resolve_route()`; `matrix_compare.spl` does not
import `converter_graph` at all.

## Consequence

`relation_precondition_failures()`
(`src/lib/nogc_sync_mut/spec/evidence/counterpart/relation_engine.spl:252-256`)
correctly refuses an exact relation reached through a lossy route — but only
when someone hands it a non-identity `route_loss`. Through `evaluate_matrix()`
that is impossible: `conversion_loss_rank(identity) == 0`, which is `<=` every
relation's permitted rank, so the clause is dead code on the production path.

The same hardcoding also means `ComparisonCell.route_loss` — which
`relation_projected_facts()` publishes as
`counterpart.<relation>.route_loss=identity` into CanonicalEvidence — is a
constant, not a measurement. A manual generated from a real run will claim every
comparison was loss-free regardless of the converters actually traversed. That
additionally defeats the design's "Conversion: every route and loss class
recorded" gate (§16).

The unit-level exactness probes that are already green (relation engine,
converter graph) are both genuine, but neither exercises the seam between them,
so the composite defect sits precisely in the gap between two passing lanes.

## Why no RED spec accompanies this record

Asserting the correct behaviour requires `matrix_build()` to accept a registry
or a per-comparison route, which is an API change owned by the matrix lane, not
by F9. Writing a spec against an API that does not exist would not compile.
`test/02_integration/infra/counterpart/foundation_redteam_spec.spl` therefore
covers the exactness rule at the `resolve_route()` level only, and this record
carries the seam.

## Unblock condition

`matrix_build()` / `evaluate_matrix()` take a `ConverterRegistry`, resolve a
route per comparison via `resolve_route()`, propagate the resolved
`route.loss`, and turn a `RouteResolution` with `resolved == false` into a
failing cell plus a rejection. Then add to the red-team suite a scenario where a
plan requests `byte_exact` over a pair whose only registered route is
`semantic_projection`, and assert `evaluate_matrix` rejects it — it must fail
before that change and pass after.

## Resolution (2026-08-09, lane F5/F6)

The diagnosis was correct and the unblock condition was implemented as written,
in `src/lib/nogc_sync_mut/spec/evidence/counterpart/matrix_compare.spl`:

- `matrix_build_with_registry(plan, results, registry)` and
  `evaluate_matrix_with_registry(plan, results, registry)` are the new
  registry-taking entry points.
- For every comparison the engine now calls `resolve_route()` from
  `source_schema_id(left)` to `source_schema_id(right)` with the comparison's
  own relation, and carries the resolved `route.loss` into the
  `ComparisonCell` — the constant at the old lines 177-178 is gone.
- A `RouteResolution` with `resolved == false` becomes a FAILING cell naming
  the rejection code and detail, which in turn becomes a run rejection. An
  undeclared conversion is therefore a refusal, never an implicit identity.
- `matrix_build()` / `evaluate_matrix()` remain as two-argument
  back-compatible wrappers over an EMPTY registry. This is not a re-hardcode:
  sources already sharing a canonical schema resolve to a *measured* identity
  route, and sources at differing schemas now resolve to `no_route` and fail.

The Exactness gate is consequently live on the production path: with only a
`semantic_projection` edge registered between the two schemas, a `byte_exact`
comparison is refused by the matrix itself with
`exact_relation_through_lossy_route`, before the relation engine is reached.

**New scenarios** (in the F5/F6 unit spec
`test/01_unit/infra/counterpart/relation_matrix_spec.spl`, describe block
"Counterpart matrix measures the converter route it traversed"):
measured `semantic_projection` loss on the cell; measured `identity` loss for
same-schema sources; exact-relation refusal across a lossy route; and refusal
when no converter is declared at all.

**Verification.**
`test/01_unit/infra/counterpart/relation_matrix_spec.spl`
→ `declared>=19 executed=19 passed=19 failed=0 dropped=0`, exit 0.
`test/02_integration/infra/counterpart/foundation_redteam_spec.spl`
→ `declared>=21 executed=21 passed=21 failed=0 dropped=0`, exit 0 — the
red-team suite still passes unchanged against the new API, since its sources
share one canonical schema and now resolve a measured identity route.

**Sabotage probes**, each broken → RED → reverted → GREEN:

| guard | sabotaged | restored |
|---|---|---|
| carry the measured `route.loss` (re-hardcode `ConversionLoss.identity`) | 19 exec / 18 pass / **1 fail** | 19/19/0 |
| turn an unresolved route into a failing cell | 19 exec / 17 pass / **2 fail** | 19/19/0 |
