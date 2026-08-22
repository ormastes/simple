# Collection optimizer requires semantic-legality proofs

## Status

Open; canonical dispatch is contained by `PassStatus.Disabled`.

## Evidence

The retained optimizer contains source-shape rewrites that are not authorized
by shared ownership, alias, effect, memory-version, and lifetime facts:

- array concat replacement does not establish COW/value equivalence for the
  receiver and copy-back destination;
- string append replacement recognizes `Ptr(I8)` without proving string
  ownership or allocation/trap/destruction equivalence;
- query reuse relies on operation names instead of resolved
  `OperationSummary` and region memory versions; and
- dead capacity-array deletion and generic index specialization lack effect and
  ABI differential evidence.

The former invariant path also inserted into the natural-loop header rather
than a canonical preheader.

## Containment

`collection_opt` is excluded from effective pipelines. Both public hoisting
compatibility entrypoints return their original blocks, and the provider no
longer claims hoisted-query or scalar-hoisting facts.

## Unblock condition

Rehabilitate each rewrite independently with resolved operation identity,
`PerfFacts` dominance/preheader/region/effect/MemorySSA evidence,
ownership/COW/lifetime/trapping/destruction proof, positive and negative
witnesses, adversarial semantic differentials, and profitability evidence.
Do not re-enable the aggregate pass merely because one pattern is repaired.
