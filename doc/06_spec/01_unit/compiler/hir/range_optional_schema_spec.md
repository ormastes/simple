# Optional Range schema consumers

Executable source: `test/01_unit/compiler/hir/range_optional_schema_spec.spl`.

The spec constructs real HIR nodes and exercises generated children and structural hash owners, production monomorphization type substitution, criticality traversal, and effect loop-bound classification.

| Scenario | Real assertion |
|---|---|
| Enumerate present endpoints | Child counts are 0, 1, 1, 2 for all four endpoint topologies. |
| Hash distinct open bounds | Missing endpoints and opposite endpoint positions yield distinct hashes. |
| Preserve absence during substitution | Rewritten HIR retains one endpoint and its structural hash. |
| Traverse absent bounds | Dispatch and allocation checks return false without accessing absent nodes. |
| Fail closed on open end | Loop-bound classification returns NONE rather than a finite-capacity admission. |

Evidence: Phase1 seed diagnostic run executed 5 cases, 5 passed, 0 failed, 0 skipped. This is not self-hosted native qualification.
