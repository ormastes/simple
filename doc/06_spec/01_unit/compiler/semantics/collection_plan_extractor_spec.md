# Typed collection region discovery

Authored companion to
`test/01_unit/compiler/semantics/collection_plan_extractor_spec.spl`.
The tests build resolved typed HIR and call production logical-plan extraction;
they do not compile or execute a substituted plan.

The original extraction cases cover node ordering, unresolved/absent metadata,
receiver and arity mismatch, chain bounds, and callback-derived distinct key
types. The module-analysis increment adds six scenarios:

| Scenario | Oracle |
|---|---|
| Maximal map/filter chain | One three-node plan; no duplicate suffix plan. |
| Unregistered outer method | Only the admitted inner map is discovered. |
| Missing result type | No plan; blocker identifies function and source line. |
| Argument-owned region | Both the outer chain and nested argument region survive traversal. |
| Invalid registry | No admitted regions and one explicit registry blocker. |
| Empty registry | No invented operations or plans. |

Analysis uses the existing typed diagnostic scan plus an iterative region scan.
Successful receiver chains are pruned while their source and call arguments
remain visited. Extraction is bounded by the existing 128-call chain limit.
Facts do not confer callback, alias, memory, profitability or rewrite proofs.
All scenarios remain authored but unexecuted.
