# Typed collection region discovery

Authored companion to
`test/01_unit/compiler/semantics/collection_plan_extractor_spec.spl`.
The tests build resolved typed HIR and call production logical-plan extraction;
they do not compile or execute a substituted plan.

Authored source-cardinality cases additionally require Exact(0)/Exact(3) for
typed empty/nonempty literals through real chain extraction. Variable, call,
ArrayRepeat, fixed-length variable, untyped and non-array-typed inputs retain
Unknown. An effectful element still gives one slot conditional on successful
construction; every independent effect/cost/allocation/rewrite proof stays
unknown or false. These tests were committed before implementation, unexecuted.

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
| User-produced collection source | Outer map/filter is extracted; the whole source call remains opaque. |
| Unresolved typed source call | Only the resolved outer operation is admitted; source effects remain unknown. |
| Untyped opaque source | Extraction fails instead of inventing a source type. |
| Opaque call between admitted regions | Exactly two independent regions; neither assigns authority to the user call. |
| Chain bound with opaque source | 128 admitted operations accepted; 129 rejected. The source is not charged as an admitted operation. |

Analysis uses the existing typed diagnostic scan plus an iterative region scan.
Successful receiver chains are pruned while their source and call arguments
remain visited. Extraction is bounded by the existing 128-call chain limit.
Facts do not confer callback, alias, memory, profitability or rewrite proofs.
An unregistered receiver call terminates an already admitted chain. This does
not classify that source call as a collection operation or execute it twice.
All scenarios remain authored but unexecuted.
