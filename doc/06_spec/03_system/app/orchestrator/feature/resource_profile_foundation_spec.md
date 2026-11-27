# Resource-profile foundation scenarios

Source: `test/03_system/app/orchestrator/feature/resource_profile_foundation_spec.spl`
Requirements: CFG-01, CFG-02, ORCH-01 from the existing orchestrator lane.
Status: **NOT_RUN**. This manual is authored from executable scenarios; it is not
SPipe-generated evidence. No admitted runner is available; the separate native
diagnostic build and its limitations are recorded in the foundation design.

Read `test/fixtures/orchestration/agent_cpu_profile.sdn` directly with
`decode_resource_profile`. Its CPU minimum/recommendation/preference are
1000/2000/4000 millicores; memory minimum/recommendation/preference are 2/4/8 GiB.
Configuration cannot launch work or reserve capacity.

| Scenario | Expected observation |
|---|---|
| Decode the fixture directly | Correct name, namespace, ranges and policy flags |
| Supply only minima | Recommend, prefer and limit inherit preceding values |
| Invert ordered amounts | Reject with the exact resource_order schema path |
| Omit minima or add fields | Reject missing/unknown fields |
| Supply invalid or overflowing quantities | Reject quantity at the affected CPU/memory minimum |
| Use nonboolean policies or GPU sharing fields | Reject type/unknown field |
| Change API version or kind | Reject unsupported envelope identity |
| Offer abundant capacity normally | Select recommendation and equal effective caps |
| Explicitly allow preferences | Select preference, bounded by available capacity |
| Offer less than either minimum | Refuse rather than underallocate |
| Offer exactly minima | Accept; negative capacity remains invalid |
| Raise declared limit | Do not reserve the unused limit |
| Require GPU | Preserve unresolved device intent, grant no device |
| Construct invalid typed CPU or memory ranges | Refuse invalid-resource-range |
| Parse i64 CPU boundary and whole-core scale boundary | Accept exact supported maxima; reject next value before arithmetic |
| Parse byte, Ki, Gi and G memory boundaries | Accept exact supported maxima; reject next value before scaling |
| Decode a nested Deployment with a mismatched selector | Reject with child.spec.template.metadata.labels and positive source coordinates |
| Repeat a nested SDN minimum | Reject duplicate_key with original path and positive source coordinates |

The executable uses real decoded values, allocation comparisons and rejection
oracles. Tests intentionally exclude unified ResourceList loading, host ledger
mutation, assignment authority and TaskRunner acceptance; their owners compose
those independently. Run the focused spec and SPipe manual/maintenance checks
with an admitted self-hosted runner before recording runtime qualification.
