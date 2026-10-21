# Enum continuation edge budget

Requirements: EE-01, EE-CONS-01. Status: authored; execution and documentation generation **UNRUN**.

The fixture parses an actual guarded enum function, lowers it through the target-specific enum producer, and obtains its plan from the actual semantic validator. It precreates checked decision nodes so memoized targets cannot hide missing edge-allocation charges.

| Scenario | Step | Observable oracle |
|---|---|---|
| Exhausted edge budget | Exhaust remaining work after precreating actual checked decision targets | Expansion returns `EE-E-LIMIT`; remaining work, node count, and the empty successor array remain unchanged. |
| Exact sufficient edge budget | Supply one work unit per edge and retain constructor order and typed paths | Expansion consumes exactly the supplied edge budget and preserves each checked target, constructor identity, discriminant, and typed path. |
| Complete guarded graph | Build the complete graph from the producer and validator plan | Shared work decreases, every graph node appears in topological order, and the actual guarded false transfer retains its checked arm and residual target. |

The first two scenarios are source-predicted failures against the frozen consumer revision 1. No executed RED/GREEN or formal proof claim is made.
