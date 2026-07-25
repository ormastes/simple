# Engine2D Four-Backend Capture System Test Plan

| Requirement | Evidence |
|---|---|
| REQ-E2D4-001 | Same scene ID and dimensions in all five records |
| REQ-E2D4-002 | GPU device readback or SIMD execution counters |
| REQ-E2D4-003 | Exact six-event ordered target receipt |
| REQ-E2D4-004 | Durable capture path, SHA-256, bounds, revision |
| REQ-E2D4-005 | Pairwise and aggregate comparison report |
| REQ-E2D4-006 | Negative validation scenarios |

The pure contract spec runs first. Each live target then runs once. A failed
target may be fixed and rerun no more than twice. The final comparison consumes
only evidence created from the integrated revision.
