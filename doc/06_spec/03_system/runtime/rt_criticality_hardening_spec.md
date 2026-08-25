# RT Criticality Hardening — Operator Manual

Executable: `test/03_system/runtime/rt_criticality_hardening_spec.spl`  
Status: **not executed in this lane**; hand-maintained mirror.

## Workflow

1. **enforce RT criticality** — require exactly one migration warning using `W-RT-PROFILE-001`, then exactly one enforcement error using `E-RT-PROFILE-001` for the same implicit declaration.
2. Admit a direct effect-free transitive closure.
3. Reject a recursive unsafe closure and require stable allocation, recursion, and loader diagnostics (the same mask also covers blocking, dispatch, logging, and synchronization).

## Traceability

| Requirement | Evidence |
|---|---|
| REQ-012 | Stable warning-to-error staging and implicit critical default text |
| REQ-013 | Safe adjacency plus transitive forbidden-effect closure |
| REQ-015 | Concrete positive/negative assertions and stable diagnostics |

