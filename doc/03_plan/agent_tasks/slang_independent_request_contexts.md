# Slang independent request-context implementation tasks

Date: 2026-09-08.

| Lane | Owner | Deliverable |
|---|---|---|
| Architecture review | Astra | Ownership, ABI, lifecycle, and non-claims |
| Runtime implementation | Root | Native request table, handles, leases, teardown |
| Simple integration | Root | Optional ABI group and request lifecycle API |
| Verification | Root | Fixtures, ASan, real-header build, admission gates |
| Additional sidecars | N/A | Shared runtime files require one merge owner |

Merge owner and final reviewer: root. Runtime and Simple integration remain
serial patches so no two agents edit the same ownership boundary.
