# Slang physical paged-KV implementation tasks

Date: 2026-09-08.

| Lane | Owner | Deliverable |
|---|---|---|
| Architecture and SDK review | Astra | Provider boundary, hazards, nonclaims |
| Contract values | Root | Page/pool/request identities and execution namespace |
| Reference page manager | Root | Bounded tables, refs, COW, transactions, telemetry |
| Native provider | Root | Real tensor pages or pinned backend extension |
| S3 compatibility | Root | Atomic capability fallback and differential path |
| Verification | Root | Fault fixture, sanitizers, numerical and memory evidence |
| Lower-model sidecars | N/A | Shared ownership files require one merge owner |

Merge owner and final reviewer: root, with Astra reviewing any change to page
semantics or claims. Implement contract values and a deterministic reference page
manager first. Do not advertise S4 until a physical provider and parity/memory
evidence pass.
