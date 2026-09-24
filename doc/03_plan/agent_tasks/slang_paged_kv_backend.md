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
# Physical-provider activation wave (Astra refinement, 2026-09-09)

1. **Owner lane:** add `model_executor/paged_executor.spl`; connect provider
   handles to `KvPageManager` identities and implement serial
   cold/reuse/decode lifecycle. Keep stable storage contracts in
   `core/page_contract.spl` and mutable transitions in `core/page_manager.spl`.
2. **Backend lane:** add request tokenization/readback helpers without moving
   tensor ownership or scheduling policy out of the owner.
3. **Engine lane:** integrate load, readiness, generation dispatch, fallback,
   resumable unload, and honest activation reasons.
4. **Evidence lane:** extend the system spec and real-provider runner through
   the Simple owner path; add matched snapshot/physical benchmarks.

Shared interfaces are owned by the primary implementation lane. Sidecar lanes:
N/A for the initial patch because owner, engine, and lifecycle state overlap.
Merge owner: primary Codex session. Final reviewer: Astra, followed by GitHub
admin self-review. Merge is prohibited until parity, bounds, cleanup, and
fallback gates pass. SSD tiering begins only after this activation is merged.
