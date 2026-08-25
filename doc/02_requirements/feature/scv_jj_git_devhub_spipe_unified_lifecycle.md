# Unified lifecycle feature requirements

**Status:** Selected from the user-provided target architecture on 2026-08-25.

- REQ-001: SCV shall own stable lifecycle identity and exact-revision evidence independently of JJ/Git/provider aliases.
- REQ-002: SJ shall expose typed, policy-checked protected mutation planning and remain observe/dry-run only until promotion gates pass.
- REQ-003: approvals and gates shall bind exact immutable revisions and become stale after relevant source, policy, or evidence changes.
- REQ-004: DevHub shall expose one versioned typed lifecycle/provider interface without flattening unsupported provider semantics.
- REQ-005: remote projection shall use idempotent three-way field-authoritative synchronization with durable conflicts.
- REQ-006: release candidates may be abandoned; published releases/tags shall be immutable and only withdrawn/superseded.
- REQ-007: Features, Tasks, Changes, Revisions, Reviews, Gates, Releases, Documents, and Runs shall remain distinct linked entities.
- REQ-008: machine-readable Spipe policy shall define protected refs, authority, gates, routing, synchronization, and version projections.
- REQ-009: existing SCV/JJ/Git/DevHub/SJ commands shall migrate progressively through compatibility wrappers.
- REQ-010: protected-ref mutation and provider publication shall remain disabled by default in the base implementation.

