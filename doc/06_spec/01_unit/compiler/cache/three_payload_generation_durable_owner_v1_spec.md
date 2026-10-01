# Three-payload durable generation owner V1 — incomplete draft

- Executable: `test/01_unit/compiler/cache/three_payload_generation_durable_owner_v1_spec.spl`
- Requirements: `REQ-CSM-003`, `REQ-CSM-007`, `REQ-CSM-008`, `REQ-CSM-012`, `REQ-CSM-024`
- Evidence class: executable SSpec definition; no execution receipt is embedded.

The owner validates and retains a coherent generation packet before switching
its active projection. The critical outcome scenario resolves cancellation and
lost acknowledgment after CAS from recovered durable state. A later publisher
may supersede the candidate; resolution then reports the later active
generation while preserving the candidate's committed identity. A known CAS
conflict reports attempt-local refusal and the competing durable active root,
never the losing attempt's pinned generation.

## Scenario inventory

- one guard across blob, journal, checkpoint, and active projection;
- recovery before and after durable stages;
- pin changes and precommit revocation;
- cancellation, acknowledgment loss, conflict, supersession, and unknown outcome;
- nondeterministic action and corrupt retained packet refusal; and
- uncheckpointed, duplicate, and oversized recovery inventories.

Frozen visible flow: pin one coherent generation; apply one scoped semantic
mutation; recompute the authenticated affected closure; publish or refuse one
coherent generation; verify exact reuse and confined consumer IO. This draft
covers only the publication/refusal portion.

This is a Pure-Simple owner/model boundary. The host commit-scope availability
gate remains false, and no host durability or runtime execution is claimed.

This is an incomplete hand-authored draft, not generated-manual qualification.
