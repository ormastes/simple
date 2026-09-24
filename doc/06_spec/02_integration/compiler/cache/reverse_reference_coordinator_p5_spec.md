# Reverse-reference coordinator P5 — incomplete draft

- Executable: `test/02_integration/compiler/cache/reverse_reference_coordinator_p5_spec.spl`
- Requirements: `REQ-CSM-016`, `REQ-CSM-017`, `REQ-CSM-023`, `REQ-CSM-024`
- Evidence class: executable SSpec definition; no execution receipt is embedded.

## Mutation-history counterexample

Genesis RR seeding is a separate operation. Every post-genesis mutation must
present a complete old forward-read manifest. `nil` is refused even when the
consumer has no old edges; a complete manifest with zero ordered reads is the
explicit authenticated-empty shape. Refusal preserves the entire prior shard
set, while an explicit empty history can add the first edge.

## Scenario inventory

- old/new membership union and zero-match witness shape;
- canonical CAS persistence and typed readback;
- failed reevaluation and nil/stale history refusal;
- aggregate preflight bounds;
- typed absent-object miss; and
- corrupt persisted-object refusal.

Frozen visible flow: pin one coherent generation; apply one scoped semantic
mutation; recompute the authenticated affected closure; publish or refuse one
coherent generation; verify exact reuse and confined consumer IO. This draft
covers only RR replacement/refusal components.

The same executable also covers canonical CAS persistence, fingerprint
replacement, reevaluation refusal, stale removals, aggregate bounds, typed
misses, and corrupt-object rejection. Runtime execution remains unqualified
until an admitted self-hosted full CLI and the frozen common-contract closure
are available.

This is an incomplete hand-authored draft, not generated-manual qualification.
