# Process Observation V4 cleanup lifecycle

**Source:** `test/02_integration/lib/io/process_observation_cleanup_v4_spec.spl`

**Status:** design-frozen component contract. Common V4 and the production
facade are integrated. Qualified host fixture authority remains
`MissingEvidence`; fail-fast host helpers must not be replaced by synthetic
data.

The executable is presently a scenario skeleton with zero executed live branch
coverage. Its common receipt, snapshot, and deadline assertions are concrete,
but C01–C25 and the C02/C03/C18/C19/C23 live slice remain planned until
qualified host fixtures are available.

## Visible flow

Each primary scenario uses: prepare a pinned request; trigger startup cleanup;
observe retained cleanup authority; collect the cleanup snapshot; acknowledge
the exact snapshot.

## Assertions

- CleanupPending retains its phase and live ticket through repeated observations.
- CleanupFrozen is ProviderFailed, fully bound, and replay-identical.
- Wrong digest/kind/duplicate acknowledgement does not deactivate ownership.
- Exec failure origin, retained bytes, counters, and deadlines remain unchanged.
- Physical host execution is explicitly MissingEvidence.

Sol reviews helper/API fidelity and RED fail-fast behavior. Astra reviews C01–C25
coverage, separate branch reports, ownership negatives, and host evidence
admission.
