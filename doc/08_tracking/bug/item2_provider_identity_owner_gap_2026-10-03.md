# REQ-017 provider identity enforcement is absent from effect admission

Status: OPEN; source-derived defect, runtime reproduction UNEXECUTED.

The selected requirement demands capability-declared observation identity,
idempotent identical input and quarantine of changed bytes under the same
identity. Current Reference and Paged observation owners enforce signatures,
typed reproduction bindings and content availability, but do not call
`db_observation_admit` or maintain an equivalent provider-identity index.
`AppendObservation` identifies rows by EntityRef. A new observation UID can
therefore avoid the existing-row collision while retaining the same provider
tuple and changing its failure signature. This is distinct from accepted batch
replay or an actor-counter collision.

Reproduction source: `test/02_integration/app/scv_db_provider_identity_gap_it_spec.spl`.
It admits actual signed bindings, signs an authorized second patch against the
current base with a new row UID, proves provider identity equality, and expects
the existing pure-contract `QuarantinedIdentityReuse` error before semantic or
retention mutation. This is an intended failing regression, not a recorded RED.
It does not substitute rejection for the required durable quarantine record.

An additional gap is that the codec derives declared dimension names from the
incoming dimensions themselves. There is no independently pinned provider
capability declaration at this admission boundary. A producer must not be able
to change identity scope by altering its own dimension list.

Completion requires an authoritative capability revision, indexed identity
lookup on the captured generation, exact duplicate handling across import
batches, changed-byte quarantine preserving original signed input, and atomic
publication/recovery on both backends. The index and quarantine must participate
in checkpoint validation/preservation and settlement; a local preflight scan or
an independent side file would leave race and bypass paths. Genuine reruns with
distinct attempts must remain distinct. All three REQ-017 system placeholders
remain fail-fast until their complete durable oracles exist.

Pure-kernel progress: 910eb15de9f adds pinned policy/claim/decision helpers and
f694bb9c6c6 adds eleven unit sources. This does not resolve the defect: neither
Reference nor Paged admission invokes an atomic provider index/quarantine owner.
The actual-owner regression remains expected-failing; all runtime tests are
UNEXECUTED. Keep this issue open through full effect and migration verification.
