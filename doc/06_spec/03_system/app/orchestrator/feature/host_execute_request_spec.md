# Host execute request scenarios

Source: `test/03_system/app/orchestrator/feature/host_execute_request_spec.spl`.
Status: **NOT_RUN**. Authored manual; not SPipe-generated evidence.
No admitted SSpec, native diagnostic or live-provider result is claimed.

Envelope-only shape and integrity checks use opaque canonical SDN and zero-signature fixtures. These are deliberately not provider requests or valid signed authorization. The host must independently decode the actual provider request, recompute its semantic digest and verify action-specific signed grants and approval before effects.

The executable scenarios assert these behaviors:

1. Round trips exact envelope bytes without claiming signed authorization.
2. Rejects intent operation and receipt tampering.
3. Requires full scope and matching host boot provider and service identity.
4. Binds the canonical launch plan digest to the reservation.
5. Rejects unknown duplicate noncanonical and tampered wire fields.
6. Bounds opaque canonical request syntax without trusting semantic digest fields.
7. Rejects malformed signature shapes without treating valid lengths as authentication.
8. Enforces request and envelope limits in UTF8 bytes.

No result here implies a callable controller service, host mutation, authenticated
receipt provenance, provider execution or TaskRunner parent acceptance. These are
necessary dependencies for the actual signed dispatch composition. Runtime and
manual-generation checks remain pending an admitted runner and authorized build.
