# Historical Windows HCS contract compatibility

Status: NOT_RUN; authored mirror of the source unit spec, not generated evidence.

The spec retains historical pair/isolation predicates and exact intent-builder
argv assertions. Provider metadata now advertises no live logs or recovery.
Probe/capability and valid lifecycle admission remain blocked with
`windows-hcs-superseded-use-docker-process-provider`; a copied scripted probe plus
`live_source=true` cannot establish delegated authority. Invalid requests still
fail their original validation before the superseded-provider gate.

Canonical execution is owned by the Docker process provider. Historical helpers
are not runtime evidence, and their preserved compatibility table is not reused
by the new provider's exact selected host/image observation policy.
