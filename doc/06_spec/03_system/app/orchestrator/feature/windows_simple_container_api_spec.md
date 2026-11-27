# Windows through the shared Simple Container API

Status: authored NOT_RUN. This manual mirrors the source spec; it is not a
runtime or generated-doc qualification claim.

The scenarios invoke the actual shared `simple_container_observe_v2` and
`simple_container_open_v2` factories. They reject unsupported Hyper-V selection,
malformed Windows policy and an attempt to use service continuity through the
finite strong-boot factory. Policy codec negatives cover duplicate, unknown,
wrongly typed and noncanonical records. Scoped command assertions verify that
physical host, service and service-incarnation labels are explicit, while actual
native boot remains empty and the internal opaque fence occupies its own label.

These assertions do not exercise Docker or authorize service restart adoption.
Successful Windows lifecycle acceptance requires the persistent shared service
owner, its startup inventory quarantine/reconciliation and the Windows fixture.
The service nonce is never substituted for a native boot observation.
