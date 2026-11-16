# Windows Host post-effect projection retention

Status: AUTHORED_NOT_RUN. Manual authored from the executable source; docgen was
not run. Native/bootstrap qualification campaigns remain closed.

Two scenarios in `test/03_system/app/orchestrator/feature/windows_host_retained_projection_v3_spec.spl`:

1. Open the genuine protected Host and inject an inconsistent returned ledger revision.
   The exact native writer and returned projection remain retained, the original
   projection error is returned, readiness becomes false, and native close remains available.
2. Change the returned lease digest while retaining the genuine native store.
   The provenance guard rejects before replacing the canonical owner.

Requires actual Windows, an installed signed protected deployment, empty
reconcilable Docker inventory, and `SIMPLE_WINDOWS_HOST_PRIVATE_PARENT`,
`SIMPLE_WINDOWS_HOST_POLICY_PIN`, `SIMPLE_WINDOWS_HOST_BINDING_FILE`.
Missing prerequisites fail; there is no synthetic Windows owner or skip PASS.
The malformed projection is deliberately injected after genuine owner creation.
Actual settlement commit followed by row-loss/revision fault injection is
NOT_COVERED; no native cleanup, timing or durability qualification is claimed.
