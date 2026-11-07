# Signed preparation through the actual host owner

Status: **NOT_RUN**. Three authored executable scenarios use real Ed25519
signatures, private files and the existing capacity journal. No provider effects
or platform qualification are implied.

Source: `test/03_system/app/orchestrator/feature/host_signed_prepare_spec.spl`.

| Scenario | Expected evidence |
|---|---|
| Exact replay and reopened writer | Identical receipt, no duplicate journal event, capacity charged once |
| Corrupt approval and expiry after signature validation | Exact rejection, no reservation payload directory or capacity mutation |
| Oversized UTF8 and noncanonical packet | Bounded decoder rejects before admission |

Execution logs, compiler identity and branch coverage remain unavailable until
the admitted-runtime verification gate is run.
