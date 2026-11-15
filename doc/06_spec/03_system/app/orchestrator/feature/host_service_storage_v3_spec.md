# Retained Host journal storage and service input boundary

Source: `test/03_system/app/orchestrator/feature/host_service_storage_v3_spec.spl`.
Requirements: HOST-STORE-01, HOST-SERVICE-01.
**AUTHORED_NOT_RUN**. This manual is authored, not generated/docgen-verified.

| Scenario / step | Observation asserted |
|---|---|
| admits bounded relative records and refuses path escapes before storage | Production path guard accepts record names and rejects absolute, traversal, malformed, deep and oversized paths. |
| uses one CLI shape for genuine Linux and Windows installed owners | Production syntax accepts both backend forms and a Windows prepare request. This checks syntax, not installed authority. |
| refuses missing Windows anchors and unsupported effects before opening owners | Missing trust-anchor fields, arbitrary backend and effect action refuse. |
| preserves immutable Linux records on identical and changed publication replay | A real Linux journal publishes once, preserves original bytes, distinguishes absence, then refuses stale writes after close. |
| keeps the legacy WAL parser and compare publication behavior without a Windows store | The actual legacy WAL commits and reads one entry, refuses stale-parent publication, and preserves CURRENT. |

The last two scenarios allocate real temporary filesystem state when executed.
None has been executed in this campaign. Successful Windows Host startup,
authenticated preparation, ACL/locking, native cleanup, provider inventory and
connection consumption are not established by these five scenarios.
