# Windows Docker process-only request admission

Status: NOT_RUN. Authored manual mirror of
`test/03_system/app/orchestrator/feature/windows_docker_process_contract_spec.spl`.
Admitted SPipe/docgen/sspec-maintain execution remains outstanding; this is not a
generated pass report. Fixtures are synthetic and never start Docker.

Requirements: REQ-WDP-001, REQ-WDP-002, REQ-WDP-003, REQ-WDP-005, REQ-WDP-006.

| Scenario | Reader action | Expected assertion |
|---|---|---|
| Explicit compatibility tuple | Supply selected host kernel and image OS-version strings. | Values are individually retained; their differing formats are accepted without a compatibility claim. |
| Engine route | Replace local named pipe with a remote daemon or resolve Docker through PATH. | Policy refuses the endpoint or executable. |
| Identity and bounds | Omit engine identity, use generation zero, infinite timeout or excess output. | Policy refuses execution. |
| Immutable image | Supply tag-only or shortened digest. | Request refuses mutable/partial identity. |
| Resource policy | Ask for NAT, zero CPUs or undersized memory. | Request refuses unsupported network/limits. |
| Entrypoint bounds | Omit the command or supply NUL. | Request refuses unsafe data before execution. |
| Typed arguments | Use a spaced executable, spaces, shell-looking text and an empty argument. | Exact argv elements remain separate; process isolation and ContainerUser are explicit. |
| Request binding | Change argument boundaries, CPU allocation or engine identity. | Canonical semantic digest changes. |
| Native identity | Supply a full lowercase ID, prefix, name or flag. | Only the full native ID is admitted. |

The tests compare concrete errors, fields, digest differences and argument indices.
They do not prove Windows API quoting, resource enforcement, engine availability,
image compatibility, actual process isolation, or ordinary-client authorization.

The SDN scenarios additionally round-trip quoted/newline/empty arguments, reject
duplicate/unknown/missing/typed fields, reject modified digests and schema versions,
require canonical serialization, and refuse a record bound to another engine policy.
Policy is trusted local input and never decoded from request payload bytes.
