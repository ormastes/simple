# Windows server launch projection V1

Executable source: `test/01_unit/lib/container/server_windows_launch_projection_v1_spec.spl`.
Requirements: REQ-002, REQ-005. Qualification: **source-only NOT_RUN**.
This manual describes authored assertions, without native or interpreter results.

| Scenario | Assertions |
| --- | --- |
| Immutable binding | Windows retained bytes contain the selected public discovery environment; provider request digest matches execution plan; endpoint changes alter both request and plan digests; unsigned input remains unchanged. |
| Actual Docker command | The provider's create command receives the exact administrator-pinned network ID and direct `--env` snapshot, scope and empty config-path arguments. |
| Network refusal | `none` returns an explicit discovery network error; a different network ID fails provider policy validation. |
| Invalid discovery | Loopback, inline credential bytes, competing config paths and case-aliased Windows reserved environment are rejected before signing. |

Production constructor:
`src/lib/nogc_async_mut/container/server_windows_launch_projection_v1.spl`.
It depends on Windows provider workload environment V5 and pinned-network V6
request support. Native creation must independently observe and admit the
administrator-configured NAT network and the exact resulting attachment.
The typed constructor does not create, delete or authorize a network.

The owner convenience API additionally routes the completed request through
`simple_container_project_v2` to verify scope, provider policy and digest
against the tagged owner. A signed envelope is never modified. No host private
key store, home directory or runtime socket is exposed. DNS, connectivity and
credential availability remain live qualification requirements.
