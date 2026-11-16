# Container server launch projection V1

Executable source: `test/01_unit/lib/container/server_launch_projection_v1_spec.spl`.
Requirements: REQ-002, REQ-005. Qualification: **source-only NOT_RUN**.
This manual records authored assertions; it is not generated runtime evidence.

| Scenario | Assertions |
| --- | --- |
| Selected public snapshot | One context/server, deterministic canonical SDN, projected guest host, logical credential/trust references, no local host or private key bytes. |
| Actual OCI environment encoder | Existing LANG preserved; exact three reserved `--env` arguments include SDN snapshot, container scope marker and empty config path to clear image defaults. |
| Immutable request binding | Retained provider bytes decode to injected environment; native request digest matches plan; endpoint change changes request and plan digests; input remains unchanged. |
| Invalid discovery | Missing/duplicate marker, missing config clear, case aliases, host scope, malformed SDN and competing config path are rejected by the actual environment encoder. |
| Unsupported access | Loopback/local endpoint, malformed credential reference and disabled network are refused before a launch plan is returned. |
| Existing environment | Reserved discovery cannot be replaced; ordinary explicit environment still encodes as before. |

The production hook is in
`src/lib/common/contracts/container/execution_options_v1.spl`, which the Linux
provider uses for request validation/digests and workload `--env` arguments.
The pre-sign producer is
`src/lib/nogc_async_mut/container/server_launch_projection_v1.spl`.
No signed envelope is rewritten. No host home, private key store or engine
socket is mounted. A bridge-capable plan does not prove DNS, route, credential
availability or successful server contact; those remain live qualification.

Windows workload environment needs its separate V5 provider extension. The V1
Linux-typed owner convenience function explicitly refuses Windows owners.
