# Selected Windows Docker process-provider requirements

Selection: user's explicit full orchestrator plan, 2026-11-07; Docker is the first
Windows process-isolation bridge. Existing `REQ-WPC-*` scope is retained. This is
an implementation slice, not completion of all Windows orchestration gates.

| ID | Required behavior | Evidence |
|---|---|---|
| REQ-WDP-001 | Bind the explicit local Docker endpoint and engine identity; reject non-Windows engine/image observations. | Exact scripted probes and negative assertions; live NOT_RUN. |
| REQ-WDP-002 | Use digest-pinned Windows images, exact selected host/image versions, ContainerUser and process isolation; check actual inspection. | Negative metadata/isolation assertions; live NOT_RUN. |
| REQ-WDP-003 | Carry command and arguments as typed argv; bound resources, execution and retained output. | Command-vector and validation assertions; native argv NOT_RUN. |
| REQ-WDP-004 | Bind every lifecycle mutation to boot, generation, attempt, operation, request digest and full engine-native ID. | Ownership/recovery negative assertions; live restart NOT_RUN. |
| REQ-WDP-005 | Do not retry an uncertain create, clean up by raw name, prune globally or substitute Hyper-V/WSL. | Ambiguous failure scenarios and source review. |
| REQ-WDP-006 | Preserve common operation envelopes and distinguish scripted observations from live qualification. | Provider integration source review; compiler/SPipe NOT_RUN. |

Ordinary-client delegation, controller Windows dispatch, installation, broad
network policy, mounts and live qualification are outstanding gates. A Docker
pipe grants broad engine authority and does not satisfy `REQ-WPC-004` alone.
