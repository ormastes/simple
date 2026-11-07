# Selected Windows Docker process-provider requirements

Selection: user's explicit full orchestrator plan, 2026-11-07; Docker is the first
Windows process-isolation bridge. Existing `REQ-WPC-*` scope is retained. This is
an implementation slice, not completion of all Windows orchestration gates.

| ID | Required behavior | Evidence |
|---|---|---|
| REQ-WDP-001 | Bind the explicit local Docker endpoint and engine identity; reject non-Windows engine/image observations. | Exact scripted probes and negative assertions; live NOT_RUN. |
| REQ-WDP-002 | Use digest-pinned Windows images, exact selected host/image versions, ContainerUser and process isolation; check actual inspection. | Negative metadata/isolation assertions; live NOT_RUN. |
| REQ-WDP-003 | Carry command and arguments as typed argv; bound resources, execution and retained output. | Command-vector and validation assertions; native argv NOT_RUN. |
| REQ-WDP-004 | Bind every lifecycle mutation to the explicit continuity scope, generation, attempt, operation, request digest and full engine-native ID. | Ownership/recovery negative assertions; live restart NOT_RUN. |
| REQ-WDP-005 | Do not retry an uncertain create, clean up by raw name, prune globally or substitute Hyper-V/WSL. | Ambiguous failure scenarios and source review. |
| REQ-WDP-006 | Preserve common operation envelopes and distinguish scripted observations from live qualification. | Provider integration source review; compiler/SPipe NOT_RUN. |

The user subsequently selected all lifecycle effects through the shared Simple
Container API, persistent service continuity and protected workspace execution.

| ID | Required behavior | Evidence |
|---|---|---|
| REQ-WDP-007 | Mint a native service incarnation, inventory exact old scopes and keep launches closed until durable host quarantine acknowledgment. | Actual service factory/adapter source and common API scripted service specs; live NOT_RUN. |
| REQ-WDP-008 | Permit one typed bind mount only below the administrator's protected root, verify native path containment and exact Docker mount metadata. | Policy/request SDN negatives, scripted actual mount mismatches, native path owner source; live NOT_RUN. |
| REQ-WDP-009 | Resolve explicit argv/cwd/mounts and retain a fresh exact-object configured-user receipt; guest workspace access must be probed before task execution. | Shared action projection, selected-user query assertions and remote producer integration; live NOT_RUN. |
| REQ-WDP-010 | A failed create confirmation grants recovery-only authority for its exact retained native candidate; cleanup/start remain blocked until successful full recovery. | Actual shared API candidate recovery and wrong-ID/cleanup negatives; SPipe NOT_RUN. |

Ordinary-client delegation, end-to-end controller Windows dispatch, installation,
broad network policy and live qualification remain verification gates. A Docker
pipe grants broad engine authority and does not satisfy `REQ-WPC-004` alone.
