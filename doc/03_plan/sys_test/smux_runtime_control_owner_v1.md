# Runtime control owner acceptance

All new SSpec cases are AUTHORED_UNRUN. No compiler, core/MCP or native checks
were rerun for this source checkpoint. The earlier credential evidence applies
only to its historical native owner and is not evidence for these controls.

| Requirement | Implementation | Prevention/acceptance |
|---|---|---|
| REQ-RCONTROL-001: authenticated installed owner only | server configured dispatch and fixed policy snapshot | route wrong-token/unconfigured denial; real configured socket fixture |
| REQ-RCONTROL-002: independent Input/Geometry rights | common target and bounded issuer | pure owner distinct rights/CAS/replay/expiry/clock cases |
| REQ-RCONTROL-003: current exact target and attachment | target resolver, checked ClientLease snapshot | digest mismatch, holder loss, binding drift; real adopted binding fixture |
| REQ-RCONTROL-004: legacy leases cannot bypass control | existing pane send/VT/geometry effect guards | direct guard regression and real client-request input refusal |
| REQ-RCONTROL-005: truthful effects and cleanup | strict reply/client and retained signed fixture | unsupported controls exit nonzero; real attachment cleanup and independent workload inspection |

Unit source: `test/01_unit/os/apps/smux/runtime_control_route_v1_spec.spl` and
the adjacent issuer/policy specs. Pure owner fixtures are metadata only; their
success does not attest native adoption or authentication.

System source: `test/03_system/app/llm_caret/feature/smux_runtime_control_socket_spec.spl`.
It reuses actual signed Container binding setup and cleanup, requires fresh
workload output through pane polling, exercises compiled socket clients, and
independently inspects the surviving workload after host writer release.
Missing enrollment, policy, compiled products, broker facilities or evidence
fails preconditions. No environment skip is a pass. All post-start outcomes keep
the original fixture carrier before cleanup or assertions.

No positive input delivery/PTY resize/Windows execution test can pass until the
actual common provider effect ports exist. Those are explicit full-feature gaps.
