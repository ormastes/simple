<!-- codex-design -->

# SimpleOS Enhancement System Test Plan

| Requirement | Scenario | First executable owner |
| --- | --- | --- |
| REQ-001 | filesystem exec receives a live caller context and rejects an unknown task | Lane A focused spec |
| REQ-002–003 | two same-image workloads receive distinct CSpaces; attenuation/revocation/seal deny escalation | Lane A focused spec |
| REQ-004–005 | PID1 orders VFS→network→HTTP, restarts network with fresh grants, then quarantines a storm | Lane B QEMU spec |
| REQ-006 | cross-domain VFS/PID/IPC/network/device attempts fail; resource exhaustion stays local | Lanes C/D system specs |
| REQ-007–009 | common policy compiles service/container/agent; rootless lifecycle and subagent approval flow execute | Lanes E/F QEMU specs |

All future scenario specs use the frozen `step(...)` vocabulary from the agent
plan and built-in matchers only. Each QEMU/environment row that cannot run on
the current host stays visible as `blocked` with a tracked resume command.

## Executable host contract

[`test/03_system/os/simple_os_enhance_spec.spl`](../../../test/03_system/os/simple_os_enhance_spec.spl)
is the deterministic host-level contract for REQ-004 and REQ-005. It proves
readiness ordering, fresh-grant restart semantics, and the bounded restart
decision using the service lifecycle model that PID1 consumes.

It is intentionally not native/QEMU evidence. The required target campaign
remains blocked until `sh scripts/os/simpleos-native-build.shs` can find a
working self-hosted Simple compiler; the current capability probe segfaults
before a native image can be produced. Once fixed, the QEMU scenario must
replace host-model proof with process launch, crash, re-grant, reconnect and
quarantine evidence.
