# SimpleOS PID1 service-lifecycle host contract

> This deterministic system-level contract exercises the typed lifecycle policy consumed by the SimpleOS PID1 service manager. It makes service readiness, restart revocation and restart-rate bounds executable at the host-model layer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SimpleOS PID1 service-lifecycle host contract

This deterministic system-level contract exercises the typed lifecycle policy consumed by the SimpleOS PID1 service manager. It makes service readiness, restart revocation and restart-rate bounds executable at the host-model layer.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Requirements | doc/02_requirements/feature/simple_os_enhance.md |
| Plan | doc/03_plan/sys_test/simple_os_enhance.md |
| Design | doc/05_design/simple_os_enhance.md |
| Research | doc/01_research/local/simple_os_enhance.md |
| Source | `test/03_system/os/simple_os_enhance_spec.spl` |
| Updated | 2026-08-11 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This deterministic system-level contract exercises the typed lifecycle policy
consumed by the SimpleOS PID1 service manager. It makes service readiness,
restart revocation and restart-rate bounds executable at the host-model layer.

## Requirements

**Requirements:** doc/02_requirements/feature/simple_os_enhance.md

* REQ-004: managed services start only after their readiness dependencies.
* REQ-005: a restart loses all old grants and a restart storm is bounded.

## Plan

**Plan:** doc/03_plan/sys_test/simple_os_enhance.md

The test follows the planned VFS -> network -> HTTP ordering, then models a
network crash. The only accepted restarted state contains no old device or IPC
grant labels. Once the restart counter reaches its configured limit, the
lifecycle policy denies another restart; PID1 is then responsible for
quarantining it.

## Design

**Design:** doc/05_design/simple_os_enhance.md

## Research

**Research:** doc/01_research/local/simple_os_enhance.md

## Syntax

The test names are behavioral contracts.  Their implementation follows a
stable three-step vocabulary:

```text
step("Register PID1 service manifests")
step("Gate dependent services on reported readiness")
step("Publish dependency readiness in dependency order")
```

The contract uses `ServiceManifest` as the shared lifecycle record. A service
declares `readiness_deps`; `can_start` accepts it only when each dependency is
in the supervisor's ready set. `on_restart` returns a new record and empties
`granted_handles`, making prior grants unusable by the replacement instance.

## Examples

### Readiness gate

```text
vfs:  readiness_deps = []       -> may start
net:  readiness_deps = ["vfs"]  -> waits for VFS Ready
http: readiness_deps = ["net"]  -> waits for network Ready
```

Reporting that VFS is merely starting is insufficient: only its `Ready` name
is passed to the next dependency evaluation. This avoids claiming network or
HTTP availability before their supporting endpoints are available.

### Fresh restart instance

```text
before crash: granted_handles = [device:virtio-net, endpoint:net]
after restart: granted_handles = []
```

The broker must issue any replacement authority after the new process exists.
The old process must not retain handles through a copied lifecycle record.

### Bounded failure response

```text
restart_count < max_restarts  -> PID1 may attempt restart
restart_count >= max_restarts -> PID1 must quarantine
```

The policy function does not itself kill a process or grant an endpoint. Those
effects belong to the live service manager and kernel capability machinery;
the split keeps this host contract deterministic and makes its boundary clear.

## Evidence boundary

This is host-model evidence, not a fabricated native execution result. Native
and QEMU acceptance needs filesystem-backed service payloads, a working
self-hosted native compiler, real process-exit events and broker reacquisition.
Those checks remain blocked until the native build can pass its compiler
capability probe. The source-level lifecycle invariants here stay useful during
that remediation because they are the policy PID1 must preserve.

## Non-goals

This specification does not model a device driver, a network socket ABI, or an
HTTP implementation. It also does not substitute string grants for kernel
capability handles: the labels only make the pure lifecycle transition visible.
The native acceptance suite must independently show handle revocation, process
reaping, endpoint recreation and peer reconnection under QEMU.

## Scenarios

### SimpleOS managed-service host contract

#### starts VFS then network then HTTP only after each readiness dependency

- Register PID1 service manifests
- Gate dependent services on reported readiness
- Publish VFS and network readiness in dependency order
   - Expected: vfs.state equals `Ready`
   - Expected: net.state equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Register PID1 service manifests")
var vfs = ServiceManifest.create("vfs", "1")
var net = ServiceManifest.create("net", "1")
var http = ServiceManifest.create("http", "1")
net.readiness_deps = ["vfs"]
http.readiness_deps = ["net"]

step("Gate dependent services on reported readiness")
expect(can_start(vfs, [])).to_be(true)
expect(can_start(net, [])).to_be(false)
expect(can_start(http, ["vfs"])).to_be(false)

step("Publish VFS and network readiness in dependency order")
vfs = mark_ready(mark_starting(vfs))
expect(vfs.state).to_equal("Ready")
expect(can_start(net, [vfs.name])).to_be(true)
net = mark_ready(mark_starting(net))
expect(net.state).to_equal("Ready")
expect(can_start(http, [vfs.name, net.name])).to_be(true)
```

</details>

#### revokes stale grants before a crashed service can restart

- Model a running network service with broker-issued grants
- Restart from a fresh lifecycle instance
   - Expected: restarted.state equals `Restarting`
   - Expected: restarted.restart_count equals `1`
   - Expected: restarted.granted_handles.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Model a running network service with broker-issued grants")
var net = ServiceManifest.create("net", "1")
net.granted_handles = ["device:virtio-net", "endpoint:net"]
net = mark_ready(mark_starting(net))
expect(holds_grants(net)).to_be(true)

step("Restart from a fresh lifecycle instance")
val restarted = on_restart(net)
expect(restarted.state).to_equal("Restarting")
expect(restarted.restart_count).to_equal(1)
expect(restarted.granted_handles.len()).to_equal(0)
expect(holds_grants(restarted)).to_be(false)
```

</details>

#### quarantines a restart storm at the manifest restart limit

- Apply PID1 bounded-restart policy
- Consume the permitted restarts
   - Expected: net.restart_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply PID1 bounded-restart policy")
var net = ServiceManifest.create("net", "1")
net.max_restarts = 2
expect(should_restart(net.restart_policy, net.restart_count, net.max_restarts)).to_be(true)

step("Consume the permitted restarts")
net = on_restart(net)
net = on_restart(net)
expect(net.restart_count).to_equal(2)
expect(should_restart(net.restart_policy, net.restart_count, net.max_restarts)).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/02_requirements/feature/simple_os_enhance.md`
- **Plan:** `doc/03_plan/sys_test/simple_os_enhance.md`
- **Design:** `doc/05_design/simple_os_enhance.md`
- **Research:** `doc/01_research/local/simple_os_enhance.md`


</details>
