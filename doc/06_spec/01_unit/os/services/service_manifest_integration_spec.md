# service_v1 Manifests Declared by REAL Services

> Verifies the service manifest integration behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# service_v1 Manifests Declared by REAL Services

Verifies the service manifest integration behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime / OS / Services |
| Status | In Progress |
| Source | `test/01_unit/os/services/service_manifest_integration_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the service manifest integration behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### container-manager declares a service_v1 manifest

#### publishes exactly the declared manifest fields

- Verify: publishes exactly the declared manifest fields
   - Expected: m.name equals `container-manager`
   - Expected: m.version equals `service_v1`
   - Expected: m.health_check_kind equals `heartbeat`
   - Expected: m.restart_policy equals `on_failure`
   - Expected: m.max_restarts equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.watchdog_timeout_ms equals `5000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned ... (full value in folded executable source)`
   - Expected: m.restart_count equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.state equals `Registered`
   - Expected: m.readiness_deps.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.readiness_deps[0] equals `vfs`
   - Expected: m.readiness_deps[1] equals `pm`
   - Expected: m.required_capabilities.len() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.required_capabilities[0] equals `cap.spawn`
   - Expected: m.granted_handles.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: publishes exactly the declared manifest fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m = container_manager_manifest()
expect(m.name).to_equal("container-manager")
expect(m.version).to_equal("service_v1")
expect(m.health_check_kind).to_equal("heartbeat")
expect(m.restart_policy).to_equal("on_failure")
expect(m.max_restarts).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.watchdog_timeout_ms).to_equal(5000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.restart_count).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.state).to_equal("Registered")
expect(m.readiness_deps.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.readiness_deps[0]).to_equal("vfs")
expect(m.readiness_deps[1]).to_equal("pm")
expect(m.required_capabilities.len()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.required_capabilities[0]).to_equal("cap.spawn")
expect(m.granted_handles.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### a fresh world carries the declared manifest, Registered and grant-free

- Verify: a fresh world carries the declared manifest, Registered and grant-free
   - Expected: w.svc_name() equals `container-manager`
   - Expected: w.svc_state() equals `Registered`
   - Expected: w.svc_restart_count() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.svc_holds_grants() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: a fresh world carries the declared manifest, Registered and grant-free")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_name()).to_equal("container-manager")
expect(w.svc_state()).to_equal("Registered")
expect(w.svc_restart_count()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.svc_holds_grants()).to_equal(false)
```

</details>

#### the start hook refuses until every readiness dependency is up

- Verify: the start hook refuses until every readiness dependency is up
   - Expected: w.svc_start(["vfs"]) is false
   - Expected: w.svc_state() equals `Registered`
   - Expected: w.svc_start(["clock", "vfs", "pm"]) is true
   - Expected: w.svc_state() equals `Starting`
   - Expected: w.svc_state() equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: the start hook refuses until every readiness dependency is up")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_start(["vfs"])).to_equal(false)
expect(w.svc_state()).to_equal("Registered")
expect(w.svc_start(["clock", "vfs", "pm"])).to_equal(true)
expect(w.svc_state()).to_equal("Starting")
w.svc_ready()
expect(w.svc_state()).to_equal("Ready")
```

</details>

### container-manager §21: restart drops stale grants

#### a restart clears the service manifest's granted handles

- Verify: a restart clears the service manifest's granted handles
   - Expected: w.svc_start(["vfs", "pm"]) is true
   - Expected: w.svc_grants().len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.svc_holds_grants() is true
   - Expected: w.svc_restart() is true
   - Expected: w.svc_grants().len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.svc_holds_grants() is false
   - Expected: w.svc_restart_count() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.svc_state() equals `Starting`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: a restart clears the service manifest's granted handles")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_start(["vfs", "pm"])).to_equal(true)
w.svc_acquire_grant("grant.blockdev.0")
w.svc_acquire_grant("secret.image-signing-key")
w.svc_ready()
expect(w.svc_grants().len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.svc_holds_grants()).to_equal(true)

expect(w.svc_restart()).to_equal(true)
# §21: zero grants survive, restart counted, back in Starting.
expect(w.svc_grants().len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.svc_holds_grants()).to_equal(false)
expect(w.svc_restart_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.svc_state()).to_equal("Starting")
```

</details>

#### a restart also tears down authority the manager had brokered out

- Verify: a restart also tears down authority the manager had brokered out
   - Expected: w.svc_start(["vfs", "pm"]) is true
   - Expected: w.granted_of(c0).len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.granted_of(c1).len() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.allows_path(c0, "/c1/app") is true
   - Expected: w.allows_path(c1, "/c2/app") is true
   - Expected: w.svc_restart() is true
   - Expected: w.svc_grants().len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.granted_of(c0).len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.granted_of(c1).len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.allows_path(c0, "/c1/app") is false
   - Expected: w.allows_path(c1, "/c2/app") is false
   - Expected: w.allows_pid(c0, 100u64) is false
   - Expected: w.path_decision(c0, "/c1/app") equals `deny`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: a restart also tears down authority the manager had brokered out")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_start(["vfs", "pm"])).to_equal(true)
w.svc_acquire_grant("grant.blockdev.0")
w.svc_ready()
val c0 = w.sys_create("app1", "/c1", [100u64], "sha256:aaa", 512u64, 2048u64, 50u64, 32u64, ["cap.fs_read", "cap.net_scoped"], false)
val c1 = w.sys_create("app2", "/c2", [200u64], "sha256:bbb", 512u64, 2048u64, 50u64, 32u64, ["cap.fs_read"], false)
# sanity: live containers resolve their own roots and hold pouches.
expect(w.granted_of(c0).len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.granted_of(c1).len()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.allows_path(c0, "/c1/app")).to_equal(true)
expect(w.allows_path(c1, "/c2/app")).to_equal(true)

expect(w.svc_restart()).to_equal(true)
# §21 at world granularity: pouches emptied, views collapsed to
# rootless — a manager that died vouches for nothing.
expect(w.svc_grants().len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.granted_of(c0).len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.granted_of(c1).len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.allows_path(c0, "/c1/app")).to_equal(false)
expect(w.allows_path(c1, "/c2/app")).to_equal(false)
expect(w.allows_pid(c0, 100u64)).to_equal(false)
expect(w.path_decision(c0, "/c1/app")).to_equal("deny")
```

</details>

### container-manager restart-limit counting

#### admits exactly max_restarts restarts, then refuses

- Verify: admits exactly max_restarts restarts, then refuses
   - Expected: w.svc_start(["vfs", "pm"]) is true
   - Expected: w.svc_restart_allowed() is true
   - Expected: w.svc_restart() is true
   - Expected: w.svc_restart_count() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.svc_restart() is true
   - Expected: w.svc_restart_count() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.svc_restart() is true
   - Expected: w.svc_restart_count() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: w.svc_restart_allowed() is false
   - Expected: w.svc_restart() is false
   - Expected: w.svc_restart_count() equals `3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: admits exactly max_restarts restarts, then refuses")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_start(["vfs", "pm"])).to_equal(true)
w.svc_ready()
expect(w.svc_restart_allowed()).to_equal(true)
expect(w.svc_restart()).to_equal(true)
expect(w.svc_restart_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.svc_restart()).to_equal(true)
expect(w.svc_restart_count()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(w.svc_restart()).to_equal(true)
expect(w.svc_restart_count()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
# limit spent: the 4th is refused and changes nothing.
expect(w.svc_restart_allowed()).to_equal(false)
expect(w.svc_restart()).to_equal(false)
expect(w.svc_restart_count()).to_equal(3)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### container-manager health + watchdog from world invariants

#### a clean world reports Ready and a §21 breach degrades then fails

- Verify: a clean world reports Ready and a §21 breach degrades then fails
   - Expected: w.svc_start(["vfs", "pm"]) is true
   - Expected: w.svc_world_invariant() is true
   - Expected: w.svc_health_check() equals `Ready`
   - Expected: life.state equals `stopped`
   - Expected: w.svc_world_invariant() is true
   - Expected: w.svc_health_check() equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: a clean world reports Ready and a §21 breach degrades then fails")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_start(["vfs", "pm"])).to_equal(true)
w.svc_ready()
val c0 = w.sys_create("app1", "/c1", [100u64], "sha256:aaa", 512u64, 2048u64, 50u64, 32u64, ["cap.fs_read"], false)
expect(w.svc_world_invariant()).to_equal(true)
expect(w.svc_health_check()).to_equal("Ready")
# a stopped container must hold nothing — sys_stop enforces it.
val life = w.sys_stop(c0)
expect(life.state).to_equal("stopped")
expect(w.svc_world_invariant()).to_equal(true)
expect(w.svc_health_check()).to_equal("Ready")
```

</details>

#### the watchdog fails a Ready service that stopped heart-beating

- Verify: the watchdog fails a Ready service that stopped heart-beating
   - Expected: w.svc_start(["vfs", "pm"]) is true
   - Expected: w.svc_watchdog(5500) equals `Ready`
   - Expected: w.svc_watchdog(6500) equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: the watchdog fails a Ready service that stopped heart-beating")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_start(["vfs", "pm"])).to_equal(true)
w.svc_ready()
w.svc_heartbeat(1000)
# inside the declared 5000ms window: still Ready.
expect(w.svc_watchdog(5500)).to_equal("Ready")
# past it: Failed.
expect(w.svc_watchdog(6500)).to_equal("Failed")
```

</details>

### tty service declares a service_v1 manifest

#### publishes exactly the declared manifest fields

- Verify: publishes exactly the declared manifest fields
   - Expected: m.name equals `tty`
   - Expected: m.version equals `service_v1`
   - Expected: m.health_check_kind equals `heartbeat`
   - Expected: m.restart_policy equals `always`
   - Expected: m.max_restarts equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.watchdog_timeout_ms equals `2000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned ... (full value in folded executable source)`
   - Expected: m.restart_count equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.state equals `Registered`
   - Expected: m.readiness_deps.len() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.readiness_deps[0] equals `ds`
   - Expected: m.required_capabilities.len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: m.required_capabilities[0] equals `dev.console`
   - Expected: m.required_capabilities[1] equals `dev.serial`
   - Expected: m.granted_handles.len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: publishes exactly the declared manifest fields")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val m = tty_service_manifest()
expect(m.name).to_equal("tty")
expect(m.version).to_equal("service_v1")
expect(m.health_check_kind).to_equal("heartbeat")
expect(m.restart_policy).to_equal("always")
expect(m.max_restarts).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.watchdog_timeout_ms).to_equal(2000)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.restart_count).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.state).to_equal("Registered")
expect(m.readiness_deps.len()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.readiness_deps[0]).to_equal("ds")
expect(m.required_capabilities.len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(m.required_capabilities[0]).to_equal("dev.console")
expect(m.required_capabilities[1]).to_equal("dev.serial")
expect(m.granted_handles.len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### a fresh service carries the declared manifest and gates on ds

- Verify: a fresh service carries the declared manifest and gates on ds
   - Expected: svc.svc_name() equals `tty`
   - Expected: svc.svc_state() equals `Registered`
   - Expected: svc.svc_holds_grants() is false
   - Expected: svc.svc_start(["vfs"]) is false
   - Expected: svc.svc_state() equals `Registered`
   - Expected: svc.svc_start(["ds"]) is true
   - Expected: svc.svc_state() equals `Starting`
   - Expected: svc.svc_state() equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: a fresh service carries the declared manifest and gates on ds")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var svc = TtyService.new()
expect(svc.svc_name()).to_equal("tty")
expect(svc.svc_state()).to_equal("Registered")
expect(svc.svc_holds_grants()).to_equal(false)
expect(svc.svc_start(["vfs"])).to_equal(false)
expect(svc.svc_state()).to_equal("Registered")
expect(svc.svc_start(["ds"])).to_equal(true)
expect(svc.svc_state()).to_equal("Starting")
svc.svc_ready()
expect(svc.svc_state()).to_equal("Ready")
```

</details>

### tty service §21: restart drops grants and pending-signal targeting

#### a pending SIGINT recorded before a restart does not survive it

- Verify: a pending SIGINT recorded before a restart does not survive it
   - Expected: svc.svc_start(["ds"]) is true
   - Expected: svc.svc_grants().len() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_set_session(tty, 42) is true
   - Expected: svc.tty_set_foreground(tty, 42, 777) is true
   - Expected: svc.tty_pending_signal(tty) equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_pending_signal_pgrp(tty) equals `777)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: svc.svc_pending_signal_total() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.svc_restart() is true
   - Expected: svc.svc_grants().len() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.svc_holds_grants() is false
   - Expected: svc.tty_pending_signal(tty) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_pending_signal_pgrp(tty) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.svc_pending_signal_total() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_take_pending_signal(tty) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.svc_restart_count() equals `1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.svc_state() equals `Starting`
   - Expected: svc.tty_session_id(tty) equals `42)  # oracle: pinned constant asserted by this scenario  # oracle: pinned co... (full value in folded executable source)`
   - Expected: svc.tty_foreground_pgrp(tty) equals `777)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 33 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: a pending SIGINT recorded before a restart does not survive it")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var svc = TtyService.new()
expect(svc.svc_start(["ds"])).to_equal(true)
svc.svc_acquire_grant("dev.console.0")
svc.svc_acquire_grant("dev.serial.0")
svc.svc_ready()
expect(svc.svc_grants().len()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

val tty = svc.tty_create(TTY_CONSOLE, 10u64, 20u64)
expect(svc.tty_set_session(tty, 42)).to_equal(true)
expect(svc.tty_set_foreground(tty, 42, 777)).to_equal(true)
# ISIG: a VINTR byte records a pending SIGINT aimed at pgrp 777.
svc.tty_ld_input(tty, 3)
expect(svc.tty_pending_signal(tty)).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_pending_signal_pgrp(tty)).to_equal(777)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.svc_pending_signal_total()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

expect(svc.svc_restart()).to_equal(true)
# §21: no device grant and NO pending-signal targeting survives.
expect(svc.svc_grants().len()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.svc_holds_grants()).to_equal(false)
expect(svc.tty_pending_signal(tty)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_pending_signal_pgrp(tty)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.svc_pending_signal_total()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_take_pending_signal(tty)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.svc_restart_count()).to_equal(1)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.svc_state()).to_equal("Starting")
# controlling-terminal binding is deliberately PRESERVED.
expect(svc.tty_session_id(tty)).to_equal(42)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_foreground_pgrp(tty)).to_equal(777)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

#### pending signals on EVERY tty are cleared, not just the first

- Verify: pending signals on EVERY tty are cleared, not just the first
   - Expected: svc.svc_start(["ds"]) is true
   - Expected: svc.tty_set_session(t0, 1) is true
   - Expected: svc.tty_set_session(t1, 2) is true
   - Expected: svc.tty_set_foreground(t0, 1, 111) is true
   - Expected: svc.tty_set_foreground(t1, 2, 222) is true
   - Expected: svc.tty_pending_signal_pgrp(t0) equals `111)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: svc.tty_pending_signal_pgrp(t1) equals `222)  # oracle: pinned constant asserted by this scenario  # oracle: pinned c... (full value in folded executable source)`
   - Expected: svc.svc_pending_signal_total() equals `2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.svc_restart() is true
   - Expected: svc.svc_pending_signal_total() equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_pending_signal(t0) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_pending_signal(t1) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_pending_signal_pgrp(t0) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.tty_pending_signal_pgrp(t1) equals `0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: pending signals on EVERY tty are cleared, not just the first")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var svc = TtyService.new()
expect(svc.svc_start(["ds"])).to_equal(true)
svc.svc_ready()
val t0 = svc.tty_create(TTY_CONSOLE, 10u64, 20u64)
val t1 = svc.tty_create(TTY_CONSOLE, 11u64, 21u64)
expect(svc.tty_set_session(t0, 1)).to_equal(true)
expect(svc.tty_set_session(t1, 2)).to_equal(true)
expect(svc.tty_set_foreground(t0, 1, 111)).to_equal(true)
expect(svc.tty_set_foreground(t1, 2, 222)).to_equal(true)
svc.tty_ld_input(t0, 3)
svc.tty_ld_input(t1, 3)
expect(svc.tty_pending_signal_pgrp(t0)).to_equal(111)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_pending_signal_pgrp(t1)).to_equal(222)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.svc_pending_signal_total()).to_equal(2)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario

expect(svc.svc_restart()).to_equal(true)
expect(svc.svc_pending_signal_total()).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_pending_signal(t0)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_pending_signal(t1)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_pending_signal_pgrp(t0)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
expect(svc.tty_pending_signal_pgrp(t1)).to_equal(0)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### tty service restart-limit counting

#### admits exactly max_restarts restarts, then refuses

- Verify: admits exactly max_restarts restarts, then refuses
   - Expected: svc.svc_start(["ds"]) is true
   - Expected: svc.svc_restart() is true
   - Expected: svc.svc_restart() is true
   - Expected: svc.svc_restart() is true
   - Expected: svc.svc_restart() is true
   - Expected: svc.svc_restart() is true
   - Expected: svc.svc_restart_count() equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`
   - Expected: svc.svc_restart_allowed() is false
   - Expected: svc.svc_restart() is false
   - Expected: svc.svc_restart_count() equals `5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned con... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: admits exactly max_restarts restarts, then refuses")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var svc = TtyService.new()
expect(svc.svc_start(["ds"])).to_equal(true)
svc.svc_ready()
expect(svc.svc_restart()).to_equal(true)
expect(svc.svc_restart()).to_equal(true)
expect(svc.svc_restart()).to_equal(true)
expect(svc.svc_restart()).to_equal(true)
expect(svc.svc_restart()).to_equal(true)
expect(svc.svc_restart_count()).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
# the declared max_restarts=5 is spent: the 6th is refused.
expect(svc.svc_restart_allowed()).to_equal(false)
expect(svc.svc_restart()).to_equal(false)
expect(svc.svc_restart_count()).to_equal(5)  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario  # oracle: pinned constant asserted by this scenario
```

</details>

### tty service health + watchdog

#### reports Ready while its pending-signal model is consistent

- Verify: reports Ready while its pending-signal model is consistent
   - Expected: svc.svc_start(["ds"]) is true
   - Expected: svc.tty_set_session(tty, 5) is true
   - Expected: svc.tty_set_foreground(tty, 5, 99) is true
   - Expected: svc.svc_world_invariant() is true
   - Expected: svc.svc_health_check() equals `Ready`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: reports Ready while its pending-signal model is consistent")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var svc = TtyService.new()
expect(svc.svc_start(["ds"])).to_equal(true)
svc.svc_ready()
val tty = svc.tty_create(TTY_CONSOLE, 10u64, 20u64)
expect(svc.tty_set_session(tty, 5)).to_equal(true)
expect(svc.tty_set_foreground(tty, 5, 99)).to_equal(true)
svc.tty_ld_input(tty, 3)
expect(svc.svc_world_invariant()).to_equal(true)
expect(svc.svc_health_check()).to_equal("Ready")
```

</details>

#### the watchdog fails a Ready service past its 2000ms deadline

- Verify: the watchdog fails a Ready service past its 2000ms deadline
   - Expected: svc.svc_start(["ds"]) is true
   - Expected: svc.svc_watchdog(2400) equals `Ready`
   - Expected: svc.svc_watchdog(2600) equals `Failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: the watchdog fails a Ready service past its 2000ms deadline")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var svc = TtyService.new()
expect(svc.svc_start(["ds"])).to_equal(true)
svc.svc_ready()
svc.svc_heartbeat(500)
expect(svc.svc_watchdog(2400)).to_equal("Ready")
expect(svc.svc_watchdog(2600)).to_equal("Failed")
```

</details>

### both services stop through the manifest path

#### a stopped service is Stopped and holds no grants

- Verify: a stopped service is Stopped and holds no grants
   - Expected: w.svc_start(["vfs", "pm"]) is true
   - Expected: w.svc_state() equals `Stopped`
   - Expected: w.svc_holds_grants() is false
   - Expected: svc.svc_start(["ds"]) is true
   - Expected: svc.svc_state() equals `Stopped`
   - Expected: svc.svc_holds_grants() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-SVC-service_v1-002
# @req: REQ-SVC-
step("Verify: a stopped service is Stopped and holds no grants")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var w = ContainerWorld.new()
expect(w.svc_start(["vfs", "pm"])).to_equal(true)
w.svc_acquire_grant("grant.blockdev.0")
w.svc_ready()
w.svc_stop()
expect(w.svc_state()).to_equal("Stopped")
expect(w.svc_holds_grants()).to_equal(false)

var svc = TtyService.new()
expect(svc.svc_start(["ds"])).to_equal(true)
svc.svc_acquire_grant("dev.console.0")
svc.svc_ready()
svc.svc_stop()
expect(svc.svc_state()).to_equal("Stopped")
expect(svc.svc_holds_grants()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1819ccf133494bc41148b8905fab2993c1a6bb61f3d58a85303df35d998d6d87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1819ccf133494bc41148b8905fab2993c1a6bb61f3d58a85303df35d998d6d87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1819ccf133494bc41148b8905fab2993c1a6bb61f3d58a85303df35d998d6d87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/os/services/service_manifest_integration_spec.spl
mirror: doc/06_spec/01_unit/os/services/service_manifest_integration_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/service_manifest_integration_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/os/services/service_manifest_integration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/service_manifest_integration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
