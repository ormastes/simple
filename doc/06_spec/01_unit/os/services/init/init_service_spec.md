# Init Service Specification

> Tests the init service manager: registration, dependency resolution via topological sort, dependency checking, and default service definitions.

<!-- sdn-diagram:id=init_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=init_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

init_service_spec -> std
init_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=init_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 33 | 33 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Init Service Specification

Tests the init service manager: registration, dependency resolution via topological sort, dependency checking, and default service definitions.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-INIT |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | In Progress |
| Source | `test/01_unit/os/services/init/init_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the init service manager: registration, dependency resolution
via topological sort, dependency checking, and default service definitions.

## Scenarios

### InitService

### new

#### starts with empty services

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = InitService.new()
expect(init.services.len()).to_equal(0)
```

</details>

#### starts with boot_complete false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = InitService.new()
expect(init.boot_complete).to_equal(false)
```

</details>

#### accepts an injected launcher

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = InitService.with_launcher(_launcher_ok)
expect(init.boot_complete).to_equal(false)
```

</details>

### register

#### adds a service

1. var init = InitService new
2. capabilities: ["FileRead
3. init register
   - Expected: init.services.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
val def_ = ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: ["FileRead(/)"],
    restart: RestartPolicy.Always,
    priority: "high"
)
init.register(def_)
expect(init.services.len()).to_equal(1)
```

</details>

#### sets initial state to Stopped

1. var init = InitService new
2. init register
   - Expected: init.services[0].state equals `ServiceState.Stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
val def_ = ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
)
init.register(def_)
expect(init.services[0].state).to_equal(ServiceState.Stopped)
```

</details>

#### sets restart_count to zero

1. var init = InitService new
2. init register
   - Expected: init.services[0].restart_count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
val def_ = ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
)
init.register(def_)
expect(init.services[0].restart_count).to_equal(0)
```

</details>

#### registers multiple services

1. var init = InitService new
2. init register
3. init register
   - Expected: init.services.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
val vfs_def = ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
)
val net_def = ServiceDef(
    name: "net",
    binary: "/sys/services/net",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
)
init.register(vfs_def)
init.register(net_def)
expect(init.services.len()).to_equal(2)
```

</details>

### resolve_start_order

#### returns single service

1. var init = InitService new
   - Expected: order.len() equals `1`
   - Expected: order[0] equals `vfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
val order = init.resolve_start_order()
expect(order.len()).to_equal(1)
expect(order[0]).to_equal("vfs")
```

</details>

#### puts dependency before dependent

1. var init = InitService new


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
init.register(ServiceDef(
    name: "compositor",
    binary: "/sys/services/compositor",
    args: [],
    dependencies: ["vfs"],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
val order = init.resolve_start_order()
# vfs must come before compositor
var vfs_idx = -1
var comp_idx = -1
var i = 0
while i < order.len():
    if order[i] == "vfs":
        vfs_idx = i
    if order[i] == "compositor":
        comp_idx = i
    i = i + 1
expect(vfs_idx).to_be_less_than(comp_idx)
```

</details>

#### handles multi-level dependencies

1. var init = InitService new
   - Expected: order.len() equals `3`
   - Expected: order[0] equals `vfs`


<details>
<summary>Executable SSpec</summary>

Runnable source: 32 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
init.register(ServiceDef(
    name: "desktop",
    binary: "/sys/apps/desktop",
    args: [],
    dependencies: ["compositor", "vfs"],
    capabilities: [],
    restart: RestartPolicy.OnFailure,
    priority: "normal"
))
init.register(ServiceDef(
    name: "compositor",
    binary: "/sys/services/compositor",
    args: [],
    dependencies: ["vfs"],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
val order = init.resolve_start_order()
expect(order.len()).to_equal(3)
# vfs first
expect(order[0]).to_equal("vfs")
```

</details>

### check_deps

#### returns true for empty dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = InitService.new()
val result = init.check_deps([])
expect(result).to_equal(true)
```

</details>

#### returns false when dep is not running

1. var init = InitService new
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.new()
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
# vfs is Stopped, not Running
val result = init.check_deps(["vfs"])
expect(result).to_equal(false)
```

</details>

#### returns false when dep is not registered

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val init = InitService.new()
val result = init.check_deps(["nonexistent"])
expect(result).to_equal(false)
```

</details>

### default_services

#### returns 5 services

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs.len()).to_equal(5)
```

</details>

#### starts with vfs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[0].name).to_equal("vfs")
```

</details>

#### includes net

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[1].name).to_equal("net")
```

</details>

#### includes compositor depending on vfs

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[2].name).to_equal("compositor")
expect(defs[2].dependencies).to_contain("vfs")
```

</details>

#### includes desktop depending on compositor and vfs

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[3].name).to_equal("desktop")
expect(defs[3].dependencies).to_contain("compositor")
expect(defs[3].dependencies).to_contain("vfs")
```

</details>

#### includes llm_mcp depending on compositor, vfs, and net

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[4].name).to_equal("llm_mcp")
expect(defs[4].dependencies).to_contain("compositor")
expect(defs[4].dependencies).to_contain("vfs")
expect(defs[4].dependencies).to_contain("net")
```

</details>

#### vfs has no dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[0].dependencies.len()).to_equal(0)
```

</details>

#### vfs has Always restart policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[0].restart).to_equal(RestartPolicy.Always)
```

</details>

#### desktop has OnFailure restart policy

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val defs = default_services()
expect(defs[3].restart).to_equal(RestartPolicy.OnFailure)
```

</details>

### InitService launch path

#### starts a service through the binary launcher

1. var init = InitService with launcher
2. init start service
   - Expected: init.services[0].state equals `ServiceState.Running(pid: 41)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.start_service("vfs")
expect(init.services[0].state).to_equal(ServiceState.Running(pid: 41))
```

</details>

#### fails a service when the launcher returns an error

1. var init = InitService with launcher
2. init start service
   - Expected: init.services[0].state equals `ServiceState.Failed(reason: "launch failed")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_err)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.start_service("vfs")
expect(init.services[0].state).to_equal(ServiceState.Failed(reason: "launch failed"))
```

</details>

#### forwards service args into the launcher

1. var init = InitService with launcher
2. init start service
   - Expected: init.services[0].state equals `ServiceState.Running(pid: 77)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_expect_args)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: ["--foreground", "--trace"],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.start_service("vfs")
expect(init.services[0].state).to_equal(ServiceState.Running(pid: 77))
```

</details>

#### does not launch a service until dependencies are running

1. var init = InitService with launcher
2. init start service
   - Expected: init.services[0].state equals `ServiceState.Stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "compositor",
    binary: "/sys/services/compositor",
    args: [],
    dependencies: ["vfs"],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.start_service("compositor")
expect(init.services[0].state).to_equal(ServiceState.Stopped)
```

</details>

### InitService supervision

#### can start a stopped service with satisfied dependencies

1. var init = InitService with launcher
   - Expected: init.can_start_service("vfs") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
expect(init.can_start_service("vfs")).to_equal(true)
```

</details>

#### does not start a running service again

1. var init = InitService with launcher
2. init start service
   - Expected: init.can_start_service("vfs") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.start_service("vfs")
expect(init.can_start_service("vfs")).to_equal(false)
```

</details>

#### restarts an Always service after clean exit

1. var init = InitService with launcher
2. init start service
   - Expected: disposition equals `AppExitDisposition.Restart`
   - Expected: init.services[0].restart_count equals `1`
   - Expected: init.services[0].state equals `ServiceState.Running(pid: 41)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.start_service("vfs")
val disposition = init.handle_service_exit("vfs", 0)
expect(disposition).to_equal(AppExitDisposition.Restart)
expect(init.services[0].restart_count).to_equal(1)
expect(init.services[0].state).to_equal(ServiceState.Running(pid: 41))
```

</details>

#### stops an OnFailure service after clean exit

1. var init = InitService with launcher
2. init start service
   - Expected: disposition equals `AppExitDisposition.Stop`
   - Expected: init.services[0].restart_count equals `0`
   - Expected: init.services[0].state equals `ServiceState.Stopped`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.OnFailure,
    priority: "high"
))
init.start_service("vfs")
val disposition = init.handle_service_exit("vfs", 0)
expect(disposition).to_equal(AppExitDisposition.Stop)
expect(init.services[0].restart_count).to_equal(0)
expect(init.services[0].state).to_equal(ServiceState.Stopped)
```

</details>

#### restarts an OnFailure service after failure exit

1. var init = InitService with launcher
2. init start service
   - Expected: disposition equals `AppExitDisposition.Restart`
   - Expected: init.services[0].restart_count equals `1`
   - Expected: init.services[0].state equals `ServiceState.Running(pid: 41)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.OnFailure,
    priority: "high"
))
init.start_service("vfs")
val disposition = init.handle_service_exit("vfs", 101)
expect(disposition).to_equal(AppExitDisposition.Restart)
expect(init.services[0].restart_count).to_equal(1)
expect(init.services[0].state).to_equal(ServiceState.Running(pid: 41))
```

</details>

#### quarantines a service after hitting restart limit

1. var init = InitService with launcher
   - Expected: disposition equals `AppExitDisposition.Quarantine`
   - Expected: init.services[0].state equals `ServiceState.Quarantined(reason: "panic")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
init.services[0].restart_count = 5
val disposition = init.handle_service_exit("vfs", 101)
expect(disposition).to_equal(AppExitDisposition.Quarantine)
expect(init.services[0].state).to_equal(ServiceState.Quarantined(reason: "panic"))
```

</details>

#### escalates invariant violations for system services

1. var init = InitService with launcher
   - Expected: disposition equals `AppExitDisposition.Escalate`
   - Expected: init.services[0].state equals `ServiceState.Failed(reason: "invariant_violation")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var init = InitService.with_launcher(_launcher_ok)
init.register(ServiceDef(
    name: "vfs",
    binary: "/sys/services/vfs",
    args: [],
    dependencies: [],
    capabilities: [],
    restart: RestartPolicy.Always,
    priority: "high"
))
val disposition = init.handle_service_crash("vfs", CrashReason.InvariantViolation)
expect(disposition).to_equal(AppExitDisposition.Escalate)
expect(init.services[0].state).to_equal(ServiceState.Failed(reason: "invariant_violation"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 33 |
| Active scenarios | 33 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
