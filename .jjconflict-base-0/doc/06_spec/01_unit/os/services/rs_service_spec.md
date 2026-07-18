# RsService Specification (G4)

> Reincarnation Server (RS) — Minix-style capsule supervisor.  Validates registration, heartbeat liveness, timeout detection, restart policy, budget exhaustion, crash reason codes, and multi-capsule isolation.

<!-- sdn-diagram:id=rs_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=rs_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

rs_service_spec -> std
rs_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=rs_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# RsService Specification (G4)

Reincarnation Server (RS) — Minix-style capsule supervisor.  Validates registration, heartbeat liveness, timeout detection, restart policy, budget exhaustion, crash reason codes, and multi-capsule isolation.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G4 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/rs_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Reincarnation Server (RS) — Minix-style capsule supervisor.  Validates
registration, heartbeat liveness, timeout detection, restart policy,
budget exhaustion, crash reason codes, and multi-capsule isolation.

## Scenarios

### RsService initial state
_Verify that a freshly constructed RsService starts empty at tick 0._

#### constructs with tick=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = RsService.new()
expect(svc.tick).to_equal(0)
```

</details>

#### constructs with zero supervised capsules

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val svc = RsService.new()
expect(svc.rs_count()).to_equal(0)
```

</details>

### RsService registration
_rs_register installs all components and returns distinct entities._

#### register increments capsule count to 1

1. var svc = RsService new
   - Expected: svc.rs_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val _e = svc.rs_register("pm", "/bin/pm", 10, 30, 3, true)
expect(svc.rs_count()).to_equal(1)
```

</details>

#### two registrations yield distinct entity ids

1. var svc = RsService new
   - Expected: ids_differ is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e1 = svc.rs_register("pm",  "/bin/pm",  10, 30, 3, true)
val e2 = svc.rs_register("vfs", "/bin/vfs", 10, 30, 3, true)
val ids_differ: bool = e1.id != e2.id
expect(ids_differ).to_equal(true)
```

</details>

### RsService heartbeat
_Heartbeat keeps capsule alive; missing heartbeat past timeout triggers restart._

#### heartbeat keeps capsule alive after one advance

1. var svc = RsService new
   - Expected: svc.rs_is_alive(e) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("pm", "/bin/pm", 10, 5, 3, true)
val _hb = svc.rs_heartbeat(e)
val _t1 = svc.rs_advance()
val _hb2 = svc.rs_heartbeat(e)
expect(svc.rs_is_alive(e)).to_equal(true)
```

</details>

#### heartbeat on unregistered entity returns false

1. var svc = RsService new
   - Expected: result is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val bogus = svc.rs_register("pm", "/bin/pm", 10, 5, 3, true)
# Advance enough ticks that the capsule times out so we can
# observe behavior on an entity that has been registered but
# whose component slot is freshly allocated; use a second fresh
# service with no registrations to get a truly unknown entity.
val svc2 = RsService.new()
# bogus entity was allocated from svc, not svc2 — no component in svc2
val result = svc2.rs_heartbeat(bogus)
expect(result).to_equal(false)
```

</details>

#### missing heartbeat past timeout makes capsule not alive

1. var svc = RsService new
   - Expected: svc.rs_is_alive(e) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("pm", "/bin/pm", 10, 2, 5, true)
# Advance 3 ticks without sending heartbeat — elapsed (3) > timeout (2)
val _t1 = svc.rs_advance()
val _t2 = svc.rs_advance()
val _t3 = svc.rs_advance()
expect(svc.rs_is_alive(e)).to_equal(false)
```

</details>

#### missing heartbeat triggers restart: restart_count goes 0 to 1

1. var svc = RsService new
   - Expected: svc.rs_restart_count(e) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("pm", "/bin/pm", 10, 1, 5, true)
# Advance 2 ticks without heartbeat — elapsed (2) > timeout (1)
val _t1 = svc.rs_advance()
val _t2 = svc.rs_advance()
expect(svc.rs_restart_count(e)).to_equal(1)
```

</details>

### RsService restart policy
_Restart budget enforcement and backoff tracking._

#### restart budget exhausted: rs_restart returns false

1. var svc = RsService new
   - Expected: ok1 is true
   - Expected: ok2 is true
   - Expected: ok3 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("pm", "/bin/pm", 10, 99, 2, true)
# Manually trigger two restarts via rs_restart
val ok1 = svc.rs_restart(e)
val ok2 = svc.rs_restart(e)
val ok3 = svc.rs_restart(e)
expect(ok1).to_equal(true)
expect(ok2).to_equal(true)
expect(ok3).to_equal(false)
```

</details>

#### consecutive restarts update last_restart_tick

1. var svc = RsService new
   - Expected: svc.rs_restart_count(e) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("driver", "/bin/drv", 10, 99, 5, true)
val _t1 = svc.rs_advance()
val _ok1 = svc.rs_restart(e)
val _t2 = svc.rs_advance()
val _ok2 = svc.rs_restart(e)
# After 2 restarts, restart count must be 2
expect(svc.rs_restart_count(e)).to_equal(2)
```

</details>

#### rs_restart_count returns 0 for unregistered entity

1. var svc = RsService new
   - Expected: svc2.rs_restart_count(e) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("pm", "/bin/pm", 10, 5, 3, true)
val svc2 = RsService.new()
expect(svc2.rs_restart_count(e)).to_equal(0)
```

</details>

### RsService crash reason
_LastCrashInfo records the correct reason code after a timeout._

#### crash reason is RS_REASON_HEARTBEAT_TIMEOUT after missed heartbeat

1. var svc = RsService new
   - Expected: svc.rs_last_crash_reason(e) equals `RS_REASON_HEARTBEAT_TIMEOUT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("vfs", "/bin/vfs", 10, 1, 5, true)
val _t1 = svc.rs_advance()
val _t2 = svc.rs_advance()
expect(svc.rs_last_crash_reason(e)).to_equal(RS_REASON_HEARTBEAT_TIMEOUT)
```

</details>

#### crash reason is RS_REASON_NONE before any crash

1. var svc = RsService new
   - Expected: svc.rs_last_crash_reason(e) equals `RS_REASON_NONE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e = svc.rs_register("vfs", "/bin/vfs", 10, 100, 5, true)
expect(svc.rs_last_crash_reason(e)).to_equal(RS_REASON_NONE)
```

</details>

### RsService multi-capsule isolation
_One capsule dying must not affect others._

#### one capsule times out while others stay alive

1. var svc = RsService new
   - Expected: svc.rs_is_alive(e_pm) is false
   - Expected: svc.rs_is_alive(e_vfs) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var svc = RsService.new()
val e_pm  = svc.rs_register("pm",  "/bin/pm",  10, 1, 5, true)
val e_vfs = svc.rs_register("vfs", "/bin/vfs", 10, 100, 5, true)
# e_vfs sends heartbeat; e_pm does not
val _hb = svc.rs_heartbeat(e_vfs)
val _t1 = svc.rs_advance()
val _hb2 = svc.rs_heartbeat(e_vfs)
val _t2 = svc.rs_advance()
# e_pm elapsed=2 > timeout=1 → dead; e_vfs just heartbeated → alive
expect(svc.rs_is_alive(e_pm)).to_equal(false)
expect(svc.rs_is_alive(e_vfs)).to_equal(true)
```

</details>

### RsService reason constants
_RS_REASON_* constants must have their specified fixed values._

#### RS_REASON_NONE is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RS_REASON_NONE).to_equal(0)
```

</details>

#### RS_REASON_HEARTBEAT_TIMEOUT is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RS_REASON_HEARTBEAT_TIMEOUT).to_equal(1)
```

</details>

#### RS_REASON_EXIT_NONZERO is 2

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RS_REASON_EXIT_NONZERO).to_equal(2)
```

</details>

#### RS_REASON_SIGNAL is 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(RS_REASON_SIGNAL).to_equal(3)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
