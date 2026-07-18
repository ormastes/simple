# Process Manager Service Specification

> Validates PmService process lifecycle management: init, fork, exec, exit, waitpid, kill, and entity-pid round-trip queries.

<!-- sdn-diagram:id=pm_service_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=pm_service_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

pm_service_spec -> std
pm_service_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=pm_service_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 17 | 17 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Process Manager Service Specification

Validates PmService process lifecycle management: init, fork, exec, exit, waitpid, kill, and entity-pid round-trip queries.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #G3 |
| Category | Infrastructure |
| Difficulty | 3/5 |
| Status | Implemented |
| Source | `test/01_unit/os/services/pm_service/pm_service_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates PmService process lifecycle management: init, fork, exec, exit,
waitpid, kill, and entity-pid round-trip queries.

## Behavior

- pm_init creates the pid-1 init entity
- pm_fork allocates a child entity cloning parent creds; COW-clones vmspace
- pm_exec calls loader_exec and updates ExecImage on success
- pm_exit marks zombie and notifies parent via signal_deliver
- pm_waitpid is one-shot: reaping twice returns -ECHILD
- pm_kill delivers signal via signal_deliver; -ESRCH for unknown pid
- pm_find_entity round-trips pid -> entity -> pid

## Scenarios

### PmService init

#### pm_init creates the init process with pid 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
val ok = pm.pm_init()
expect(ok).to_equal(true)
expect(pm.pm_process_count()).to_equal(1)
val e = pm.pm_find_entity(1)
expect(e.is_null()).to_equal(false)
val pid_back = pm.pm_get_pid(e.id)
expect(pid_back).to_equal(1)
```

</details>

#### pm_init is idempotent (second call returns true without duplicating)

1. pm pm init
   - Expected: ok2 is true
   - Expected: pm.pm_process_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val ok2 = pm.pm_init()
expect(ok2).to_equal(true)
expect(pm.pm_process_count()).to_equal(1)
```

</details>

### PmService fork

#### pm_fork returns a new pid and increments process_count

1. pm pm init
   - Expected: pm.pm_process_count() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
expect(child_pid).to_be_greater_than(0)
expect(pm.pm_process_count()).to_equal(2)
```

</details>

#### pm_fork with unknown parent returns -ECHILD

1. pm pm init
   - Expected: result equals `-ECHILD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val result = pm.pm_fork(999)
expect(result).to_equal(-ECHILD)
```

</details>

#### two successive forks produce distinct pids

1. pm pm init
   - Expected: pm.pm_process_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val pid1 = pm.pm_fork(1)
val pid2 = pm.pm_fork(1)
expect(pid1).to_be_greater_than(0)
expect(pid2).to_be_greater_than(0)
expect(pid2).to_be_greater_than(pid1)
expect(pm.pm_process_count()).to_equal(3)
```

</details>

### PmService exec

#### pm_exec on unknown pid returns negative errno

1. pm pm init


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val result = pm.pm_exec(999, "/bin/sh", [], [])
expect(result).to_be_less_than(0)
```

</details>

#### pm_exec on valid pid calls loader and returns 0

1. reset signal counters
2. pm pm init
   - Expected: result equals `0`
   - Expected: test_loader_exec_calls equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_signal_counters()
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
val result = pm.pm_exec(child_pid.to_u32(), "/bin/init", [], [])
expect(result).to_equal(0)
expect(test_loader_exec_calls).to_equal(1)
```

</details>

#### pm_exec propagates loader failure as negative errno

1. reset signal counters
2. pm pm init


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_signal_counters()
test_loader_exec_should_fail = true
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
val result = pm.pm_exec(child_pid.to_u32(), "/missing", [], [])
expect(result).to_be_less_than(0)
test_loader_exec_should_fail = false
```

</details>

### PmService exit and waitpid

#### pm_exit marks process as zombie; parent can pm_waitpid successfully

1. reset signal counters
2. pm pm init
3. pm pm exit
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_signal_counters()
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
pm.pm_exit(child_pid.to_u32(), 42)
val result = pm.pm_waitpid(1, child_pid.to_u32())
expect(result).to_equal(42)
```

</details>

#### pm_waitpid on non-zombie child returns -EAGAIN

1. pm pm init
   - Expected: result equals `-EAGAIN`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
val result = pm.pm_waitpid(1, child_pid.to_u32())
expect(result).to_equal(-EAGAIN)
```

</details>

#### pm_waitpid on already-reaped child returns -ECHILD (one-shot)

1. reset signal counters
2. pm pm init
3. pm pm exit
4. pm pm waitpid
   - Expected: result2 equals `-ECHILD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_signal_counters()
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
pm.pm_exit(child_pid.to_u32(), 0)
pm.pm_waitpid(1, child_pid.to_u32())    # first reap
val result2 = pm.pm_waitpid(1, child_pid.to_u32())
expect(result2).to_equal(-ECHILD)
```

</details>

#### pm_waitpid with wrong parent returns -ECHILD

1. pm pm init
2. pm pm exit
   - Expected: result equals `-ECHILD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
pm.pm_exit(child_pid.to_u32(), 7)
# pid 2 is not the parent of child (parent is 1)
val result = pm.pm_waitpid(2, child_pid.to_u32())
expect(result).to_equal(-ECHILD)
```

</details>

#### pm_exit notifies parent via signal_deliver(SIGCHLD)

1. reset signal counters
2. pm pm init
3. pm pm exit
   - Expected: test_signal_deliver_last_signo equals `17)   # SIGCHLD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_signal_counters()
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
pm.pm_exit(child_pid.to_u32(), 0)
expect(test_signal_deliver_calls).to_be_greater_than(0)
expect(test_signal_deliver_last_signo).to_equal(17)   # SIGCHLD
```

</details>

### PmService kill and find

#### pm_kill on unknown pid returns -ESRCH

1. reset signal counters
2. pm pm init
   - Expected: result equals `-ESRCH`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_signal_counters()
val pm = PmService.new()
pm.pm_init()
val result = pm.pm_kill(9999, 9)
expect(result).to_equal(-ESRCH)
```

</details>

#### pm_kill on valid pid returns 0 and invokes signal_deliver

1. reset signal counters
2. pm pm init
   - Expected: result equals `0`
   - Expected: test_signal_deliver_calls equals `1`
   - Expected: test_signal_deliver_last_pid equals `1`
   - Expected: test_signal_deliver_last_signo equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
reset_signal_counters()
val pm = PmService.new()
pm.pm_init()
val result = pm.pm_kill(1, 9)
expect(result).to_equal(0)
expect(test_signal_deliver_calls).to_equal(1)
expect(test_signal_deliver_last_pid).to_equal(1)
expect(test_signal_deliver_last_signo).to_equal(9)
```

</details>

#### pm_find_entity round-trips pid to entity to pid

1. pm pm init
   - Expected: e.is_null() is false
   - Expected: pid_back equals `child_pid.to_u32()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val child_pid = pm.pm_fork(1)
val e = pm.pm_find_entity(child_pid.to_u32())
expect(e.is_null()).to_equal(false)
val pid_back = pm.pm_get_pid(e.id)
expect(pid_back).to_equal(child_pid.to_u32())
```

</details>

#### pm_find_entity for unknown pid returns null entity

1. pm pm init
   - Expected: e.is_null() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pm = PmService.new()
pm.pm_init()
val e = pm.pm_find_entity(9999)
expect(e.is_null()).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 17 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
