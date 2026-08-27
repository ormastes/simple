# Daemon Sdk Lock System Specification

> Tests covering DaemonLock System, real lock acquisition, stale lock detection, lock release, reacquisition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Daemon Sdk Lock System Specification

## Scenarios

### DaemonLock System

### real lock acquisition

#### acquires lock with our PID

- acquires lock with our PID
   - Expected: pid equals `our_pid`
   - Expected: rt_file_exists(lock_get_file()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("acquires lock with our PID")
lock_sys_setup()
val pid = lock_acquire()
val our_pid = rt_getpid()
expect(pid).to_equal(our_pid)
expect(rt_file_exists(lock_get_file())).to_equal(true)
lock_sys_cleanup()
```

</details>

#### writes correct PID to lock file

- writes correct PID to lock file
   - Expected: stored_pid equals `our_pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("writes correct PID to lock file")
lock_sys_setup()
lock_acquire()
val stored_pid = lock_read_pid()
val our_pid = rt_getpid()
expect(stored_pid).to_equal(our_pid)
lock_sys_cleanup()
```

</details>

#### detects our own process as alive

- detects our own process as alive
   - Expected: rt_process_exists(our_pid) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects our own process as alive")
if _can_run:
    lock_sys_setup()
    val our_pid = rt_getpid()
    expect(rt_process_exists(our_pid)).to_equal(true)
    lock_sys_cleanup()
else:
    print "SKIP: rt_process_exists() not available"
```

</details>

### stale lock detection

#### detects stale lock from dead PID

- detects stale lock from dead PID
   - Expected: lock_is_running() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects stale lock from dead PID")
lock_sys_setup()
# PID 99999999 almost certainly doesn't exist
lock_write(99999999)
# On Windows rt_process_exists may behave differently for invalid PIDs
if not _is_windows:
    expect(lock_is_running()).to_equal(false)
lock_sys_cleanup()
```

</details>

#### acquires over stale lock

- acquires over stale lock
   - Expected: pid equals `our_pid`
   - Expected: lock_read_pid() equals `our_pid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("acquires over stale lock")
lock_sys_setup()
lock_write(99999999)
# On Windows rt_process_exists may report invalid PIDs differently
if not _is_windows:
    val pid = lock_acquire()
    val our_pid = rt_getpid()
    expect(pid).to_equal(our_pid)
    expect(lock_read_pid()).to_equal(our_pid)
lock_sys_cleanup()
```

</details>

#### detects our own lock as active

- detects our own lock as active
   - Expected: lock_is_running() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects our own lock as active")
if _can_run:
    lock_sys_setup()
    lock_acquire()
    expect(lock_is_running()).to_equal(true)
    lock_sys_cleanup()
else:
    print "SKIP: rt_process_exists() not available"
```

</details>

### lock release

#### releases and removes lock file

- releases and removes lock file
   - Expected: rt_file_exists(lock_get_file()) is true
   - Expected: ok is true
   - Expected: rt_file_exists(lock_get_file()) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("releases and removes lock file")
lock_sys_setup()
val pid = lock_acquire()
expect(rt_file_exists(lock_get_file())).to_equal(true)
val ok = lock_release(pid)
expect(ok).to_equal(true)
expect(rt_file_exists(lock_get_file())).to_equal(false)
lock_sys_cleanup()
```

</details>

#### refuses release with wrong PID

- refuses release with wrong PID
   - Expected: ok is false
   - Expected: rt_file_exists(lock_get_file()) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("refuses release with wrong PID")
lock_sys_setup()
lock_acquire()
val ok = lock_release(99999999)
expect(ok).to_equal(false)
expect(rt_file_exists(lock_get_file())).to_equal(true)
lock_sys_cleanup()
```

</details>

### reacquisition

#### reacquires after release

- reacquires after release
   - Expected: pid2 equals `pid1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reacquires after release")
lock_sys_setup()
val pid1 = lock_acquire()
lock_release(pid1)
val pid2 = lock_acquire()
expect(pid2).to_equal(pid1)
lock_sys_cleanup()
```

</details>

#### blocks reacquisition when held

- blocks reacquisition when held
   - Expected: pid2 equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("blocks reacquisition when held")
if _can_run:
    lock_sys_setup()
    lock_acquire()
    # Our own process holds the lock, so re-acquire should fail
    val pid2 = lock_acquire()
    expect(pid2).to_equal(-1)
    lock_sys_cleanup()
else:
    print "SKIP: rt_process_exists() not available"
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DaemonLock System, real lock acquisition, stale lock detection, lock release, reacquisition.
- DaemonLock System
- real lock acquisition
- stale lock detection
- lock release
- reacquisition

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `11b7f415dd8b1838db74f5d550253f0472ff93a376f2688d6f95a975f0cb70e6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `11b7f415dd8b1838db74f5d550253f0472ff93a376f2688d6f95a975f0cb70e6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `11b7f415dd8b1838db74f5d550253f0472ff93a376f2688d6f95a975f0cb70e6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.spl
mirror: doc/06_spec/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.spl:119:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'acquires lock with our PID' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes correct PID to lock file' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/daemon_sdk/daemon_sdk_lock_system_spec.spl:139:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects our own process as alive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
