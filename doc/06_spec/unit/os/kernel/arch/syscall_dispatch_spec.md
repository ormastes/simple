# Syscall Dispatch Specification

> Tests covering syscall dispatch numbers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Dispatch Specification

## Scenarios

### syscall dispatch numbers

#### core process syscalls have expected values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- core process syscalls have expected values


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("core process syscalls have expected values")
assert_equal(SYS_EXIT,           0)
assert_equal(SYS_YIELD,          1)
assert_equal(SYS_SPAWN,          2)
assert_equal(SYS_WAIT,           3)
assert_equal(SYS_GETPID,         4)
assert_equal(SYS_SPAWN_BINARY,   13)
```

</details>

#### SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct

- SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct")
assert_true(SYS_EXIT != SYS_YIELD)
assert_true(SYS_EXIT != SYS_SPAWN_BINARY)
assert_true(SYS_YIELD != SYS_SPAWN_BINARY)
```

</details>

#### memory syscalls are in the 10-12 range

- memory syscalls are in the 10-12 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("memory syscalls are in the 10-12 range")
assert_equal(SYS_MMAP,     10)
assert_equal(SYS_MUNMAP,   11)
assert_equal(SYS_MPROTECT, 12)
assert_true(SYS_MMAP < SYS_MUNMAP)
assert_true(SYS_MUNMAP < SYS_MPROTECT)
```

</details>

#### IPC syscalls start at 20

- IPC syscalls start at 20


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("IPC syscalls start at 20")
assert_equal(SYS_IPC_SEND,        20)
assert_equal(SYS_IPC_RECV,        21)
assert_equal(SYS_IPC_CREATE_PORT, 22)
assert_equal(SYS_IPC_CONNECT,     23)
```

</details>

#### file syscalls are in the 30-48 range

- file syscalls are in the 30-48 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("file syscalls are in the 30-48 range")
assert_equal(SYS_FILE_OPEN,  30)
assert_equal(SYS_FILE_READ,  31)
assert_equal(SYS_FILE_WRITE, 32)
assert_true(SYS_FILE_OPEN < SYS_FILE_WRITE)
assert_true(SYS_FILE_WRITE < SYS_CHDIR)
```

</details>

#### debug_write is 60

- debug_write is 60


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("debug_write is 60")
assert_equal(SYS_DEBUG_WRITE, 60)
```

</details>

#### POSIX libc syscall numbers are reserved

- POSIX libc syscall numbers are reserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("POSIX libc syscall numbers are reserved")
assert_equal(SYS_POSIX_PROC_CREATE, 57)
assert_equal(SYS_POSIX_IMAGE_RUN, 59)
assert_equal(SYS_POSIX_CHILD_WAIT, 61)
assert_equal(SYS_POSIX_PIPE_PAIR, 62)
assert_equal(SYS_POSIX_FD_DUP2, 63)
assert_equal(SYS_POSIX_FD_DUP, 64)
assert_equal(SYS_DLOPEN, 65)
assert_equal(SYS_DLSYM, 66)
assert_equal(SYS_DLCLOSE, 67)
assert_equal(SYS_POSIX_POLL, 68)
assert_equal(SYS_POSIX_FCNTL, 69)
assert_true(SYS_SLEEP < SYS_POSIX_PROC_CREATE)
assert_true(SYS_POSIX_IMAGE_RUN < SYS_DEBUG_WRITE)
assert_true(SYS_DEBUG_WRITE < SYS_POSIX_CHILD_WAIT)
assert_true(SYS_POSIX_FCNTL < SYS_NET_SOCKET)
```

</details>

#### network syscalls are in the 70-77 range

- network syscalls are in the 70-77 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("network syscalls are in the 70-77 range")
assert_equal(SYS_NET_SOCKET,    70)
assert_equal(SYS_NET_IF_CONFIG, 77)
assert_true(SYS_NET_SOCKET < SYS_NET_IF_CONFIG)
```

</details>

#### device syscalls are in the 80-85 range

- device syscalls are in the 80-85 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("device syscalls are in the 80-85 range")
assert_equal(SYS_DEV_ENUMERATE, 80)
assert_equal(SYS_FREE_DMA,      85)
assert_true(SYS_DEV_ENUMERATE < SYS_FREE_DMA)
```

</details>

#### log and sysinfo syscalls are in 90-97 range

- log and sysinfo syscalls are in 90-97 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("log and sysinfo syscalls are in 90-97 range")
assert_equal(SYS_LOG_WRITE,     90)
assert_equal(SYS_LOG_READ,      91)
assert_equal(SYS_SYSINFO,       95)
assert_equal(SYS_GET_HOSTNAME,  96)
assert_equal(SYS_SET_HOSTNAME,  97)
assert_true(SYS_LOG_WRITE < SYS_SYSINFO)
assert_true(SYS_GET_HOSTNAME != SYS_SET_HOSTNAME)
```

</details>

#### all primary syscall groups are non-overlapping

- all primary syscall groups are non-overlapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("all primary syscall groups are non-overlapping")
# process group max (13) < ipc group start (20)
assert_true(SYS_SPAWN_BINARY < SYS_IPC_SEND)
# ipc group max (29) < file group start (30)
assert_true(SYS_NOTIF_WAIT_ANY < SYS_FILE_OPEN)
# file group max (51) < debug (60)
assert_true(SYS_SLEEP < SYS_DEBUG_WRITE)
# debug (60) < net group start (70)
assert_true(SYS_DEBUG_WRITE < SYS_NET_SOCKET)
# net group max (77) < dev group start (80)
assert_true(SYS_NET_IF_CONFIG < SYS_DEV_ENUMERATE)
# dev group max (85) < log group start (90)
assert_true(SYS_FREE_DMA < SYS_LOG_WRITE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/kernel/arch/syscall_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering syscall dispatch numbers.
- syscall dispatch numbers

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f162692e11ed225a610ca13697d4aca83053f7249c128563cea3734387a7f96a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f162692e11ed225a610ca13697d4aca83053f7249c128563cea3734387a7f96a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f162692e11ed225a610ca13697d4aca83053f7249c128563cea3734387a7f96a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/arch/syscall_dispatch_spec.spl
mirror: doc/06_spec/unit/os/kernel/arch/syscall_dispatch_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/arch/syscall_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/arch/syscall_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/arch/syscall_dispatch_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'core process syscalls have expected values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/syscall_dispatch_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/arch/syscall_dispatch_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'memory syscalls are in the 10-12 range' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
