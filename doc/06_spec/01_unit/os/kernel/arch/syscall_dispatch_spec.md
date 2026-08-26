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

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("core process syscalls have expected values")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_EXIT,           0)
expect_eq(SYS_YIELD,          1)
expect_eq(SYS_SPAWN,          2)
expect_eq(SYS_WAIT,           3)
expect_eq(SYS_GETPID,         4)
expect_eq(SYS_SPAWN_BINARY,   13)
```

</details>

#### SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct

- SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("SYS_EXIT SYS_YIELD and SYS_SPAWN_BINARY are distinct")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_true(SYS_EXIT != SYS_YIELD)
expect_true(SYS_EXIT != SYS_SPAWN_BINARY)
expect_true(SYS_YIELD != SYS_SPAWN_BINARY)
```

</details>

#### memory syscalls are in the 10-12 range

- memory syscalls are in the 10-12 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("memory syscalls are in the 10-12 range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_MMAP,     10)
expect_eq(SYS_MUNMAP,   11)
expect_eq(SYS_MPROTECT, 12)
expect_true(SYS_MMAP < SYS_MUNMAP)
expect_true(SYS_MUNMAP < SYS_MPROTECT)
```

</details>

#### IPC syscalls start at 20

- IPC syscalls start at 20


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("IPC syscalls start at 20")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_IPC_SEND,        20)
expect_eq(SYS_IPC_RECV,        21)
expect_eq(SYS_IPC_CREATE_PORT, 22)
expect_eq(SYS_IPC_CONNECT,     23)
```

</details>

#### file syscalls are in the 30-48 range

- file syscalls are in the 30-48 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("file syscalls are in the 30-48 range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_FILE_OPEN,  30)
expect_eq(SYS_FILE_READ,  31)
expect_eq(SYS_FILE_WRITE, 32)
expect_true(SYS_FILE_OPEN < SYS_FILE_WRITE)
expect_true(SYS_FILE_WRITE < SYS_CHDIR)
```

</details>

#### debug_write is 60

- debug_write is 60


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("debug_write is 60")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_DEBUG_WRITE, 60)
```

</details>

#### POSIX libc syscall numbers are reserved

- POSIX libc syscall numbers are reserved


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("POSIX libc syscall numbers are reserved")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_POSIX_PROC_CREATE, 57)
expect_eq(SYS_POSIX_IMAGE_RUN, 59)
expect_eq(SYS_POSIX_CHILD_WAIT, 61)
expect_eq(SYS_POSIX_PIPE_PAIR, 62)
expect_eq(SYS_POSIX_FD_DUP2, 63)
expect_eq(SYS_POSIX_FD_DUP, 64)
expect_eq(SYS_DLOPEN, 65)
expect_eq(SYS_DLSYM, 66)
expect_eq(SYS_DLCLOSE, 67)
expect_eq(SYS_POSIX_POLL, 68)
expect_eq(SYS_POSIX_FCNTL, 69)
expect_true(SYS_SLEEP < SYS_POSIX_PROC_CREATE)
expect_true(SYS_POSIX_IMAGE_RUN < SYS_DEBUG_WRITE)
expect_true(SYS_DEBUG_WRITE < SYS_POSIX_CHILD_WAIT)
expect_true(SYS_POSIX_FCNTL < SYS_NET_SOCKET)
```

</details>

#### network syscalls are in the 70-77 range

- network syscalls are in the 70-77 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("network syscalls are in the 70-77 range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_NET_SOCKET,    70)
expect_eq(SYS_NET_IF_CONFIG, 77)
expect_true(SYS_NET_SOCKET < SYS_NET_IF_CONFIG)
```

</details>

#### device syscalls are in the 80-85 range

- device syscalls are in the 80-85 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("device syscalls are in the 80-85 range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_DEV_ENUMERATE, 80)
expect_eq(SYS_FREE_DMA,      85)
expect_true(SYS_DEV_ENUMERATE < SYS_FREE_DMA)
```

</details>

#### log and sysinfo syscalls are in 90-97 range

- log and sysinfo syscalls are in 90-97 range


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("log and sysinfo syscalls are in 90-97 range")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect_eq(SYS_LOG_WRITE,     90)
expect_eq(SYS_LOG_READ,      91)
expect_eq(SYS_SYSINFO,       95)
expect_eq(SYS_GET_HOSTNAME,  96)
expect_eq(SYS_SET_HOSTNAME,  97)
expect_true(SYS_LOG_WRITE < SYS_SYSINFO)
expect_true(SYS_GET_HOSTNAME != SYS_SET_HOSTNAME)
```

</details>

#### all primary syscall groups are non-overlapping

- all primary syscall groups are non-overlapping


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("all primary syscall groups are non-overlapping")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
# process group max (13) < ipc group start (20)
expect_true(SYS_SPAWN_BINARY < SYS_IPC_SEND)
# ipc group max (29) < file group start (30)
expect_true(SYS_NOTIF_WAIT_ANY < SYS_FILE_OPEN)
# file group max (51) < debug (60)
expect_true(SYS_SLEEP < SYS_DEBUG_WRITE)
# debug (60) < net group start (70)
expect_true(SYS_DEBUG_WRITE < SYS_NET_SOCKET)
# net group max (77) < dev group start (80)
expect_true(SYS_NET_IF_CONFIG < SYS_DEV_ENUMERATE)
# dev group max (85) < log group start (90)
expect_true(SYS_FREE_DMA < SYS_LOG_WRITE)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl` |
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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ec58270401bc792cb6bd3ee580407180b6a06f3101c613a65cb72bd60325716a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ec58270401bc792cb6bd3ee580407180b6a06f3101c613a65cb72bd60325716a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ec58270401bc792cb6bd3ee580407180b6a06f3101c613a65cb72bd60325716a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/arch/syscall_dispatch_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/os/kernel/arch/syscall_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/arch/syscall_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/arch/syscall_dispatch_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): no real executed assertion or compiler oracle
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
<!-- sspec-maintain:scorecard:end -->
