# Syscall Number Consistency Specification

> Drift detector for the `SYS_IPC_*` constants duplicated across the kernel syscall dispatcher (`src/os/kernel/ipc/syscall.spl`) and every userland service that dispatches IPC syscalls (`wm_service`, `launcher`, `vfs`, `driver_supervisor`, `device_registry`, `netstack`, `userlib/window`, etc.).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 38 | 38 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Number Consistency Specification

Drift detector for the `SYS_IPC_*` constants duplicated across the kernel syscall dispatcher (`src/os/kernel/ipc/syscall.spl`) and every userland service that dispatches IPC syscalls (`wm_service`, `launcher`, `vfs`, `driver_supervisor`, `device_registry`, `netstack`, `userlib/window`, etc.).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #OS-006 |
| Category | Runtime |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | doc/01_research/local/ipc_error_38_2026-04-13.md |
| Source | `test/unit/os/kernel/ipc/syscall_number_consistency_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Drift detector for the `SYS_IPC_*` constants duplicated across the kernel
syscall dispatcher (`src/os/kernel/ipc/syscall.spl`) and every userland
service that dispatches IPC syscalls (`wm_service`, `launcher`, `vfs`,
`driver_supervisor`, `device_registry`, `netstack`, `userlib/window`, etc.).

The kernel dispatcher in `src/os/kernel/ipc/syscall.spl` is the canonical
source of truth:

    case 20: IpcSend         -> _handle_ipc_send
    case 21: IpcRecv         -> _handle_ipc_recv
    case 22: IpcCreatePort   -> _handle_ipc_create_port
    case 23: IpcConnect      -> _handle_ipc_connect

Historically several service modules declared `SYS_IPC_SEND = 23`, which
actually routed send traffic to the kernel's `IpcConnect` handler. This
spec asserts the canonical values and exists purely to prevent future
drift — if you change a `SYS_IPC_*` constant in any service, you must
update this spec (and the kernel dispatcher) to match.

## Scenarios

### SYS_IPC_* constant consistency across kernel and services

### kernel canonical values

#### SYS_IPC_SEND is 20

- SYS_IPC_SEND is 20
   - Expected: CANONICAL_SYS_IPC_SEND equals `20 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_IPC_SEND is 20")
expect(CANONICAL_SYS_IPC_SEND).to_equal(20 as u64)
```

</details>

#### SYS_IPC_RECV is 21

- SYS_IPC_RECV is 21
   - Expected: CANONICAL_SYS_IPC_RECV equals `21 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_IPC_RECV is 21")
expect(CANONICAL_SYS_IPC_RECV).to_equal(21 as u64)
```

</details>

#### SYS_IPC_CREATE_PORT is 22

- SYS_IPC_CREATE_PORT is 22
   - Expected: CANONICAL_SYS_IPC_CREATE_PORT equals `22 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_IPC_CREATE_PORT is 22")
expect(CANONICAL_SYS_IPC_CREATE_PORT).to_equal(22 as u64)
```

</details>

#### SYS_IPC_CONNECT is 23

- SYS_IPC_CONNECT is 23
   - Expected: CANONICAL_SYS_IPC_CONNECT equals `23 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_IPC_CONNECT is 23")
expect(CANONICAL_SYS_IPC_CONNECT).to_equal(23 as u64)
```

</details>

#### SYS_IPC_PORT_OWNER is 19

- SYS_IPC_PORT_OWNER is 19
   - Expected: CANONICAL_SYS_IPC_PORT_OWNER equals `19 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_IPC_PORT_OWNER is 19")
expect(CANONICAL_SYS_IPC_PORT_OWNER).to_equal(19 as u64)
```

</details>

#### SYS_BRK is 15

- SYS_BRK is 15
   - Expected: CANONICAL_SYS_BRK equals `15 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_BRK is 15")
expect(CANONICAL_SYS_BRK).to_equal(15 as u64)
```

</details>

#### SYS_REBOOT is 16

- SYS_REBOOT is 16
   - Expected: CANONICAL_SYS_REBOOT equals `16 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_REBOOT is 16")
expect(CANONICAL_SYS_REBOOT).to_equal(16 as u64)
```

</details>

#### SYS_SLEEP is 51

- SYS_SLEEP is 51
   - Expected: CANONICAL_SYS_SLEEP equals `51 as u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SYS_SLEEP is 51")
expect(CANONICAL_SYS_SLEEP).to_equal(51 as u64)
```

</details>

### wm_service matches kernel

#### wm SYS_IPC_SEND == canonical

- wm SYS_IPC_SEND == canonical
   - Expected: WM_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wm SYS_IPC_SEND == canonical")
expect(WM_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### wm SYS_IPC_RECV == canonical

- wm SYS_IPC_RECV == canonical
   - Expected: WM_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wm SYS_IPC_RECV == canonical")
expect(WM_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### wm SYS_IPC_CREATE_PORT == canonical

- wm SYS_IPC_CREATE_PORT == canonical
   - Expected: WM_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wm SYS_IPC_CREATE_PORT == canonical")
expect(WM_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### wm SYS_IPC_CONNECT == canonical

- wm SYS_IPC_CONNECT == canonical
   - Expected: WM_CONNECT equals `CANONICAL_SYS_IPC_CONNECT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wm SYS_IPC_CONNECT == canonical")
expect(WM_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### launcher matches kernel

#### launcher SYS_IPC_SEND == canonical

- launcher SYS_IPC_SEND == canonical
   - Expected: LAUNCHER_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("launcher SYS_IPC_SEND == canonical")
expect(LAUNCHER_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### launcher SYS_IPC_RECV == canonical

- launcher SYS_IPC_RECV == canonical
   - Expected: LAUNCHER_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("launcher SYS_IPC_RECV == canonical")
expect(LAUNCHER_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### launcher SYS_IPC_CREATE_PORT == canonical

- launcher SYS_IPC_CREATE_PORT == canonical
   - Expected: LAUNCHER_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("launcher SYS_IPC_CREATE_PORT == canonical")
expect(LAUNCHER_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### launcher SYS_IPC_CONNECT == canonical

- launcher SYS_IPC_CONNECT == canonical
   - Expected: LAUNCHER_CONNECT equals `CANONICAL_SYS_IPC_CONNECT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("launcher SYS_IPC_CONNECT == canonical")
expect(LAUNCHER_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### vfs_service matches kernel

#### vfs SYS_IPC_SEND == canonical

- vfs SYS_IPC_SEND == canonical
   - Expected: VFS_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vfs SYS_IPC_SEND == canonical")
expect(VFS_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### vfs SYS_IPC_RECV == canonical

- vfs SYS_IPC_RECV == canonical
   - Expected: VFS_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vfs SYS_IPC_RECV == canonical")
expect(VFS_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### vfs SYS_IPC_CREATE_PORT == canonical

- vfs SYS_IPC_CREATE_PORT == canonical
   - Expected: VFS_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vfs SYS_IPC_CREATE_PORT == canonical")
expect(VFS_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### vfs SYS_IPC_CONNECT == canonical

- vfs SYS_IPC_CONNECT == canonical
   - Expected: VFS_CONNECT equals `CANONICAL_SYS_IPC_CONNECT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("vfs SYS_IPC_CONNECT == canonical")
expect(VFS_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### netstack matches kernel

#### netstack SYS_IPC_SEND == canonical

- netstack SYS_IPC_SEND == canonical
   - Expected: NETSTACK_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("netstack SYS_IPC_SEND == canonical")
expect(NETSTACK_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### netstack SYS_IPC_RECV == canonical

- netstack SYS_IPC_RECV == canonical
   - Expected: NETSTACK_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("netstack SYS_IPC_RECV == canonical")
expect(NETSTACK_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### netstack SYS_IPC_CREATE_PORT == canonical

- netstack SYS_IPC_CREATE_PORT == canonical
   - Expected: NETSTACK_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("netstack SYS_IPC_CREATE_PORT == canonical")
expect(NETSTACK_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

### driver_supervisor matches kernel

#### supervisor SYS_IPC_SEND == canonical

- supervisor SYS_IPC_SEND == canonical
   - Expected: SUPERVISOR_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supervisor SYS_IPC_SEND == canonical")
expect(SUPERVISOR_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### supervisor SYS_IPC_RECV == canonical

- supervisor SYS_IPC_RECV == canonical
   - Expected: SUPERVISOR_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supervisor SYS_IPC_RECV == canonical")
expect(SUPERVISOR_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### supervisor SYS_IPC_CREATE_PORT == canonical

- supervisor SYS_IPC_CREATE_PORT == canonical
   - Expected: SUPERVISOR_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supervisor SYS_IPC_CREATE_PORT == canonical")
expect(SUPERVISOR_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### supervisor SYS_SLEEP == canonical

- supervisor SYS_SLEEP == canonical
   - Expected: SUPERVISOR_SLEEP equals `CANONICAL_SYS_SLEEP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supervisor SYS_SLEEP == canonical")
expect(SUPERVISOR_SLEEP).to_equal(CANONICAL_SYS_SLEEP)
```

</details>

### device_registry matches kernel

#### registry SYS_IPC_RECV == canonical

- registry SYS_IPC_RECV == canonical
   - Expected: REGISTRY_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registry SYS_IPC_RECV == canonical")
expect(REGISTRY_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### registry SYS_IPC_CREATE_PORT == canonical

- registry SYS_IPC_CREATE_PORT == canonical
   - Expected: REGISTRY_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("registry SYS_IPC_CREATE_PORT == canonical")
expect(REGISTRY_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

### userlib/window matches kernel

#### userlib SYS_IPC_SEND == canonical

- userlib SYS_IPC_SEND == canonical
   - Expected: USERLIB_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("userlib SYS_IPC_SEND == canonical")
expect(USERLIB_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### userlib SYS_IPC_RECV == canonical

- userlib SYS_IPC_RECV == canonical
   - Expected: USERLIB_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("userlib SYS_IPC_RECV == canonical")
expect(USERLIB_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### userlib SYS_IPC_CREATE_PORT == canonical

- userlib SYS_IPC_CREATE_PORT == canonical
   - Expected: USERLIB_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("userlib SYS_IPC_CREATE_PORT == canonical")
expect(USERLIB_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

#### userlib SYS_IPC_CONNECT == canonical

- userlib SYS_IPC_CONNECT == canonical
   - Expected: USERLIB_CONNECT equals `CANONICAL_SYS_IPC_CONNECT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("userlib SYS_IPC_CONNECT == canonical")
expect(USERLIB_CONNECT).to_equal(CANONICAL_SYS_IPC_CONNECT)
```

</details>

### driver_runtime matches kernel

#### driver runtime SYS_IPC_SEND == canonical

- driver runtime SYS_IPC_SEND == canonical
   - Expected: DRV_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driver runtime SYS_IPC_SEND == canonical")
expect(DRV_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### driver runtime SYS_IPC_RECV == canonical

- driver runtime SYS_IPC_RECV == canonical
   - Expected: DRV_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driver runtime SYS_IPC_RECV == canonical")
expect(DRV_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

#### driver runtime SYS_IPC_CREATE_PORT == canonical

- driver runtime SYS_IPC_CREATE_PORT == canonical
   - Expected: DRV_CREATE_PORT equals `CANONICAL_SYS_IPC_CREATE_PORT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("driver runtime SYS_IPC_CREATE_PORT == canonical")
expect(DRV_CREATE_PORT).to_equal(CANONICAL_SYS_IPC_CREATE_PORT)
```

</details>

### posix layer matches kernel

#### posix _SYS_IPC_SEND == canonical

- posix _SYS_IPC_SEND == canonical
   - Expected: POSIX_SEND equals `CANONICAL_SYS_IPC_SEND`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("posix _SYS_IPC_SEND == canonical")
expect(POSIX_SEND).to_equal(CANONICAL_SYS_IPC_SEND)
```

</details>

#### posix _SYS_IPC_RECV == canonical

- posix _SYS_IPC_RECV == canonical
   - Expected: POSIX_RECV equals `CANONICAL_SYS_IPC_RECV`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("posix _SYS_IPC_RECV == canonical")
expect(POSIX_RECV).to_equal(CANONICAL_SYS_IPC_RECV)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 38 |
| Active scenarios | 38 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Research:** `doc/01_research/local/ipc_error_38_2026-04-13.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68cf6a63207845f89162a44dd4e4113c6d2b948c59ef19f328b47aaea145c5ff`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68cf6a63207845f89162a44dd4e4113c6d2b948c59ef19f328b47aaea145c5ff`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68cf6a63207845f89162a44dd4e4113c6d2b948c59ef19f328b47aaea145c5ff`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/kernel/ipc/syscall_number_consistency_spec.spl
mirror: doc/06_spec/unit/os/kernel/ipc/syscall_number_consistency_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/kernel/ipc/syscall_number_consistency_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/kernel/ipc/syscall_number_consistency_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/kernel/ipc/syscall_number_consistency_spec.spl:122:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYS_IPC_SEND is 20' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/syscall_number_consistency_spec.spl:126:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYS_IPC_RECV is 21' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/kernel/ipc/syscall_number_consistency_spec.spl:130:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SYS_IPC_CREATE_PORT is 22' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
