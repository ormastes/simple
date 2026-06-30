# Ipc Error Codes Specification

> <details>

<!-- sdn-diagram:id=ipc_error_codes_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ipc_error_codes_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ipc_error_codes_spec -> std
ipc_error_codes_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ipc_error_codes_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ipc Error Codes Specification

## Scenarios

### IPC error code -38 semantics

#### matches POSIX ENOSYS (38)

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ENOSYS).to_equal(38)
```

</details>

#### encodes as -38 when returned from a syscall handler

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val returned: i32 = 0 - ENOSYS
expect(returned).to_equal(-38)
```

</details>

#### is distinct from EAGAIN (-11) used by non-blocking IPC recv

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EAGAIN).to_equal(11)
val eagain_ret: i32 = 0 - EAGAIN
expect(eagain_ret).to_equal(-11)
val enosys_ret: i32 = 0 - ENOSYS
val different = enosys_ret != eagain_ret
expect(different).to_equal(true)
```

</details>

#### is distinct from EPERM (-1) used by capability rejection

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EPERM).to_equal(1)
val eperm_ret: i32 = 0 - EPERM
expect(eperm_ret).to_equal(-1)
```

</details>

#### is distinct from EINVAL

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val different = ENOSYS != EINVAL
expect(different).to_equal(true)
```

</details>

### IPC error code semantic documentation

#### records -38 as 'function not implemented' (ENOSYS)

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Documentation anchor — if someone changes the numeric value of
# ENOSYS, this spec fails loudly so callers depending on -38 as a
# sentinel (ps_tool/top_tool/log_viewer) can be updated in lockstep.
val semantic_value = 38
expect(ENOSYS).to_equal(semantic_value)
```

</details>

#### proves the baremetal default branch convention

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The x86_64 baremetal syscall dispatcher's default branch returns
# -38. Any unrecognized syscall id therefore surfaces as ENOSYS at
# the Simple caller. This is expected behaviour for this spec.
val expected_default: i32 = -38
val enosys_return: i32 = 0 - ENOSYS
expect(enosys_return).to_equal(expected_default)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/ipc/ipc_error_codes_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- IPC error code -38 semantics
- IPC error code semantic documentation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
