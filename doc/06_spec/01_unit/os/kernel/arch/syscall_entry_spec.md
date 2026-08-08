# Syscall Entry Specification

> <details>

<!-- sdn-diagram:id=syscall_entry_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=syscall_entry_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

syscall_entry_spec -> std
syscall_entry_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=syscall_entry_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Syscall Entry Specification

## Scenarios

### kernel.arch.x86_64 SYSCALL trampoline wiring

#### exposes the trampoline address helper

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Call it twice — the contract is "callable without error AND
# deterministic"; link-time presence is verified at kernel build.
val a: u64 = kernel_syscall_entry_addr()
val b: u64 = kernel_syscall_entry_addr()
expect(a).to_equal(b)
```

</details>

#### install_syscall_entry is idempotent

1. install syscall entry
2. install syscall entry
3. install syscall entry
   - Expected: syscall_entry_installed() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
install_syscall_entry()
install_syscall_entry()
install_syscall_entry()
expect(syscall_entry_installed()).to_equal(true)
```

</details>

#### documents EFER_SCE as bit 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(EFER_SCE).to_equal(0x1)
```

</details>

#### documents SYSCALL_FMASK_IF as RFLAGS bit 9

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(SYSCALL_FMASK_IF).to_equal(0x200)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/syscall_entry_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- kernel.arch.x86_64 SYSCALL trampoline wiring

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
