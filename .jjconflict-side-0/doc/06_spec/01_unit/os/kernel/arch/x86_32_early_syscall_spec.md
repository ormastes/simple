# X86 32 Early Syscall Specification

> _Hosted coverage for the i386 live boot syscall subset._

<!-- sdn-diagram:id=x86_32_early_syscall_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_32_early_syscall_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_32_early_syscall_spec -> std
x86_32_early_syscall_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_32_early_syscall_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Early Syscall Specification

## Scenarios

### x86_32 freestanding early syscall ABI
_Hosted coverage for the i386 live boot syscall subset._

#### handles process, brk, reboot, diagnostics, and shell smoke syscalls

1. x86 32 install early syscall runtime
   - Expected: pid equals `1001`
   - Expected: x86_32_dispatch_installed_syscall_abi(15u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `1`
   - Expected: x86_32_dispatch_installed_syscall_abi(15u32, 0x30001000u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `1`
   - Expected: x86_32_dispatch_installed_syscall_abi(16u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `0`
   - Expected: x86_32_dispatch_installed_syscall_abi(5u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `2`
   - Expected: x86_32_dispatch_installed_syscall_abi(6u32, pid as u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `0`
   - Expected: x86_32_dispatch_installed_syscall_abi(13u32, 4u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `1002`
   - Expected: x86_32_dispatch_installed_syscall_abi(99u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32) equals `-38`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
x86_32_install_early_syscall_runtime()

val pid = x86_32_dispatch_installed_syscall_abi(2u32, 0x1000u32, 0u32, 0u32, 0u32, 0u32, 0u32)
expect(pid).to_equal(1001)
expect(x86_32_dispatch_installed_syscall_abi(15u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(1)
expect(x86_32_dispatch_installed_syscall_abi(15u32, 0x30001000u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(1)
expect(x86_32_dispatch_installed_syscall_abi(16u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(0)
expect(x86_32_dispatch_installed_syscall_abi(5u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(2)
expect(x86_32_dispatch_installed_syscall_abi(6u32, pid as u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(0)
expect(x86_32_dispatch_installed_syscall_abi(13u32, 4u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(1002)
expect(x86_32_dispatch_installed_syscall_abi(99u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32)).to_equal(-38)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_32_early_syscall_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_32 freestanding early syscall ABI

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
