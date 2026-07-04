# X86 32 Trap Model Specification

> _Pure register marshalling contract for the future int 0x80 entry._

<!-- sdn-diagram:id=x86_32_trap_model_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_32_trap_model_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_32_trap_model_spec -> std
x86_32_trap_model_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_32_trap_model_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 32 Trap Model Specification

## Scenarios

### x86_32 trap model
_Pure register marshalling contract for the future int 0x80 entry._

#### marshals int 0x80 registers into syscall args

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val args = x86_32_syscall_args_from_context(make_context())
expect(args.id).to_equal(60)
expect(args.arg0).to_equal(10)
expect(args.arg1).to_equal(11)
expect(args.arg2).to_equal(12)
expect(args.arg3).to_equal(13)
expect(args.arg4).to_equal(14)
expect(args.arg5).to_equal(15)
```

</details>

#### applies syscall result to eax and advances past int 0x80

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val updated = x86_32_apply_syscall_result(make_context(), SyscallResult(value: 42))
expect(updated.eax).to_equal(42u32)
expect(updated.eip).to_equal(0x1000u32 + X86_32_INT80_SIZE)
expect(updated.esp).to_equal(0x9000u32)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/arch/x86_32_trap_model_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_32 trap model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
