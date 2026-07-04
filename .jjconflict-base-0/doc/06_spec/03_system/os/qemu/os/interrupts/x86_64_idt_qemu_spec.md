# X86 64 Idt Qemu Specification

> <details>

<!-- sdn-diagram:id=x86_64_idt_qemu_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_64_idt_qemu_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_64_idt_qemu_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_64_idt_qemu_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X86 64 Idt Qemu Specification

## Scenarios

### x86_64 IDT Setup

<details>
<summary>Advanced: IDT initialized with 256 entries</summary>

#### IDT initialized with 256 entries _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("[IRQ]")
```

</details>


</details>

<details>
<summary>Advanced: interrupt controller enabled</summary>

#### interrupt controller enabled _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("Interrupts enabled")
```

</details>


</details>

<details>
<summary>Advanced: GDT and IDT both loaded</summary>

#### GDT and IDT both loaded _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if _can_run():
    val output = _run_qemu()
    expect(output).to_contain("[BOOT]")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/qemu/os/interrupts/x86_64_idt_qemu_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- x86_64 IDT Setup

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
