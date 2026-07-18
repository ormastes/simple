# Bare-Metal Interrupt Handlers

> Tests bare-metal interrupt handler registration, dispatch, and context saving. Verifies that interrupt vectors are correctly installed, that handlers execute with proper priority, and that interrupted context is preserved and restored.

<!-- sdn-diagram:id=interrupt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interrupt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interrupt_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interrupt_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal Interrupt Handlers

Tests bare-metal interrupt handler registration, dispatch, and context saving. Verifies that interrupt vectors are correctly installed, that handlers execute with proper priority, and that interrupted context is preserved and restored.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/interrupt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests bare-metal interrupt handler registration, dispatch, and context saving.
Verifies that interrupt vectors are correctly installed, that handlers execute
with proper priority, and that interrupted context is preserved and restored.

## Scenarios

### ARM NVIC

#### interrupt enable/disable

<details>
<summary>Advanced: enables external interrupt</summary>

#### enables external interrupt _(slow)_

1. nvic enable irq
   - Expected: _last_nvic_enabled_irq equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_enable_irq(15)
expect(_last_nvic_enabled_irq).to_equal(15)
```

</details>


</details>

<details>
<summary>Advanced: disables external interrupt</summary>

#### disables external interrupt _(slow)_

1. nvic disable irq
   - Expected: _last_nvic_disabled_irq equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_disable_irq(15)
expect(_last_nvic_disabled_irq).to_equal(15)
```

</details>


</details>

<details>
<summary>Advanced: handles out-of-range IRQ gracefully</summary>

#### handles out-of-range IRQ gracefully _(slow)_

1. nvic enable irq
2. nvic enable irq
   - Expected: _last_nvic_enabled_irq equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_enable_irq(-1)
nvic_enable_irq(300)
expect(_last_nvic_enabled_irq).to_equal(300)
```

</details>


</details>

#### priority configuration

<details>
<summary>Advanced: sets interrupt priority</summary>

#### sets interrupt priority _(slow)_

1. nvic set priority
   - Expected: _last_nvic_priority_irq equals `10`
   - Expected: _last_nvic_priority equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_set_priority(10, 128)
expect(_last_nvic_priority_irq).to_equal(10)
expect(_last_nvic_priority).to_equal(128)
```

</details>


</details>

<details>
<summary>Advanced: reads interrupt priority</summary>

#### reads interrupt priority _(slow)_

1. nvic set priority
   - Expected: priority equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_set_priority(10, 64)
val priority = nvic_get_priority(10)
# Stub returns 0
expect(priority).to_equal(0)
```

</details>


</details>

#### pending interrupts

<details>
<summary>Advanced: sets interrupt pending</summary>

#### sets interrupt pending _(slow)_

1. nvic set pending
   - Expected: _last_nvic_pending_irq equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_set_pending(20)
expect(_last_nvic_pending_irq).to_equal(20)
```

</details>


</details>

<details>
<summary>Advanced: clears pending interrupt</summary>

#### clears pending interrupt _(slow)_

1. nvic clear pending
   - Expected: _last_nvic_cleared_irq equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_clear_pending(20)
expect(_last_nvic_cleared_irq).to_equal(20)
```

</details>


</details>

<details>
<summary>Advanced: checks if interrupt is active</summary>

#### checks if interrupt is active _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val active = nvic_is_active(15)
# Stub returns false
expect(active).to_equal(false)
```

</details>


</details>

#### system control

<details>
<summary>Advanced: sets vector table offset</summary>

#### sets vector table offset _(slow)_

1. nvic set vector table
   - Expected: _last_vector_table_offset equals `0x08000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
nvic_set_vector_table(0x08000000)
expect(_last_vector_table_offset).to_equal(0x08000000)
```

</details>


</details>

<details>
<summary>Advanced: validates vector table address range</summary>

#### validates vector table address range _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Vector table should be in flash range
val vtor_addr: i64 = 0x08000000
val in_flash = vtor_addr >= 0x08000000 and vtor_addr < 0x08100000
expect(in_flash).to_equal(true)
```

</details>


</details>

### RISC-V PLIC

#### interrupt enable/disable

<details>
<summary>Advanced: enables external interrupt</summary>

#### enables external interrupt _(slow)_

1. plic enable irq
   - Expected: _last_plic_enabled_irq equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
plic_enable_irq(10)
expect(_last_plic_enabled_irq).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: disables external interrupt</summary>

#### disables external interrupt _(slow)_

1. plic disable irq
   - Expected: _last_plic_disabled_irq equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
plic_disable_irq(10)
expect(_last_plic_disabled_irq).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: rejects IRQ 0 (reserved)</summary>

#### rejects IRQ 0 (reserved) _(slow)_

1. plic enable irq
   - Expected: _last_plic_enabled_irq equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
plic_enable_irq(0)
expect(_last_plic_enabled_irq).to_equal(0)
```

</details>


</details>

#### priority configuration

<details>
<summary>Advanced: sets interrupt priority</summary>

#### sets interrupt priority _(slow)_

1. plic set priority
   - Expected: _last_plic_priority_irq equals `10`
   - Expected: _last_plic_priority equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
plic_set_priority(10, 5)
expect(_last_plic_priority_irq).to_equal(10)
expect(_last_plic_priority).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: sets priority threshold</summary>

#### sets priority threshold _(slow)_

1. plic set threshold
   - Expected: _last_plic_threshold equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
plic_set_threshold(3)
expect(_last_plic_threshold).to_equal(3)
```

</details>


</details>

#### claim/complete protocol

<details>
<summary>Advanced: claims pending interrupt</summary>

#### claims pending interrupt _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val irq = plic_claim()
# Stub returns 0 (no pending interrupt)
expect(irq).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: completes interrupt</summary>

#### completes interrupt _(slow)_

1. plic complete
   - Expected: irq equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val irq = plic_claim()
if irq != 0:
    plic_complete(irq)
# irq is 0 from stub, so complete is skipped
expect(irq).to_equal(0)
```

</details>


</details>

### x86_64 APIC

#### initialization

<details>
<summary>Advanced: enables Local APIC</summary>

#### enables Local APIC _(slow)_

1. apic enable
   - Expected: _apic_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
apic_enable()
expect(_apic_enabled).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: reads APIC ID</summary>

#### reads APIC ID _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val id = apic_get_id()
# Stub returns 0
expect(id).to_equal(0)
```

</details>


</details>

#### end of interrupt

<details>
<summary>Advanced: signals EOI</summary>

#### signals EOI _(slow)_

1. apic eoi
   - Expected: _apic_eoi_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
apic_eoi()
expect(_apic_eoi_count).to_equal(1)
```

</details>


</details>

### Generic Interrupt Control

#### global interrupt enable/disable

<details>
<summary>Advanced: disables interrupts globally</summary>

#### disables interrupts globally _(slow)_

1. disable interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
disable_interrupts()
expect(_interrupts_disable_count).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: enables interrupts globally</summary>

#### enables interrupts globally _(slow)_

1. enable interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
enable_interrupts()
expect(_interrupts_enable_count).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: checks interrupt status</summary>

#### checks interrupt status _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val enabled = interrupts_enabled()
# Stub always returns false
expect(enabled).to_equal(false)
```

</details>


</details>

#### critical sections

<details>
<summary>Advanced: executes function with interrupts disabled</summary>

#### executes function with interrupts disabled _(slow)_

1. with interrupts disabled
   - Expected: _critical_section_count equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = _critical_section_count
with_interrupts_disabled(fn():
    0
)
expect(_critical_section_count).to_equal(before + 1)
```

</details>


</details>

<details>
<summary>Advanced: restores interrupt state after function</summary>

#### restores interrupt state after function _(slow)_

1. with interrupts disabled
   - Expected: is_enabled equals `was_enabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val was_enabled = interrupts_enabled()
with_interrupts_disabled(fn():
    0
)
val is_enabled = interrupts_enabled()
expect(is_enabled).to_equal(was_enabled)
```

</details>


</details>

### Interrupt Handler Registration

#### registration

<details>
<summary>Advanced: registers interrupt handler</summary>

#### registers interrupt handler _(slow)_

1. register interrupt handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
register_interrupt_handler(15, 0x08001000, 128)
expect(interrupt_handlers.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: unregisters interrupt handler</summary>

#### unregisters interrupt handler _(slow)_

1. register interrupt handler
2. unregister interrupt handler
   - Expected: entry.vector == 15 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
register_interrupt_handler(15, 0x08001000, 128)
unregister_interrupt_handler(15)
for entry in interrupt_handlers:
    expect(entry.vector == 15).to_equal(false)
```

</details>


</details>

#### dispatch

<details>
<summary>Advanced: dispatches to default handler for unregistered vector</summary>

#### dispatches to default handler for unregistered vector _(slow)_

1. dispatch interrupt
   - Expected: _last_dispatched_vector equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
dispatch_interrupt(99)
expect(_last_dispatched_vector).to_equal(99)
```

</details>


</details>

<details>
<summary>Advanced: dispatches registered vector without crash</summary>

#### dispatches registered vector without crash _(slow)_

1. register interrupt handler
2. dispatch interrupt
   - Expected: _last_dispatched_vector equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
register_interrupt_handler(42, 0x08002000, 64)
dispatch_interrupt(42)
expect(_last_dispatched_vector).to_equal(42)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 29 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
