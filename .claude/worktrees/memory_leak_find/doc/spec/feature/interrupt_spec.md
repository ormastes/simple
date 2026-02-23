# Bare-Metal Interrupt Handler Tests

**Feature ID:** #BAREMETAL-008 | **Category:** Baremetal | **Status:** In Progress

_Source: `test/feature/baremetal/interrupt_spec.spl`_

---

## Overview

Tests interrupt controllers and exception handling across ARM NVIC, RISC-V PLIC, and
x86_64 APIC platforms. Validates interrupt enable/disable, priority configuration, pending
interrupt management, claim/complete protocol, global interrupt control, critical sections,
and interrupt handler registration and dispatch.

## Syntax

```simple
nvic_enable_irq(15)
nvic_set_priority(10, 128)
val priority = nvic_get_priority(10)

with_interrupts_disabled(fn():
    executed = true
)
expect(executed).to_equal(true)
```

---

## Test Summary

| Metric | Count |
|--------|-------|
| Tests | 29 |

## Test Structure

### ARM NVIC

#### interrupt enable/disable

- ✅ enables external interrupt
- ✅ disables external interrupt
- ✅ handles out-of-range IRQ gracefully
#### priority configuration

- ✅ sets interrupt priority
- ✅ reads interrupt priority
#### pending interrupts

- ✅ sets interrupt pending
- ✅ clears pending interrupt
- ✅ checks if interrupt is active
#### system control

- ✅ sets vector table offset
- ✅ triggers system reset
### RISC-V PLIC

#### interrupt enable/disable

- ✅ enables external interrupt
- ✅ disables external interrupt
- ✅ rejects IRQ 0 (reserved)
#### priority configuration

- ✅ sets interrupt priority
- ✅ sets priority threshold
#### claim/complete protocol

- ✅ claims pending interrupt
- ✅ completes interrupt
### x86_64 APIC

#### initialization

- ✅ enables Local APIC
- ✅ reads APIC ID
#### end of interrupt

- ✅ signals EOI
### Generic Interrupt Control

#### global interrupt enable/disable

- ✅ disables interrupts globally
- ✅ enables interrupts globally
- ✅ checks interrupt status
#### critical sections

- ✅ executes function with interrupts disabled
- ✅ restores interrupt state after function
### Interrupt Handler Registration

#### registration

- ✅ registers interrupt handler
- ✅ unregisters interrupt handler
#### dispatch

- ✅ calls registered handler
- ✅ calls default handler if no handler registered

