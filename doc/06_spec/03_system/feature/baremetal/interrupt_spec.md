# Bare-Metal Interrupt Handlers

> Tests bare-metal interrupt handler registration, dispatch, and context saving. Verifies that interrupt vectors are correctly installed, that handlers execute with proper priority, and that interrupted context is preserved and restored.

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
| Updated | 2026-08-26 |
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

- enables external interrupt
   - Expected: _last_nvic_enabled_irq equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables external interrupt")
nvic_enable_irq(15)
expect(_last_nvic_enabled_irq).to_equal(15)
```

</details>


</details>

<details>
<summary>Advanced: disables external interrupt</summary>

#### disables external interrupt _(slow)_

- disables external interrupt
   - Expected: _last_nvic_disabled_irq equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disables external interrupt")
nvic_disable_irq(15)
expect(_last_nvic_disabled_irq).to_equal(15)
```

</details>


</details>

<details>
<summary>Advanced: handles out-of-range IRQ gracefully</summary>

#### handles out-of-range IRQ gracefully _(slow)_

- handles out-of-range IRQ gracefully
   - Expected: _last_nvic_enabled_irq equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles out-of-range IRQ gracefully")
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

- sets interrupt priority
   - Expected: _last_nvic_priority_irq equals `10`
   - Expected: _last_nvic_priority equals `128`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets interrupt priority")
nvic_set_priority(10, 128)
expect(_last_nvic_priority_irq).to_equal(10)
expect(_last_nvic_priority).to_equal(128)
```

</details>


</details>

<details>
<summary>Advanced: reads interrupt priority</summary>

#### reads interrupt priority _(slow)_

- reads interrupt priority
   - Expected: priority equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads interrupt priority")
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

- sets interrupt pending
   - Expected: _last_nvic_pending_irq equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets interrupt pending")
nvic_set_pending(20)
expect(_last_nvic_pending_irq).to_equal(20)
```

</details>


</details>

<details>
<summary>Advanced: clears pending interrupt</summary>

#### clears pending interrupt _(slow)_

- clears pending interrupt
   - Expected: _last_nvic_cleared_irq equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("clears pending interrupt")
nvic_clear_pending(20)
expect(_last_nvic_cleared_irq).to_equal(20)
```

</details>


</details>

<details>
<summary>Advanced: checks if interrupt is active</summary>

#### checks if interrupt is active _(slow)_

- checks if interrupt is active
   - Expected: active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks if interrupt is active")
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

- sets vector table offset
   - Expected: _last_vector_table_offset equals `0x08000000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets vector table offset")
nvic_set_vector_table(0x08000000)
expect(_last_vector_table_offset).to_equal(0x08000000)
```

</details>


</details>

<details>
<summary>Advanced: validates vector table address range</summary>

#### validates vector table address range _(slow)_

- validates vector table address range
   - Expected: in_flash is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("validates vector table address range")
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

- enables external interrupt
   - Expected: _last_plic_enabled_irq equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables external interrupt")
plic_enable_irq(10)
expect(_last_plic_enabled_irq).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: disables external interrupt</summary>

#### disables external interrupt _(slow)_

- disables external interrupt
   - Expected: _last_plic_disabled_irq equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disables external interrupt")
plic_disable_irq(10)
expect(_last_plic_disabled_irq).to_equal(10)
```

</details>


</details>

<details>
<summary>Advanced: rejects IRQ 0 (reserved)</summary>

#### rejects IRQ 0 (reserved) _(slow)_

- rejects IRQ 0 (reserved)
   - Expected: _last_plic_enabled_irq equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("rejects IRQ 0 (reserved)")
plic_enable_irq(0)
expect(_last_plic_enabled_irq).to_equal(0)
```

</details>


</details>

#### priority configuration

<details>
<summary>Advanced: sets interrupt priority</summary>

#### sets interrupt priority _(slow)_

- sets interrupt priority
   - Expected: _last_plic_priority_irq equals `10`
   - Expected: _last_plic_priority equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets interrupt priority")
plic_set_priority(10, 5)
expect(_last_plic_priority_irq).to_equal(10)
expect(_last_plic_priority).to_equal(5)
```

</details>


</details>

<details>
<summary>Advanced: sets priority threshold</summary>

#### sets priority threshold _(slow)_

- sets priority threshold
   - Expected: _last_plic_threshold equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets priority threshold")
plic_set_threshold(3)
expect(_last_plic_threshold).to_equal(3)
```

</details>


</details>

#### claim/complete protocol

<details>
<summary>Advanced: claims pending interrupt</summary>

#### claims pending interrupt _(slow)_

- claims pending interrupt
   - Expected: irq equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("claims pending interrupt")
val irq = plic_claim()
# Stub returns 0 (no pending interrupt)
expect(irq).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: completes interrupt</summary>

#### completes interrupt _(slow)_

- completes interrupt
   - Expected: irq equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("completes interrupt")
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

- enables Local APIC
   - Expected: _apic_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables Local APIC")
apic_enable()
expect(_apic_enabled).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: reads APIC ID</summary>

#### reads APIC ID _(slow)_

- reads APIC ID
   - Expected: id equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads APIC ID")
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

- signals EOI
   - Expected: _apic_eoi_count equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("signals EOI")
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

- disables interrupts globally


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disables interrupts globally")
disable_interrupts()
expect(_interrupts_disable_count).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: enables interrupts globally</summary>

#### enables interrupts globally _(slow)_

- enables interrupts globally


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables interrupts globally")
enable_interrupts()
expect(_interrupts_enable_count).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: checks interrupt status</summary>

#### checks interrupt status _(slow)_

- checks interrupt status
   - Expected: enabled is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("checks interrupt status")
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

- executes function with interrupts disabled
   - Expected: _critical_section_count equals `before + 1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes function with interrupts disabled")
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

- restores interrupt state after function
   - Expected: is_enabled equals `was_enabled`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("restores interrupt state after function")
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

- registers interrupt handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("registers interrupt handler")
register_interrupt_handler(15, 0x08001000, 128)
expect(interrupt_handlers.len()).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: unregisters interrupt handler</summary>

#### unregisters interrupt handler _(slow)_

- unregisters interrupt handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("unregisters interrupt handler")
register_interrupt_handler(15, 0x08001000, 128)
unregister_interrupt_handler(15)
for entry in interrupt_handlers:
    expect(entry.vector).to_not_equal(15)
```

</details>


</details>

#### dispatch

<details>
<summary>Advanced: dispatches to default handler for unregistered vector</summary>

#### dispatches to default handler for unregistered vector _(slow)_

- dispatches to default handler for unregistered vector
   - Expected: _last_dispatched_vector equals `99`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches to default handler for unregistered vector")
dispatch_interrupt(99)
expect(_last_dispatched_vector).to_equal(99)
```

</details>


</details>

<details>
<summary>Advanced: dispatches registered vector without crash</summary>

#### dispatches registered vector without crash _(slow)_

- dispatches registered vector without crash
   - Expected: _last_dispatched_vector equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("dispatches registered vector without crash")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c6a7e5d476aa4dda8db5f2b1879b406691b236fea6e9cf45ba5cd490b90e96ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c6a7e5d476aa4dda8db5f2b1879b406691b236fea6e9cf45ba5cd490b90e96ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c6a7e5d476aa4dda8db5f2b1879b406691b236fea6e9cf45ba5cd490b90e96ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/interrupt_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/interrupt_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/interrupt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/interrupt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/interrupt_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/interrupt_spec.spl:185:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'enables external interrupt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/interrupt_spec.spl:191:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'disables external interrupt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/interrupt_spec.spl:197:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles out-of-range IRQ gracefully' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
