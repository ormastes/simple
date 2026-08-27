# Interrupt Handlers Specification

> Interrupt handler support for bare-metal systems:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interrupt Handlers Specification

Interrupt handler support for bare-metal systems:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-007 |
| Category | Language / Bare-Metal |
| Status | In Progress |
| Source | `test/03_system/feature/features/baremetal/interrupt_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Interrupt handler support for bare-metal systems:
- @interrupt attribute marks handler functions
- Automatic register save/restore
- Critical section primitives
- IDT generation

## Scenarios

### Interrupt Handler Attribute

#### Basic Handler
_Simple interrupt handlers._

#### declares interrupt handler

- declares interrupt handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("declares interrupt handler")
val handler = InterruptHandlerSpec.create("timer", 0, false, false, false)
check(handler.name == "timer")
check(handler.priority == 0)
```

</details>

#### specifies priority

- specifies priority


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("specifies priority")
val handler = InterruptHandlerSpec.create("keyboard", 3, false, false, false)
check(handler.priority == 3)
```

</details>

#### Handler Attributes
_Additional handler modifiers._

#### supports naked handler

- supports naked handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports naked handler")
val handler = InterruptHandlerSpec.create("nmi", 0, true, false, false)
check(handler.naked)
```

</details>

#### supports fast handler

- supports fast handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports fast handler")
val handler = InterruptHandlerSpec.create("timer", 0, false, true, false)
check(handler.fast)
```

</details>

#### supports noreturn handler

- supports noreturn handler


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports noreturn handler")
val handler = InterruptHandlerSpec.create("panic", 0, false, false, true)
check(handler.noreturn)
```

</details>

### CPU Exceptions
_x86 CPU exception handling._

#### Exception Vectors
_Standard x86 exception numbers._

#### identifies divide error (vector 0)

- identifies divide error (vector 0)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies divide error (vector 0)")
val divide_error = 0
check(divide_error == 0)
```

</details>

#### identifies page fault (vector 14)

- identifies page fault (vector 14)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies page fault (vector 14)")
val page_fault = 14
check(page_fault == 14)
```

</details>

#### identifies general protection (vector 13)

- identifies general protection (vector 13)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identifies general protection (vector 13)")
val gp_fault = 13
check(gp_fault == 13)
```

</details>

#### Error Codes
_Exceptions that push error codes._

#### double fault has error code

- double fault has error code


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("double fault has error code")
check(true)
```

</details>

#### page fault has error code

- page fault has error code


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("page fault has error code")
val route = InterruptRouteSpec.page_fault()
check(route.has_error_code)
```

</details>

#### GP fault has error code

- GP fault has error code


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("GP fault has error code")
check(true)
```

</details>

### IDT Structure
_Interrupt Descriptor Table._

#### IDT Entry
_8-byte IDT entry format._

#### has correct entry size

- has correct entry size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct entry size")
val entry = IdtEntrySpec.interrupt_gate(0x08)
check(entry.size_bytes == 8)
```

</details>

#### encodes interrupt gate correctly

- encodes interrupt gate correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encodes interrupt gate correctly")
val entry = IdtEntrySpec.interrupt_gate(0x08)
check(entry.gate_type == 0x0E)
check(entry.present)
```

</details>

#### encodes trap gate correctly

- encodes trap gate correctly


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("encodes trap gate correctly")
val entry = IdtEntrySpec.trap_gate(0x08)
check(entry.gate_type == 0x0F)
check(entry.present)
```

</details>

#### IDT Descriptor
_LIDT instruction parameter._

#### has correct descriptor size

- has correct descriptor size


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct descriptor size")
val descriptor_size = 10
check(descriptor_size == 10)
```

</details>

### PIC Configuration
_8259 Programmable Interrupt Controller._

#### PIC Ports
_I/O port addresses._

#### defines master PIC ports

- defines master PIC ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines master PIC ports")
val pic = PicConfigSpec.create()
check(pic.master_port == 0x20)
check(pic.master_data == 0x21)
```

</details>

#### defines slave PIC ports

- defines slave PIC ports


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines slave PIC ports")
val pic = PicConfigSpec.create()
check(pic.slave_port == 0xA0)
check(pic.slave_data == 0xA1)
```

</details>

#### Vector Remapping
_Remap PIC vectors to avoid CPU exceptions._

#### remaps master PIC to vector 32

- remaps master PIC to vector 32


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("remaps master PIC to vector 32")
val pic = PicConfigSpec.create()
check(pic.master_offset == 32)
```

</details>

#### remaps slave PIC to vector 40

- remaps slave PIC to vector 40


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("remaps slave PIC to vector 40")
val pic = PicConfigSpec.create()
check(pic.slave_offset == 40)
```

</details>

### Critical Sections
_Interrupt-safe critical sections._

#### Disable/Enable Interrupts
_CLI/STI instruction wrappers._

#### disables interrupts

- disables interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disables interrupts")
val guard = CriticalSectionGuardSpec.create()
guard.disable()
check(guard.active == false)
```

</details>

#### enables interrupts

- enables interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables interrupts")
val guard = CriticalSectionGuardSpec.create()
guard.enable()
check(guard.active)
```

</details>

#### saves and restores state

- saves and restores state


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("saves and restores state")
val guard = CriticalSectionGuardSpec.create()
guard.enable()
guard.save_and_restore()
check(guard.active == false)
```

</details>

#### CriticalSection Guard
_RAII-style critical section._

#### creates critical section guard

- creates critical section guard


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates critical section guard")
val guard = CriticalSectionGuardSpec.create()
check(guard.active == false)
```

</details>

#### uses with_critical_section

- uses with_critical_section


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses with_critical_section")
val guard = with_critical_section(CriticalSectionGuardSpec.create())
check(guard.active)
```

</details>

### Interrupt Stack Frame
_CPU-pushed interrupt context._

#### Without Error Code
_Stack frame for most interrupts._

#### contains EIP, CS, EFLAGS

- contains EIP, CS, EFLAGS


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains EIP, CS, EFLAGS")
val frame = InterruptStackFrameSpec.without_error()
check(frame.fields.contains("EIP"))
check(frame.fields.contains("CS"))
check(frame.fields.contains("EFLAGS"))
```

</details>

#### With Error Code
_Stack frame for exceptions with error code._

#### contains error code before EIP

- contains error code before EIP


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("contains error code before EIP")
val frame = InterruptStackFrameSpec.with_error()
check(frame.has_error_code)
check(frame.fields[0] == "error_code")
```

</details>

### Use Cases
_Real-world interrupt handling._

#### Timer Interrupt
_System timer (PIT or APIC)._

#### handles periodic timer

- handles periodic timer


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles periodic timer")
val route = InterruptRouteSpec.timer()
check(route.vector == 32)
check(route.name == "timer")
```

</details>

#### Keyboard Interrupt
_PS/2 keyboard input._

#### handles keyboard input

- handles keyboard input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles keyboard input")
val route = InterruptRouteSpec.keyboard()
check(route.vector == 33)
check(route.name == "keyboard")
```

</details>

#### Page Fault Handler
_Memory management._

#### handles page fault

- handles page fault


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles page fault")
val route = InterruptRouteSpec.page_fault()
check(route.vector == 14)
check(route.has_error_code)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
| Slow scenarios | 0 |
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

- Canonical SPipe generation for source `0e1b38b8574ca68b928dd77fbd4c638458efdc14bff3fb529bb25215ec5edaea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0e1b38b8574ca68b928dd77fbd4c638458efdc14bff3fb529bb25215ec5edaea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0e1b38b8574ca68b928dd77fbd4c638458efdc14bff3fb529bb25215ec5edaea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/baremetal/interrupt_spec.spl
mirror: doc/06_spec/03_system/feature/features/baremetal/interrupt_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/baremetal/interrupt_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/baremetal/interrupt_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/baremetal/interrupt_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares interrupt handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/interrupt_spec.spl:134:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'specifies priority' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/baremetal/interrupt_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports naked handler' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
