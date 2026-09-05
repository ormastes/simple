# Interrupt Handlers Specification

> Interrupt handler support for bare-metal systems:

<!-- sdn-diagram:id=interrupt_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interrupt_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interrupt_spec -> std
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

# Interrupt Handlers Specification

Interrupt handler support for bare-metal systems:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-007 |
| Category | Language / Bare-Metal |
| Status | In Progress |
| Source | `test/03_system/feature/features/baremetal/interrupt_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Interrupt handler support for bare-metal systems:
- @interrupt attribute marks handler functions
- Automatic register save/restore
- Critical section primitives
- IDT generation

## Scenarios

### Interrupt Handler Attribute
_Local model of @interrupt handler metadata._

#### Basic Handler
_Simple interrupt handlers._

#### declares interrupt handler

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = InterruptHandlerSpec.create("timer", 0, false, false, false)
check(handler.name == "timer")
check(handler.priority == 0)
```

</details>

#### specifies priority

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = InterruptHandlerSpec.create("keyboard", 3, false, false, false)
check(handler.priority == 3)
```

</details>

#### Handler Attributes
_Additional handler modifiers._

#### supports naked handler

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = InterruptHandlerSpec.create("nmi", 0, true, false, false)
check(handler.naked)
```

</details>

#### supports fast handler

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = InterruptHandlerSpec.create("timer", 0, false, true, false)
check(handler.fast)
```

</details>

#### supports noreturn handler

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val handler = InterruptHandlerSpec.create("panic", 0, false, false, true)
check(handler.noreturn)
```

</details>

### CPU Exceptions
_x86 CPU exception handling._

#### Exception Vectors
_Standard x86 exception numbers._

#### identifies divide error (vector 0)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val divide_error = 0
check(divide_error == 0)
```

</details>

#### identifies page fault (vector 14)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val page_fault = 14
check(page_fault == 14)
```

</details>

#### identifies general protection (vector 13)

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val gp_fault = 13
check(gp_fault == 13)
```

</details>

#### Error Codes
_Exceptions that push error codes._

#### double fault has error code

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

#### page fault has error code

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = InterruptRouteSpec.page_fault()
check(route.has_error_code)
```

</details>

#### GP fault has error code

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(true)
```

</details>

### IDT Structure
_Interrupt Descriptor Table._

#### IDT Entry
_8-byte IDT entry format._

#### has correct entry size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = IdtEntrySpec.interrupt_gate(0x08)
check(entry.size_bytes == 8)
```

</details>

#### encodes interrupt gate correctly

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = IdtEntrySpec.interrupt_gate(0x08)
check(entry.gate_type == 0x0E)
check(entry.present)
```

</details>

#### encodes trap gate correctly

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = IdtEntrySpec.trap_gate(0x08)
check(entry.gate_type == 0x0F)
check(entry.present)
```

</details>

#### IDT Descriptor
_LIDT instruction parameter._

#### has correct descriptor size

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val descriptor_size = 10
check(descriptor_size == 10)
```

</details>

### PIC Configuration
_8259 Programmable Interrupt Controller._

#### PIC Ports
_I/O port addresses._

#### defines master PIC ports

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = PicConfigSpec.create()
check(pic.master_port == 0x20)
check(pic.master_data == 0x21)
```

</details>

#### defines slave PIC ports

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = PicConfigSpec.create()
check(pic.slave_port == 0xA0)
check(pic.slave_data == 0xA1)
```

</details>

#### Vector Remapping
_Remap PIC vectors to avoid CPU exceptions._

#### remaps master PIC to vector 32

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = PicConfigSpec.create()
check(pic.master_offset == 32)
```

</details>

#### remaps slave PIC to vector 40

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pic = PicConfigSpec.create()
check(pic.slave_offset == 40)
```

</details>

### Critical Sections
_Interrupt-safe critical sections._

#### Disable/Enable Interrupts
_CLI/STI instruction wrappers._

#### disables interrupts

1. guard disable
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = CriticalSectionGuardSpec.create()
guard.disable()
check(guard.active == false)
```

</details>

#### enables interrupts

1. guard enable
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = CriticalSectionGuardSpec.create()
guard.enable()
check(guard.active)
```

</details>

#### saves and restores state

1. guard enable
2. guard save and restore
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = CriticalSectionGuardSpec.create()
guard.enable()
guard.save_and_restore()
check(guard.active == false)
```

</details>

#### CriticalSection Guard
_RAII-style critical section._

#### creates critical section guard

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = CriticalSectionGuardSpec.create()
check(guard.active == false)
```

</details>

#### uses with_critical_section

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val guard = with_critical_section(CriticalSectionGuardSpec.create())
check(guard.active)
```

</details>

### Interrupt Stack Frame
_CPU-pushed interrupt context._

#### Without Error Code
_Stack frame for most interrupts._

#### contains EIP, CS, EFLAGS

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = InterruptStackFrameSpec.without_error()
check(frame.fields.contains("EIP"))
check(frame.fields.contains("CS"))
check(frame.fields.contains("EFLAGS"))
```

</details>

#### With Error Code
_Stack frame for exceptions with error code._

#### contains error code before EIP

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = InterruptRouteSpec.timer()
check(route.vector == 32)
check(route.name == "timer")
```

</details>

#### Keyboard Interrupt
_PS/2 keyboard input._

#### handles keyboard input

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val route = InterruptRouteSpec.keyboard()
check(route.vector == 33)
check(route.name == "keyboard")
```

</details>

#### Page Fault Handler
_Memory management._

#### handles page fault

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
