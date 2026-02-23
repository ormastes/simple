# Interrupt Handling: Configuration Design

**Date**: 2026-02-05
**Status**: Design
**Related**: `doc/design/baremetal_features_examples.md`, `doc/design/volatile_config_design.md`

---

## Overview

Interrupt handling requires configuring:
1. **Vector table** - Mapping interrupt numbers to handlers
2. **Priorities** - Interrupt priority levels
3. **Attributes** - Handler function properties (naked, fast, etc.)
4. **Critical sections** - Disabling interrupts safely

This document describes how to configure interrupts at multiple levels.

---

## Configuration Levels (Priority: High to Low)

| Level | Scope | Syntax | Use Case |
|-------|-------|--------|----------|
| **Function** | Single handler | `@interrupt(vector: N)` | Individual ISR |
| **Module** | All handlers in file | `__init__: interrupt_*` | Driver file settings |
| **Project** | All handlers | `simple.sdn [interrupt]` | Project-wide defaults |
| **Target** | Architecture defaults | `--target=cortex-m4` | MCU-specific |

---

## Level 1: Function-Level Interrupt

### Basic Interrupt Handler

```simple
# Simple interrupt handler
@interrupt(vector: 15)
fn systick_handler():
    tick_count += 1

# With priority
@interrupt(vector: 25, priority: 2)
fn uart_rx_handler():
    val byte = UART_DR
    rx_buffer.push(byte)

# With explicit attributes
@interrupt(vector: 16, priority: 0, attributes: [fast, noreturn])
fn dma_complete_handler():
    DMA_FLAG = 0
    signal_complete()
```

### Interrupt Attributes

| Attribute | Effect | Use Case |
|-----------|--------|----------|
| `fast` | Minimal prologue/epilogue | Time-critical ISR |
| `naked` | No prologue/epilogue | Assembly handlers |
| `noreturn` | Handler never returns | Fault handlers |
| `reentrant` | Can be interrupted | Long-running ISR |
| `nosave` | Don't save all registers | Optimization |

```simple
# Naked handler (pure assembly)
@interrupt(vector: 3)
@naked
fn hard_fault_handler():
    asm:
        "tst lr, #4"
        "ite eq"
        "mrseq r0, msp"
        "mrsne r0, psp"
        "b hard_fault_c_handler"

# Fast handler (minimal overhead)
@interrupt(vector: 15)
@fast
fn systick_fast():
    TICK_COUNT.fetch_add(1, Relaxed)

# Reentrant handler (can be preempted)
@interrupt(vector: 25, priority: 5)
@reentrant
fn slow_handler():
    # Lower priority interrupts can preempt
    process_large_buffer()
```

---

## Level 2: Module-Level Configuration (`__init__`)

### Default Settings for All Handlers in Module

```simple
# src/drivers/interrupts.spl
__init__:
    # Default priority for all handlers in this file
    interrupt_priority_default = 3

    # Default attributes
    interrupt_attributes_default = [fast]

    # Enable interrupt nesting
    interrupt_nesting = true

    # Critical section implementation
    critical_section_impl = "primask"   # or "basepri", "faultmask"

# Handlers inherit defaults
@interrupt(vector: 15)   # priority: 3 (from default), attributes: [fast]
fn systick_handler():
    tick_count += 1

@interrupt(vector: 25, priority: 1)   # priority: 1 (override), attributes: [fast]
fn high_priority_handler():
    urgent_task()

@interrupt(vector: 30, attributes: [])  # No attributes (override default)
fn normal_handler():
    normal_task()
```

### Module-Level Vector Table Section

```simple
# src/bsp/vectors.spl
__init__:
    # All handlers in this file go to .isr_vector section
    interrupt_section = ".isr_vector"

    # Vector table base address
    interrupt_vector_base = 0x08000000

    # Number of vectors
    interrupt_vector_count = 256

# Handlers automatically placed in vector table
@interrupt(vector: 0)
fn reset_handler():
    main()

@interrupt(vector: 1)
fn nmi_handler():
    loop: pass

@interrupt(vector: 2)
fn hard_fault_handler():
    loop: pass
```

### Interrupt Groups/Banks

```simple
# src/drivers/timer_interrupts.spl
__init__:
    # All handlers in this file are timer interrupts
    interrupt_group = "timer"
    interrupt_priority_default = 2

    # Timer-specific settings
    interrupt_timer_base_vector = 28

@interrupt(vector: 28)   # TIM1
fn tim1_handler():
    TIM1_SR = 0
    timer1_callback()

@interrupt(vector: 29)   # TIM2
fn tim2_handler():
    TIM2_SR = 0
    timer2_callback()

@interrupt(vector: 30)   # TIM3
fn tim3_handler():
    TIM3_SR = 0
    timer3_callback()
```

---

## Level 3: Project-Level Configuration (`simple.sdn`)

### Basic Project Configuration

```sdn
[interrupt]
# Default priority (0 = highest)
priority_default = 3

# Priority bits (MCU-specific)
priority_bits = 4           # 16 priority levels

# Subpriority bits
subpriority_bits = 0        # No subpriority

# Default attributes for all handlers
attributes_default = []

# Vector table settings
vector_table_size = 256
vector_table_section = ".isr_vector"
vector_table_align = 512    # Must be power of 2 >= size * 4

# Stack for interrupt handlers
interrupt_stack_size = 1024
use_separate_interrupt_stack = false
```

### Priority Groups

```sdn
[interrupt.priority_groups]
# Named priority groups
critical = 0
high = 1
medium = 2
low = 3
background = 4

# Default group
default_group = "medium"
```

```simple
# Usage in code
@interrupt(vector: 15, priority: "critical")
fn systick_handler():
    ...

@interrupt(vector: 25, priority: "low")
fn background_task():
    ...
```

### Vector Mapping

```sdn
[interrupt.vectors]
# Named vectors for readability
reset = 0
nmi = 1
hard_fault = 2
mem_manage = 3
bus_fault = 4
usage_fault = 5
svcall = 11
pendsv = 14
systick = 15

# Peripheral interrupts (MCU-specific)
wwdg = 16
pvd = 17
tamp_stamp = 18
rtc_wkup = 19
flash = 20
rcc = 21
exti0 = 22
exti1 = 23
exti2 = 24
# ...
```

```simple
# Usage with named vectors
@interrupt(vector: "systick")
fn systick_handler():
    ...

@interrupt(vector: "exti0", priority: "high")
fn button_handler():
    ...
```

### Interrupt Safety Settings

```sdn
[interrupt.safety]
# Require all handlers to be registered at compile time
static_registration_only = true

# Maximum interrupt disable time (debug check)
max_critical_section_cycles = 1000

# Require handlers to clear interrupt flags
require_flag_clear = true

# Stack overflow detection
stack_check = true
stack_canary = true
```

---

## Level 4: Target-Level Defaults

### Target-Specific Configuration

```sdn
[target.cortex-m0]
interrupt.priority_bits = 2
interrupt.vector_table_size = 48
interrupt.has_basepri = false

[target.cortex-m3]
interrupt.priority_bits = 4
interrupt.vector_table_size = 256
interrupt.has_basepri = true

[target.cortex-m4]
interrupt.priority_bits = 4
interrupt.vector_table_size = 256
interrupt.has_basepri = true
interrupt.has_fpu_regs = true

[target.cortex-m7]
interrupt.priority_bits = 4
interrupt.vector_table_size = 256
interrupt.has_basepri = true
interrupt.has_fpu_regs = true
interrupt.has_cache = true

[target.riscv32]
interrupt.mode = "vectored"    # or "direct"
interrupt.vector_table_size = 32
interrupt.mtvec_align = 64
```

---

## Critical Sections

### Basic Critical Section

```simple
fn critical_section<T>(f: fn() -> T) -> T:
    val state = interrupt_disable()
    val result = f()
    interrupt_restore(state)
    result

# Usage
fn update_shared_data():
    critical_section(||:
        shared_counter += 1
        shared_buffer.push(data)
    )
```

### Module-Level Critical Section Config

```simple
__init__:
    # Critical section implementation
    critical_section_impl = "primask"    # Disable all interrupts
    # critical_section_impl = "basepri"  # Disable below priority
    # critical_section_impl = "faultmask" # Disable all including faults

    # For basepri: minimum priority to disable
    critical_section_priority = 1        # Disable priority >= 1
```

### Critical Section Macros

```simple
# Scoped critical section
fn update_atomically():
    @critical:                 # Interrupts disabled in this block
        shared_data.value += 1
        shared_data.timestamp = get_time()
    # Interrupts automatically restored

# With priority threshold (basepri)
fn update_with_threshold():
    @critical(priority: 2):    # Only disable priority >= 2
        medium_priority_data += 1
    # High priority (0, 1) interrupts can still occur

# Named critical section for debugging
fn complex_update():
    @critical(name: "buffer_update"):
        buffer.push(item)
        buffer_count += 1
```

### Critical Section Assertions

```simple
__init__:
    critical_section_max_cycles = 500    # Debug: warn if exceeded

@critical
fn quick_update():
    # Debug mode: measures cycles, warns if > 500
    data += 1

# Static assertion
static assert quick_update.max_cycles <= 500, "Critical section too long"
```

---

## Interrupt Registration

### Static Registration (Compile-Time)

```simple
# Handlers registered at compile time via @interrupt attribute
@interrupt(vector: 15)
fn systick_handler():
    ...

# Compiler generates vector table entry
```

### Dynamic Registration (Runtime)

```simple
__init__:
    interrupt_dynamic_registration = true

# Register handler at runtime
fn setup_interrupts():
    interrupt_register(15, systick_handler)
    interrupt_set_priority(15, 0)
    interrupt_enable(15)

# Unregister handler
fn teardown_interrupts():
    interrupt_disable(15)
    interrupt_unregister(15)
```

### Mixed Registration

```simple
__init__:
    # Some vectors are static, some dynamic
    interrupt_static_vectors = [0..15]     # Core handlers static
    interrupt_dynamic_vectors = [16..255]  # Peripheral handlers dynamic
```

---

## Vector Table Generation

### Automatic Generation

```simple
# src/bsp/vectors.spl
__init__:
    interrupt_generate_vector_table = true
    interrupt_vector_section = ".isr_vector"
    interrupt_default_handler = "default_irq_handler"

# Default handler for unregistered interrupts
fn default_irq_handler():
    val vector = get_active_interrupt()
    panic("Unhandled interrupt: {vector}")

# Registered handlers
@interrupt(vector: 15)
fn systick_handler(): ...

@interrupt(vector: 25)
fn uart_handler(): ...

# Compiler generates:
# .isr_vector section with:
#   [0] = reset_handler (or default)
#   [1] = nmi_handler (or default)
#   ...
#   [15] = systick_handler
#   ...
#   [25] = uart_handler
#   [other] = default_irq_handler
```

### Manual Vector Table

```simple
__init__:
    interrupt_generate_vector_table = false

# Manually define vector table
@section(".isr_vector")
@align(512)
const VECTOR_TABLE: [fn(); 256] = [
    0: reset_handler,
    1: nmi_handler,
    2: hard_fault_handler,
    3..10: default_handler,
    11: svcall_handler,
    12..13: default_handler,
    14: pendsv_handler,
    15: systick_handler,
    16..255: default_handler,
]
```

---

## Complete Example

### Project Configuration (`simple.sdn`)

```sdn
[package]
name = "stm32f4-firmware"
target = "cortex-m4"

[interrupt]
priority_default = 3
priority_bits = 4
vector_table_size = 256
vector_table_section = ".isr_vector"
attributes_default = []

[interrupt.priority_groups]
critical = 0
high = 1
normal = 2
low = 3

[interrupt.vectors]
systick = 15
tim2 = 28
usart1 = 37
dma1_stream0 = 11

[interrupt.safety]
static_registration_only = true
require_flag_clear = true
```

### Module Configuration (`__init__`)

```simple
# src/drivers/timer/__init__.spl
__init__:
    interrupt_group = "timer"
    interrupt_priority_default = "normal"
    interrupt_attributes_default = [fast]
    critical_section_impl = "basepri"
    critical_section_priority = 1
```

### Interrupt Handlers

```simple
# src/drivers/timer/tim2.spl
# Inherits from __init__: priority="normal", attributes=[fast]

var tim2_ticks: u32 = 0
var tim2_callback: fn() = || ()

@interrupt(vector: "tim2")
fn tim2_handler():
    # Clear interrupt flag (required by safety settings)
    TIM2_SR = TIM2_SR & ~0x01

    tim2_ticks += 1
    tim2_callback()

fn tim2_init(prescaler: u16, period: u16):
    # Enable clock
    RCC_APB1ENR = RCC_APB1ENR | (1 << 0)

    # Configure timer
    TIM2_PSC = prescaler
    TIM2_ARR = period
    TIM2_DIER = 0x01    # Enable update interrupt

    # Enable interrupt in NVIC
    interrupt_enable("tim2")

    # Start timer
    TIM2_CR1 = 0x01

fn tim2_set_callback(cb: fn()):
    @critical:
        tim2_callback = cb
```

### System Tick Handler

```simple
# src/bsp/systick.spl
__init__:
    interrupt_priority_default = "critical"

var system_ticks: AtomicU32 = AtomicU32(0)

@interrupt(vector: "systick", priority: "critical")
@fast
fn systick_handler():
    system_ticks.fetch_add(1, Relaxed)

fn systick_init(ticks_per_second: u32):
    val reload = SYSTEM_CLOCK / ticks_per_second - 1
    SYST_RVR = reload
    SYST_CVR = 0
    SYST_CSR = 0x07    # Enable, interrupt, use processor clock

fn get_ticks() -> u32:
    system_ticks.load(Relaxed)

fn delay_ms(ms: u32):
    val start = get_ticks()
    while get_ticks() - start < ms:
        asm: "wfi"
```

### Main Application

```simple
# src/main.spl

import bsp.systick.{systick_init, delay_ms}
import drivers.timer.tim2.{tim2_init, tim2_set_callback}
import drivers.gpio.{gpio_init, gpio_toggle, GPIOA}

fn main():
    # Initialize system tick (1ms)
    systick_init(1000)

    # Initialize GPIO for LED
    gpio_init(GPIOA, 5, Output)

    # Initialize timer with callback
    tim2_init(8400 - 1, 10000 - 1)   # 100ms period
    tim2_set_callback(||:
        gpio_toggle(GPIOA, 5)
    )

    # Main loop
    loop:
        # Low power wait
        asm: "wfi"
```

---

## Summary

### Configuration Hierarchy

```
--target=cortex-m4 (target defaults)
    └── simple.sdn [interrupt] (project)
            └── __init__ interrupt_* (module)
                    └── @interrupt(...) (function)
```

### Quick Reference

| Scope | Setting | Syntax |
|-------|---------|--------|
| **Function** | Vector | `@interrupt(vector: N)` |
| | Priority | `@interrupt(priority: N)` or `priority: "name"` |
| | Attributes | `@fast`, `@naked`, `@reentrant` |
| **Module** | Default priority | `__init__: interrupt_priority_default = N` |
| | Default attributes | `__init__: interrupt_attributes_default = [...]` |
| | Critical section | `__init__: critical_section_impl = "primask"` |
| **Project** | Priority bits | `[interrupt] priority_bits = 4` |
| | Named vectors | `[interrupt.vectors] systick = 15` |
| | Priority groups | `[interrupt.priority_groups] high = 1` |
| **Target** | Architecture | `--target=cortex-m4` |

### Interrupt Attributes

| Attribute | Effect |
|-----------|--------|
| `@fast` | Minimal prologue/epilogue |
| `@naked` | No prologue/epilogue |
| `@reentrant` | Can be preempted |
| `@noreturn` | Never returns |

### Critical Section Options

| Implementation | Syntax | Effect |
|----------------|--------|--------|
| PRIMASK | `critical_section_impl = "primask"` | Disable all interrupts |
| BASEPRI | `critical_section_impl = "basepri"` | Disable below threshold |
| FAULTMASK | `critical_section_impl = "faultmask"` | Disable all + faults |
