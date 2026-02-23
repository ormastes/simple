# Bare-Metal Features: Example Usage Code

**Date**: 2026-02-05
**Status**: Pre-Implementation Examples
**Note**: Borrow checker deferred - pass for now

---

## Design Principles

1. **`assert` is static by default** - Compile-time verification when possible
2. **`static` keyword errors if unverifiable** - Fail compilation if can't prove at compile time
3. **Runtime fallback explicit** - Use `runtime_assert` for runtime-only checks
4. **Borrow checker**: Deferred, pass for now

---

## 1. Bitfields

### Example Usage

```simple
# Define a bitfield with backing type
bitfield GpioMode(u32):
    moder0: 2       # bits 0-1
    moder1: 2       # bits 2-3
    moder2: 2       # bits 4-5
    moder3: 2       # bits 6-7
    moder4: 2       # bits 8-9
    moder5: 2       # bits 10-11
    moder6: 2       # bits 12-13
    moder7: 2       # bits 14-15
    moder8: 2       # bits 16-17
    moder9: 2       # bits 18-19
    moder10: 2      # bits 20-21
    moder11: 2      # bits 22-23
    moder12: 2      # bits 24-25
    moder13: 2      # bits 26-27
    moder14: 2      # bits 28-29
    moder15: 2      # bits 30-31

# Static assertion: bitfield fits in backing type
# This is ALWAYS verified at compile time
assert size_of<GpioMode>() == 4  # Compile error if false

# Construction
val mode = GpioMode(moder5: 0b01, moder13: 0b10)

# Field access (generates bit masking code)
val pin5_mode = mode.moder5        # Extract bits 10-11
mode.moder5 = 0b11                 # Set bits 10-11

# Convert to/from raw value
val raw: u32 = mode.to_raw()
val mode2 = GpioMode.from_raw(0x00000400)

# Bitfield with reserved fields
bitfield UartStatus(u8):
    tx_empty: 1     # bit 0
    rx_ready: 1     # bit 1
    _reserved: 4    # bits 2-5 (cannot access)
    error: 1        # bit 6
    busy: 1         # bit 7

# Static assertion on field positions
assert UartStatus.error.offset == 6      # Compile-time check
assert UartStatus.error.width == 1       # Compile-time check
```

### Generated Code (Conceptual)

```simple
# Compiler generates:
impl GpioMode:
    fn moder5() -> u32:
        (self.raw >> 10) & 0b11

    me set_moder5(value: u32):
        self.raw = (self.raw & ~(0b11 << 10)) | ((value & 0b11) << 10)

    fn to_raw() -> u32:
        self.raw

    static fn from_raw(raw: u32) -> GpioMode:
        GpioMode(raw: raw)
```

---

## 2. Volatile Memory Access

### Example Usage

```simple
# Option A: Volatile variable at fixed address
@volatile val GPIO_STATUS: u32 @ 0x40020000
@volatile var GPIO_CONTROL: u32 @ 0x40020004

# Read always fetches from memory (not cached in register)
val status = GPIO_STATUS

# Write always commits to memory
GPIO_CONTROL = 0x01

# Option B: Volatile pointer type
val status_ptr: volatile ptr<u32> = rawptr(0x40020000)
val status = *status_ptr          # Volatile read
*status_ptr = 0xFF                # Volatile write

# Option C: Volatile block (all accesses inside are volatile)
volatile:
    val a = mem[0x40020000]       # Volatile read
    mem[0x40020004] = 0x01        # Volatile write
    mem[0x40020008] = a | 0x10    # Volatile read-modify-write

# Volatile struct fields
struct PeripheralRegs:
    @volatile status: u32
    @volatile control: u32
    @volatile data: u32

# Map struct to memory address
val regs: ptr<PeripheralRegs> @ 0x40020000

# Static assertion: struct layout matches hardware
assert offset_of<PeripheralRegs, status>() == 0
assert offset_of<PeripheralRegs, control>() == 4
assert offset_of<PeripheralRegs, data>() == 8
```

### SFFI Fallback (Current Workaround)

```simple
# If native volatile not implemented, use SFFI
extern fn rt_volatile_read_u8(addr: u64) -> u8
extern fn rt_volatile_read_u16(addr: u64) -> u16
extern fn rt_volatile_read_u32(addr: u64) -> u32
extern fn rt_volatile_write_u8(addr: u64, value: u8)
extern fn rt_volatile_write_u16(addr: u64, value: u16)
extern fn rt_volatile_write_u32(addr: u64, value: u32)

# Wrapper functions
fn mmio_read_u32(addr: u64) -> u32:
    rt_volatile_read_u32(addr)

fn mmio_write_u32(addr: u64, value: u32):
    rt_volatile_write_u32(addr, value)
```

---

## 3. Memory Layout Attributes

### Example Usage

```simple
# C-compatible layout (no reordering, standard alignment)
@repr(C)
struct DmaDescriptor:
    source: u32
    dest: u32
    count: u32
    control: u32

# Static assertion: size matches C
assert size_of<DmaDescriptor>() == 16

# Packed layout (no padding)
@repr(packed)
struct PackedHeader:
    magic: u8       # offset 0
    version: u8     # offset 1
    length: u16     # offset 2
    checksum: u32   # offset 4

assert size_of<PackedHeader>() == 8  # No padding

# Custom alignment
@repr(C)
@align(16)
struct CacheLineData:
    data: [u8; 64]

assert align_of<CacheLineData>() == 16

# Combining attributes
@repr(C)
@packed
@align(4)
struct HardwareBuffer:
    header: u32
    data: [u8; 28]

# Offset assertions (static)
assert offset_of<HardwareBuffer, header>() == 0
assert offset_of<HardwareBuffer, data>() == 4
```

---

## 4. Assert System

### Assert Levels (Constants)

```simple
# Built-in assert level constants
const ASSERT_STATIC = 0      # Compile-time only, error if can't verify
const ASSERT_PREFER_STATIC = 1  # Compile-time if possible, else runtime
const ASSERT_RUNTIME = 2     # Runtime only
const ASSERT_DEBUG = 3       # Runtime in debug builds, stripped in release
const ASSERT_DISABLED = 4    # Always stripped (for documentation)
```

### Basic Assert Syntax

```simple
# Two forms:
assert(LEVEL, expr)           # Explicit level
assert(LEVEL, expr, "message")  # With message
assert expr                   # Uses default level (configurable)
assert expr, "message"        # Uses default level with message
```

### Assert Behavior by Level

```simple
# ASSERT_STATIC: Must verify at compile time
assert(ASSERT_STATIC, size_of<u32>() == 4)           # OK: computable
assert(ASSERT_STATIC, BUFFER_SIZE >= 512)            # OK: const expr
# assert(ASSERT_STATIC, x > 0)                       # ERROR: runtime value

# ASSERT_PREFER_STATIC: Compile-time if possible, else runtime
assert(ASSERT_PREFER_STATIC, size_of<u32>() == 4)    # Checked at compile time
assert(ASSERT_PREFER_STATIC, x > 0)                  # Falls back to runtime
assert(ASSERT_PREFER_STATIC, array.len() > 0)        # Falls back to runtime

# ASSERT_RUNTIME: Always runtime check
assert(ASSERT_RUNTIME, x > 0)                        # Runtime check
assert(ASSERT_RUNTIME, data.len() <= 1024, "Buffer too large")

# ASSERT_DEBUG: Runtime in debug, stripped in release
assert(ASSERT_DEBUG, index >= 0)                     # Only in debug builds
assert(ASSERT_DEBUG, ptr != null)                    # Stripped in release

# ASSERT_DISABLED: Documentation only, always stripped
assert(ASSERT_DISABLED, invariant_holds())           # Never checked
```

### Default Level Configuration

#### Option 1: Module-Level `__init__`

```simple
# At top of file (before any code)
__init__:
    assert_default = ASSERT_PREFER_STATIC   # Default for this module

# Now plain assert uses ASSERT_PREFER_STATIC
assert size_of<MyStruct>() == 32    # Compile-time (can verify)
assert x > 0                        # Runtime (cannot verify statically)
```

#### Option 2: Library/App-Wide Config (`simple.sdn`)

```sdn
# simple.sdn - Project configuration

[assert]
default_level = "prefer_static"   # ASSERT_PREFER_STATIC

[assert.profiles]
debug:
    default_level = "prefer_static"
    debug_enabled = true

release:
    default_level = "runtime"
    debug_enabled = false

embedded:
    default_level = "static"      # Strict: all asserts must be static
    debug_enabled = false
```

#### Option 3: Target-Specific Defaults

```simple
# Defaults based on --target flag
# --target=embedded  -> ASSERT_STATIC (strict)
# --target=general   -> ASSERT_PREFER_STATIC
# --target=debug     -> ASSERT_DEBUG
```

### Examples with Different Defaults

#### Embedded Mode (default = ASSERT_STATIC)

```simple
# __init__:
#     assert_default = ASSERT_STATIC  (from --target=embedded)

# Plain assert MUST be verifiable at compile time
assert size_of<GpioRegs>() == 8         # OK: static
assert offset_of<Packet, data>() == 4   # OK: static
# assert buffer.len() > 0               # ERROR: cannot verify statically

# Explicit runtime when needed
assert(ASSERT_RUNTIME, buffer.len() > 0, "Empty buffer")
```

#### General Mode (default = ASSERT_PREFER_STATIC)

```simple
# __init__:
#     assert_default = ASSERT_PREFER_STATIC  (from --target=general)

# Plain assert tries static first, falls back to runtime
assert size_of<u32>() == 4              # Static (verified at compile time)
assert x > 0                            # Runtime (cannot verify statically)
assert array.len() > 0                  # Runtime fallback

# Force static when you want compile error on failure
assert(ASSERT_STATIC, MAGIC == 0xDEADBEEF)
```

### `static assert` Shorthand

```simple
# static assert is shorthand for assert(ASSERT_STATIC, ...)
static assert size_of<MyStruct>() == 32
# Equivalent to:
assert(ASSERT_STATIC, size_of<MyStruct>() == 32)

# With message
static assert BUFFER_SIZE >= 1024, "Buffer too small for protocol"
```

### Complete Assert Reference

| Syntax | Behavior |
|--------|----------|
| `assert(ASSERT_STATIC, expr)` | Compile-time only, error if can't verify |
| `assert(ASSERT_PREFER_STATIC, expr)` | Static if possible, else runtime |
| `assert(ASSERT_RUNTIME, expr)` | Always runtime |
| `assert(ASSERT_DEBUG, expr)` | Runtime in debug, stripped in release |
| `assert(ASSERT_DISABLED, expr)` | Always stripped (documentation) |
| `assert expr` | Uses module/project default level |
| `static assert expr` | Shorthand for `assert(ASSERT_STATIC, expr)` |

### Practical Examples

```simple
# Hardware driver with mixed assert levels
__init__:
    assert_default = ASSERT_PREFER_STATIC

bitfield GpioConfig(u32):
    mode: 2
    speed: 2
    pull: 2
    _reserved: 26

# Static assertions for hardware correctness (MUST be compile-time)
static assert size_of<GpioConfig>() == 4
static assert GpioConfig.mode.offset == 0
static assert GpioConfig.speed.offset == 2

fn configure_gpio(pin: i32, config: GpioConfig):
    # These use default (ASSERT_PREFER_STATIC)
    # Static because pin range is often known at compile time
    assert pin >= 0
    assert pin < 16

    # Runtime validation of config values
    assert(ASSERT_RUNTIME, config.mode <= 3, "Invalid GPIO mode")
    assert(ASSERT_RUNTIME, config.speed <= 3, "Invalid GPIO speed")

    # Debug-only bounds check (stripped in release for performance)
    assert(ASSERT_DEBUG, get_gpio_base(pin) != 0)

    unsafe:
        write_gpio_config(pin, config)

# Const function with static assertions
const fn compute_baud_divisor(clock: u32, baud: u32) -> u32:
    val divisor = clock / (16 * baud)
    # Static assertion inside const fn
    static assert divisor > 0, "Baud rate too high for clock"
    static assert divisor < 65536, "Baud rate too low for clock"
    divisor

const UART_DIVISOR: u32 = compute_baud_divisor(84_000_000, 115200)
```

### Configuration Precedence

```
1. Explicit level: assert(LEVEL, expr)     <- Highest priority
2. Module __init__: assert_default = ...
3. Project simple.sdn: [assert].default_level
4. Target default: --target=embedded       <- Lowest priority
```

### Migration from Other Languages

| Other Language | Simple Equivalent |
|----------------|-------------------|
| C `assert()` | `assert(ASSERT_DEBUG, expr)` |
| C `static_assert()` | `static assert expr` or `assert(ASSERT_STATIC, expr)` |
| Rust `assert!()` | `assert(ASSERT_RUNTIME, expr)` |
| Rust `debug_assert!()` | `assert(ASSERT_DEBUG, expr)` |
| Zig `comptime assert` | `assert(ASSERT_STATIC, expr)` |
| Zig `std.debug.assert` | `assert(ASSERT_DEBUG, expr)` |

---

## 5. Const Functions (Compile-Time Evaluation)

### Example Usage

```simple
# Const function - evaluated at compile time when possible
const fn factorial(n: i32) -> i32:
    if n <= 1: 1
    else: n * factorial(n - 1)

# Used in const context - computed at compile time
const FACT_10: i32 = factorial(10)
assert FACT_10 == 3628800  # Static assertion, verified at compile time

# Const lookup table generation
const fn crc32_table() -> [u32; 256]:
    var table = [0u32; 256]
    for i in 0..256:
        var crc = i as u32
        for _ in 0..8:
            crc = if crc & 1 != 0:
                (crc >> 1) xor 0xEDB88320
            else:
                crc >> 1
        table[i] = crc
    table

const CRC32_TABLE: [u32; 256] = crc32_table()

# Const fn for bit manipulation
const fn bit_mask(start: i32, width: i32) -> u32:
    ((1 << width) - 1) << start

const GPIO_MODE_MASK: u32 = bit_mask(10, 2)  # Computed at compile time
assert GPIO_MODE_MASK == 0x0C00

# Const fn in type context
const fn array_size(element_size: i32, count: i32) -> i32:
    element_size * count

struct Buffer:
    data: [u8; array_size(4, 256)]  # [u8; 1024]
```

### Const vs Non-Const Context

```simple
const fn double(x: i32) -> i32:
    x * 2

# Compile-time evaluation
const DOUBLED: i32 = double(21)  # = 42, computed at compile time

# Runtime evaluation (const fn can also run at runtime)
fn process(value: i32) -> i32:
    double(value)  # Called at runtime

# Mixed: const where possible
val result = double(DOUBLED)     # double(42) might be const-folded
val dynamic = double(read_input())  # Must be runtime
```

---

## 6. Unsafe Blocks

### Example Usage

```simple
# Unsafe operations require explicit block
# Borrow checker: deferred, pass for now

unsafe:
    # Raw pointer creation and dereference
    val ptr = rawptr<u32>(0x40020000)
    val value = *ptr              # Dereference
    *ptr = 0xFF                   # Write through pointer

    # Pointer arithmetic
    val next_ptr = ptr + 4        # Advance by 4 bytes
    val array_ptr = ptr as ptr<[u32; 4]>

    # Type punning
    val float_bits = *(rawptr<u32>(&my_float))

    # Call unsafe extern function
    rt_dangerous_operation()

# Unsafe function (caller must use unsafe block)
unsafe fn write_register(addr: u64, value: u32):
    val ptr = rawptr<u32>(addr)
    *ptr = value

# Calling unsafe function
fn init_hardware():
    unsafe:
        write_register(0x40020000, 0x01)
        write_register(0x40020004, 0xFF)

# Safe wrapper around unsafe
fn safe_gpio_write(pin: i32, value: bool):
    assert pin >= 0 and pin < 16  # Static if possible, runtime otherwise
    unsafe:
        val addr = GPIO_BASE + (pin / 8) * 4
        val bit = pin % 8
        val ptr = rawptr<u32>(addr)
        if value:
            *ptr = *ptr | (1 << bit)
        else:
            *ptr = *ptr & ~(1 << bit)
```

---

## 7. Interrupt Handlers

### Example Usage

```simple
# Interrupt handler attribute
@interrupt(vector: 15)  # SysTick on Cortex-M
fn systick_handler():
    TICK_COUNT.fetch_add(1, Relaxed)

# Interrupt with priority
@interrupt(vector: 25, priority: 2)
fn uart_rx_handler():
    val byte = unsafe { *UART_DR }
    RX_BUFFER.push(byte)

# Naked function (no prologue/epilogue)
@naked
@interrupt(vector: 3)
fn hard_fault_handler():
    asm:
        "bkpt #0"
        "b ."

# Non-maskable interrupt
@interrupt(vector: 2, nmi: true)
fn nmi_handler():
    # Handle NMI
    pass

# Static assertion: interrupt vector valid
assert systick_handler.vector == 15
assert systick_handler.vector < 256
```

### Interrupt Control

```simple
# Enable/disable interrupts
fn critical_section<T>(f: fn() -> T) -> T:
    val primask = disable_interrupts()
    val result = f()
    restore_interrupts(primask)
    result

# SFFI for interrupt control
extern fn rt_disable_interrupts() -> u32
extern fn rt_restore_interrupts(primask: u32)
extern fn rt_enable_irq(vector: i32)
extern fn rt_disable_irq(vector: i32)
extern fn rt_set_priority(vector: i32, priority: i32)

fn disable_interrupts() -> u32:
    rt_disable_interrupts()

fn restore_interrupts(primask: u32):
    rt_restore_interrupts(primask)
```

---

## 8. Fixed-Size Arrays

### Example Usage

```simple
# Fixed-size array type
val buffer: [u8; 1024]

# Static assertion on size
assert size_of<[u8; 1024]>() == 1024

# Initialize with values
val lookup: [i32; 4] = [0, 1, 1, 2]

# Initialize with expression
val zeros: [u8; 256] = [0; 256]

# Const array (compile-time immutable)
const PRIMES: [i32; 10] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29]

# Static assertion on const array
assert PRIMES[0] == 2
assert PRIMES[9] == 29

# Array in struct
struct Packet:
    header: u32
    payload: [u8; 128]
    checksum: u32

assert size_of<Packet>() == 136  # 4 + 128 + 4

# Compile-time array size from const fn
const fn buffer_size(n: i32) -> i32:
    n * 64

struct DynamicBuffer:
    data: [u8; buffer_size(4)]  # [u8; 256]

# Bounds checking
fn get_element(arr: [i32; 10], index: i32) -> i32:
    # Static check when index is const
    assert index >= 0        # Error if index is runtime and can't prove
    runtime_assert index < 10, "Index out of bounds"
    arr[index]
```

---

## 9. Memory Barriers

### Example Usage

```simple
import std.atomic.{fence, MemoryOrdering}

# Acquire barrier (loads before fence happen before loads after)
fn read_with_acquire(addr: u64) -> u32:
    val value = mmio_read_u32(addr)
    fence(Acquire)
    value

# Release barrier (stores before fence complete before stores after)
fn write_with_release(addr: u64, value: u32):
    fence(Release)
    mmio_write_u32(addr, value)

# Full barrier (sequentially consistent)
fn memory_barrier():
    fence(SeqCst)

# Device memory barrier pattern
fn write_to_device(data: u32):
    # Write data to buffer
    DEVICE_BUFFER = data

    # Ensure write completes before signaling
    fence(Release)

    # Signal device
    DEVICE_CONTROL = CONTROL_START

fn read_from_device() -> u32:
    # Wait for device ready
    while (DEVICE_STATUS & STATUS_READY) == 0:
        pass

    # Ensure status read happens before data read
    fence(Acquire)

    # Read data
    DEVICE_DATA
```

---

## 10. Linker Script Generation

### SDN Configuration

```sdn
# embedded.sdn

target: cortex-m4

memory:
    flash:
        origin: 0x08000000
        length: 512K
        permissions: rx

    sram:
        origin: 0x20000000
        length: 128K
        permissions: rwx

    ccm:
        origin: 0x10000000
        length: 64K
        permissions: rw

sections:
    .isr_vector:
        memory: flash
        address: 0x08000000
        keep: true
        align: 4

    .text:
        memory: flash
        align: 4

    .rodata:
        memory: flash
        align: 4

    .data:
        memory: sram
        load_address: flash
        align: 4

    .bss:
        memory: sram
        align: 4
        type: nobits

    .heap:
        memory: sram
        size: 16K

    .stack:
        memory: ccm
        size: 8K
        direction: descending

entry: reset_handler

symbols:
    _stack_start: .stack.end
    _heap_start: .heap.start
    _heap_end: .heap.end
```

### Usage in Code

```simple
# Reference linker symbols
extern val _stack_start: u32
extern val _heap_start: u32
extern val _heap_end: u32
extern val _data_start: u32
extern val _data_end: u32
extern val _bss_start: u32
extern val _bss_end: u32

# Startup code
@entry
@naked
fn reset_handler():
    # Set stack pointer
    asm:
        "ldr sp, =_stack_start"

    # Initialize .data section
    copy_data(&_data_start, &_data_end, &_data_load)

    # Zero .bss section
    zero_bss(&_bss_start, &_bss_end)

    # Call main
    main()

    # Halt if main returns
    loop:
        asm: "wfi"

fn copy_data(start: ptr<u32>, end: ptr<u32>, load: ptr<u32>):
    var dst = start
    var src = load
    while dst < end:
        unsafe:
            *dst = *src
        dst = dst + 4
        src = src + 4

fn zero_bss(start: ptr<u32>, end: ptr<u32>):
    var ptr = start
    while ptr < end:
        unsafe:
            *ptr = 0
        ptr = ptr + 4
```

---

## 11. Complete Embedded Example

```simple
# blinky.spl - Complete LED blink for STM32F4
@target(embedded)

# ===== Hardware Definitions =====

const GPIO_A_BASE: u64 = 0x40020000
const RCC_BASE: u64 = 0x40023800

bitfield GpioModer(u32):
    mode0: 2
    mode1: 2
    mode2: 2
    mode3: 2
    mode4: 2
    mode5: 2
    mode6: 2
    mode7: 2
    mode8: 2
    mode9: 2
    mode10: 2
    mode11: 2
    mode12: 2
    mode13: 2
    mode14: 2
    mode15: 2

# Static assertions
assert size_of<GpioModer>() == 4
assert GpioModer.mode5.offset == 10
assert GpioModer.mode5.width == 2

# ===== Register Access =====

@volatile val GPIOA_MODER: ptr<u32> @ GPIO_A_BASE + 0x00
@volatile val GPIOA_ODR: ptr<u32> @ GPIO_A_BASE + 0x14
@volatile val RCC_AHB1ENR: ptr<u32> @ RCC_BASE + 0x30

# ===== Global State =====

var tick_count: AtomicU32 = AtomicU32(0)

# ===== Interrupt Handler =====

@interrupt(vector: 15)  # SysTick
fn systick_handler():
    tick_count.fetch_add(1, Relaxed)

# ===== Functions =====

fn init_gpio():
    # Enable GPIOA clock
    unsafe:
        *RCC_AHB1ENR = *RCC_AHB1ENR | (1 << 0)

    # Set PA5 as output
    var moder = GpioModer.from_raw(unsafe { *GPIOA_MODER })
    moder.mode5 = 0b01  # Output mode
    unsafe:
        *GPIOA_MODER = moder.to_raw()

fn toggle_led():
    unsafe:
        *GPIOA_ODR = *GPIOA_ODR xor (1 << 5)

fn delay_ms(ms: u32):
    val start = tick_count.load(Relaxed)
    while tick_count.load(Relaxed) - start < ms:
        asm: "nop"

# ===== Entry Point =====

@entry
fn main() -> !:
    init_gpio()
    init_systick(1000)  # 1ms tick

    loop:
        toggle_led()
        delay_ms(500)

# ===== Startup (from linker) =====

extern fn init_systick(hz: u32)
```

---

## Summary: Assert Behavior

### Assert Levels

| Level | Compile-Time | Runtime | Release |
|-------|--------------|---------|---------|
| `ASSERT_STATIC` | **Required** (error if can't) | No | No |
| `ASSERT_PREFER_STATIC` | If possible | Fallback | Yes |
| `ASSERT_RUNTIME` | No | Yes | Yes |
| `ASSERT_DEBUG` | No | Yes | **Stripped** |
| `ASSERT_DISABLED` | No | No | No |

### Syntax Summary

| Syntax | Behavior |
|--------|----------|
| `assert(LEVEL, expr)` | Explicit level control |
| `assert(LEVEL, expr, "msg")` | With message |
| `assert expr` | Uses default (configurable) |
| `static assert expr` | Shorthand for `ASSERT_STATIC` |

### Default Configuration

| Method | Scope | Example |
|--------|-------|---------|
| `__init__` block | Module | `assert_default = ASSERT_STATIC` |
| `simple.sdn` | Project | `[assert] default_level = "prefer_static"` |
| `--target` flag | Build | `--target=embedded` → `ASSERT_STATIC` |

### Target Defaults

| Target | Default Assert Level |
|--------|---------------------|
| `embedded` | `ASSERT_STATIC` (strict) |
| `general` | `ASSERT_PREFER_STATIC` |
| `debug` | `ASSERT_DEBUG` |
| `performance` | `ASSERT_RUNTIME` |

**Key Rule**: `assert expr` behavior depends on configuration. Use explicit levels (`assert(LEVEL, expr)`) when you need guaranteed behavior regardless of config.

---

## Implementation Notes

1. **Bitfields**: Parser complete in grammar, needs compiler implementation
2. **Volatile**: Start with SFFI functions, add native syntax later
3. **Assert**: Implement static evaluation engine first
4. **Const fn**: Requires compile-time interpreter
5. **Unsafe**: Mark regions, skip borrow checking (deferred)
6. **Interrupts**: Generate vector table entries, handle attributes
7. **Linker**: Parse SDN, emit GNU LD script
