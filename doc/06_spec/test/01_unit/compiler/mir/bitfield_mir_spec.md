# For field at offset 4, width 3:

> check(code.contains("bitfield"))

<!-- sdn-diagram:id=bitfield_mir_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bitfield_mir_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bitfield_mir_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bitfield_mir_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# For field at offset 4, width 3:

check(code.contains("bitfield"))

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/bitfield_mir_spec.spl` |
| Updated | 2026-07-06 |
| Generator | `simple spipe-docgen` (Simple) |

check(code.contains("bitfield"))
        check(code.contains("Flags"))

    it "supports bool fields (1 bit)":
        val code = """
        bitfield Status(u8):
            ready: bool
            error: bool

## Scenarios

### Bitfield Syntax

#### recognizes bitfield definitions

- bitfield Flags
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield Flags(u32):
    enabled: bool
    priority: u4
"""
check(code.contains("bitfield"))
check(code.contains("Flags"))
```

</details>

#### supports bool fields (1 bit)

- bitfield Status
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield Status(u8):
    ready: bool
    error: bool
"""
check(code.contains("ready: bool"))
check(code.contains("error: bool"))
```

</details>

#### supports custom bit widths

- bitfield Control
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield Control(u32):
    mode: u2      # 2 bits
    level: u4     # 4 bits
    flags: u8     # 8 bits
"""
check(code.contains("u2"))
check(code.contains("u4"))
check(code.contains("u8"))
```

</details>

#### supports reserved/padding fields

- bitfield Register
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield Register(u32):
    data: u8
    _: u8          # 8 bits reserved
    status: u16
"""
check(code.contains("_: u8"))
```

</details>

### Bitfield Field Access

#### reads bitfield fields

- bitfield Flags
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield Flags(u32):
    enabled: bool
    priority: u4

val flags = Flags(0x06)  # 0b0110
val priority = flags.priority  # Should be (0x06 >> 1) & 0xF = 3
"""
check(code.contains("flags.priority"))
```

</details>

#### writes bitfield fields

- bitfield Flags
- var flags = Flags
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield Flags(u32):
    enabled: bool
    priority: u4

var flags = Flags(0)
flags.priority = 3  # Set priority to 3
"""
check(code.contains("flags.priority = 3"))
```

</details>

#### handles multiple field updates

- bitfield Status
- var status = Status
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield Status(u8):
    ready: bool
    error: bool
    mode: u2

var status = Status(0)
status.ready = true
status.error = false
status.mode = 2
"""
check(code.contains("status.ready = true"))
check(code.contains("status.mode = 2"))
```

</details>

### Bitfield Bit Operations

#### generates correct getter mask

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For field at offset 4, width 3:
# mask = (1 << 3) - 1 = 7
# getter = (value >> 4) & 7
val code = "val result = (value >> 4) & 7"
check(code.contains(">> 4"))
check(code.contains("& 7"))
```

</details>

#### generates correct setter mask

- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For field at offset 4, width 3:
# clear_mask = ~(7 << 4) = ~0x70 = 0xFFFFFF8F
# setter = (value & clear_mask) | ((new_val & 7) << 4)
val code = "val result = (value & clear_mask) | ((new_val & 7) << 4)"
check(code.contains("& clear_mask"))
check(code.contains("& 7"))
check(code.contains("<< 4"))
```

</details>

### Bitfield Real-World Examples

#### implements hardware control register

- bitfield ControlReg
- fn enter unprivileged
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
# ARM Cortex-M CONTROL register
bitfield ControlReg(u32):
    npriv: bool      # Non-privileged mode
    spsel: bool      # Stack pointer select
    _: u30           # Reserved

@address(0xE000ED04)
@volatile
var CONTROL: ControlReg

fn enter_unprivileged():
    unsafe:
        CONTROL.npriv = true
"""
check(code.contains("bitfield ControlReg"))
check(code.contains("@volatile"))
check(code.contains("CONTROL.npriv = true"))
```

</details>

#### implements peripheral status register

- bitfield UartStatus
- fn uart ready
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
# UART status register
bitfield UartStatus(u32):
    rxne: bool       # Receive not empty
    txe: bool        # Transmit empty
    tc: bool         # Transmission complete
    idle: bool       # Idle line detected
    ore: bool        # Overrun error
    nf: bool         # Noise error
    fe: bool         # Framing error
    pe: bool         # Parity error
    _: u24           # Reserved

@address(0x40011000)
@volatile
val UART_SR: UartStatus

fn uart_ready() -> bool:
    unsafe:
        UART_SR.txe
"""
check(code.contains("bitfield UartStatus"))
check(code.contains("UART_SR.txe"))
```

</details>

#### implements DMA configuration

- bitfield DmaConfig
- psize: u2        # Peripheral size
- var dma cfg = DmaConfig
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
# DMA channel configuration
bitfield DmaConfig(u32):
    en: bool         # Channel enable
    tcie: bool       # Transfer complete interrupt
    htie: bool       # Half transfer interrupt
    teie: bool       # Transfer error interrupt
    dir: bool        # Data transfer direction
    circ: bool       # Circular mode
    pinc: bool       # Peripheral increment
    minc: bool       # Memory increment
    psize: u2        # Peripheral size (00=8bit, 01=16bit, 10=32bit)
    msize: u2        # Memory size
    pl: u2           # Priority level
    mem2mem: bool    # Memory to memory
    _: u17           # Reserved

var dma_cfg = DmaConfig(0)
dma_cfg.en = true
dma_cfg.tcie = true
dma_cfg.dir = false
dma_cfg.psize = 2  # 32-bit
dma_cfg.pl = 3     # Very high priority
"""
check(code.contains("bitfield DmaConfig"))
check(code.contains("psize: u2"))
check(code.contains("dma_cfg.pl = 3"))
```

</details>

#### implements x86 EFLAGS register

- bitfield EFlags
-  : u1            # Reserved
- fn read eflags
- asm volatile
- EFlags
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
# x86/x86_64 EFLAGS register
bitfield EFlags(u64):
    cf: bool         # Carry flag
    _: u1            # Reserved (always 1)
    pf: bool         # Parity flag
    _: u1
    af: bool         # Auxiliary carry flag
    _: u1
    zf: bool         # Zero flag
    sf: bool         # Sign flag
    tf: bool         # Trap flag
    if_: bool        # Interrupt enable flag
    df: bool         # Direction flag
    of: bool         # Overflow flag
    iopl: u2         # I/O privilege level
    nt: bool         # Nested task
    _: u1
    rf: bool         # Resume flag
    vm: bool         # Virtual 8086 mode
    ac: bool         # Alignment check
    vif: bool        # Virtual interrupt flag
    vip: bool        # Virtual interrupt pending
    id: bool         # ID flag
    _: u42           # Reserved

fn read_eflags() -> EFlags:
    var flags: u64
    unsafe:
        asm volatile("pushfq; pop {flags}", flags = out(reg) flags)
    EFlags(flags)
"""
check(code.contains("bitfield EFlags(u64)"))
check(code.contains("iopl: u2"))
```

</details>

### Bitfield Error Cases

#### detects overflow (too many bits)

- bitfield BadFlags
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield BadFlags(u8):
    field1: u4
    field2: u4
    field3: u4   # ERROR: 4+4+4=12 > 8 bits
"""
# This should fail validation
check(code.contains("field3: u4"))
```

</details>

#### requires valid backing type

- bitfield BadBacking
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val code = """
bitfield BadBacking(i32):  # ERROR: must be u8/u16/u32/u64
    field: bool
"""
# Should fail - signed types not allowed
check(code.contains("i32"))
```

</details>

### Bitfield MIR Lowering

#### lowers field read to shift and mask

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# flags.priority where priority is at offset 1, width 4
# Should become: (flags >> 1) & 0xF
val code = """
val priority = (flags >> 1) & 0xF
"""
check(code.contains(">>"))
check(code.contains("&"))
```

</details>

#### lowers field write to clear and set

- flags =
- check
- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# flags.priority = 3 where priority is at offset 1, width 4
# Should become: flags = (flags & ~(0xF << 1)) | ((3 & 0xF) << 1)
val code = """
flags = (flags & ~(0xF << 1)) | ((3 & 0xF) << 1)
"""
check(code.contains("& ~"))
check(code.contains("<<"))
check(code.contains("|"))
```

</details>

### Bitfield at Offset 0 (No Shift)

#### optimizes away zero shifts for reads

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For field at offset 0, width 1:
# Should be: value & 0x1 (no shift)
val code = "val result = value & 0x1"
check(code.contains("& 0x1"))
check(not code.contains(">>"))
```

</details>

#### optimizes away zero shifts for writes

- check
- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# For field at offset 0, width 1:
# Should be: (value & ~0x1) | (new_val & 0x1)
val code = "val result = (value & ~0x1) | (new_val & 0x1)"
check(code.contains("& ~0x1"))
check(not code.contains("<<"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
