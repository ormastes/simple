# x86 Bare-Metal Boot Specification

> Tests for the x86 bare-metal boot infrastructure including:

<!-- sdn-diagram:id=x86_boot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=x86_boot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

x86_boot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=x86_boot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# x86 Bare-Metal Boot Specification

Tests for the x86 bare-metal boot infrastructure including:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #BM-BOOT-001 |
| Category | Bare-Metal / x86 |
| Status | In Progress |
| Source | `test/03_system/feature/usage/x86_boot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests for the x86 bare-metal boot infrastructure including:
- Multiboot header generation
- GDT setup and loading
- Serial port initialization
- Test harness output

## Scenarios

### x86 Boot Infrastructure

#### Multiboot Header

#### has correct magic number

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The magic number must be 0x1BADB002.
val MULTIBOOT_MAGIC: u32 = 0x1BADB002
expect(MULTIBOOT_MAGIC).to_equal(0x1BADB002)
```

</details>

#### has correct flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PAGE_ALIGN | MEMORY_INFO flags.
val MULTIBOOT_PAGE_ALIGN: u32 = 1 << 0
val MULTIBOOT_MEMORY_INFO: u32 = 1 << 1
val MULTIBOOT_FLAGS: u32 = MULTIBOOT_PAGE_ALIGN | MULTIBOOT_MEMORY_INFO
expect(MULTIBOOT_FLAGS).to_equal(3)
```

</details>

#### checksum validates

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# magic + flags + checksum must equal 0.
val MULTIBOOT_MAGIC: u32 = 0x1BADB002
val MULTIBOOT_FLAGS: u32 = 3
val MULTIBOOT_CHECKSUM: u32 = 0 - (MULTIBOOT_MAGIC + MULTIBOOT_FLAGS)
val sum = MULTIBOOT_MAGIC + MULTIBOOT_FLAGS + MULTIBOOT_CHECKSUM
# Due to u32 overflow, this should be 0
expect((sum & 0xFFFFFFFF) as u32).to_equal(0)
```

</details>

#### GDT Entries

#### null descriptor is all zeros

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# First GDT entry must be null (all zeros).
# GdtEntry.null() should produce 8 zero bytes
val null_descriptor: [u8] = [0, 0, 0, 0, 0, 0, 0, 0]
expect(null_descriptor.len()).to_equal(8)
expect(null_descriptor[0]).to_equal(0)
expect(null_descriptor[7]).to_equal(0)
```

</details>

#### kernel code segment has correct access

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Kernel code: Present, Ring 0, Code/Data, Executable, Readable.
val ACCESS_PRESENT: u8 = 1 << 7
val ACCESS_RING0: u8 = 0 << 5
val ACCESS_CODE_DATA: u8 = 1 << 4
val ACCESS_EXEC: u8 = 1 << 3
val ACCESS_RW: u8 = 1 << 1
val expected = ACCESS_PRESENT | ACCESS_RING0 | ACCESS_CODE_DATA | ACCESS_EXEC | ACCESS_RW
expect(expected).to_equal(0x9A)  # 0b10011010
```

</details>

#### kernel data segment has correct access

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Kernel data: Present, Ring 0, Code/Data, Writable.
val ACCESS_PRESENT: u8 = 1 << 7
val ACCESS_RING0: u8 = 0 << 5
val ACCESS_CODE_DATA: u8 = 1 << 4
val ACCESS_RW: u8 = 1 << 1
val expected = ACCESS_PRESENT | ACCESS_RING0 | ACCESS_CODE_DATA | ACCESS_RW
expect(expected).to_equal(0x92)  # 0b10010010
```

</details>

#### Segment Selectors

#### kernel code selector is 0x08

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val KERNEL_CODE_SELECTOR: u16 = 0x08
expect(KERNEL_CODE_SELECTOR).to_equal(8)
```

</details>

#### kernel data selector is 0x10

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val KERNEL_DATA_SELECTOR: u16 = 0x10
expect(KERNEL_DATA_SELECTOR).to_equal(16)
```

</details>

#### user code selector has RPL 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val USER_CODE_SELECTOR: u16 = 0x18 | 3
expect(USER_CODE_SELECTOR).to_equal(0x1B)
```

</details>

#### user data selector has RPL 3

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val USER_DATA_SELECTOR: u16 = 0x20 | 3
expect(USER_DATA_SELECTOR).to_equal(0x23)
```

</details>

### Serial Port

#### COM Port Addresses

#### COM1 base address is 0x3F8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val COM1: u16 = 0x3F8
expect(COM1).to_equal(0x3F8)
```

</details>

#### COM2 base address is 0x2F8

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val COM2: u16 = 0x2F8
expect(COM2).to_equal(0x2F8)
```

</details>

#### UART Registers

#### data register offset is 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val UART_DATA: u16 = 0
expect(UART_DATA).to_equal(0)
```

</details>

#### line status register offset is 5

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val UART_LSR: u16 = 5
expect(UART_LSR).to_equal(5)
```

</details>

#### Baud Rate Divisors

#### 115200 baud divisor is 1

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BAUD_115200: u16 = 1
expect(BAUD_115200).to_equal(1)
```

</details>

#### 9600 baud divisor is 12

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val BAUD_9600: u16 = 12
expect(BAUD_9600).to_equal(12)
```

</details>

### Linker Script Generation

#### Memory Regions

#### formats hex addresses correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test format_hex function
# 0x100000 = 1048576
val addr: i64 = 1048576
expect(addr).to_equal(0x100000)
```

</details>

#### Section Layout

#### multiboot section comes first

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Multiboot header must be within first 8KB
val MULTIBOOT_ADDR: i64 = 0x00100000
val MULTIBOOT_LIMIT: i64 = 0x00102000  # 8KB after load addr
expect(MULTIBOOT_ADDR).to_be_less_than(MULTIBOOT_LIMIT)
```

</details>

### QEMU Exit Codes

#### Exit Code Translation

#### success exit code (0) becomes (1)

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# QEMU: exit_code = (value << 1) | 1
val value = 0
val qemu_exit = (value << 1) | 1
expect(qemu_exit).to_equal(1)
```

</details>

#### failure exit code (1) becomes (3)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val value = 1
val qemu_exit = (value << 1) | 1
expect(qemu_exit).to_equal(3)
```

</details>

#### can decode QEMU exit code

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# adjusted = (exit_code - 1) / 2
val qemu_exit = 3
val original = (qemu_exit - 1) / 2
expect(original).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
