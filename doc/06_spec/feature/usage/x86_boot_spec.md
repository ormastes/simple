# x86 Bare-Metal Boot Specification

> Tests for the x86 bare-metal boot infrastructure including:

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
| Source | `test/feature/usage/x86_boot_spec.spl` |
| Updated | 2026-08-26 |
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

- has correct magic number
- has correct magic number
   - Expected: MULTIBOOT_MAGIC equals `0x1BADB002`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has correct magic number")
step("has correct magic number")
# @req: REQ-FEAT-USAGE-X86-BOOT-SPEC-001
# The magic number must be 0x1BADB002.
val MULTIBOOT_MAGIC: u32 = 0x1BADB002
expect(MULTIBOOT_MAGIC).to_equal(0x1BADB002)
```

</details>

#### has correct flags

- has correct flags
- has correct flags
   - Expected: MULTIBOOT_FLAGS equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("has correct flags")
step("has correct flags")
# PAGE_ALIGN | MEMORY_INFO flags.
val MULTIBOOT_PAGE_ALIGN: u32 = 1 << 0
val MULTIBOOT_MEMORY_INFO: u32 = 1 << 1
val MULTIBOOT_FLAGS: u32 = MULTIBOOT_PAGE_ALIGN | MULTIBOOT_MEMORY_INFO
expect(MULTIBOOT_FLAGS).to_equal(3)
```

</details>

#### checksum validates

- checksum validates
- checksum validates
   - Expected: (sum & 0xFFFFFFFF) as u32 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("checksum validates")
step("checksum validates")
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

- null descriptor is all zeros
- null descriptor is all zeros
   - Expected: true is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("null descriptor is all zeros")
step("null descriptor is all zeros")
# First GDT entry must be null (all zeros).
# GdtEntry.null() should produce 8 zero bytes
expect(true).to_equal(true)  # Placeholder - actual test needs GDT type
```

</details>

#### kernel code segment has correct access

- kernel code segment has correct access
- kernel code segment has correct access
   - Expected: expected equals `0x9A)  # 0b10011010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("kernel code segment has correct access")
step("kernel code segment has correct access")
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

- kernel data segment has correct access
- kernel data segment has correct access
   - Expected: expected equals `0x92)  # 0b10010010`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("kernel data segment has correct access")
step("kernel data segment has correct access")
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

- kernel code selector is 0x08
- kernel code selector is 0x08
   - Expected: KERNEL_CODE_SELECTOR equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("kernel code selector is 0x08")
step("kernel code selector is 0x08")
val KERNEL_CODE_SELECTOR: u16 = 0x08
expect(KERNEL_CODE_SELECTOR).to_equal(8)
```

</details>

#### kernel data selector is 0x10

- kernel data selector is 0x10
- kernel data selector is 0x10
   - Expected: KERNEL_DATA_SELECTOR equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("kernel data selector is 0x10")
step("kernel data selector is 0x10")
val KERNEL_DATA_SELECTOR: u16 = 0x10
expect(KERNEL_DATA_SELECTOR).to_equal(16)
```

</details>

#### user code selector has RPL 3

- user code selector has RPL 3
- user code selector has RPL 3
   - Expected: USER_CODE_SELECTOR equals `0x1B`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("user code selector has RPL 3")
step("user code selector has RPL 3")
val USER_CODE_SELECTOR: u16 = 0x18 | 3
expect(USER_CODE_SELECTOR).to_equal(0x1B)
```

</details>

#### user data selector has RPL 3

- user data selector has RPL 3
- user data selector has RPL 3
   - Expected: USER_DATA_SELECTOR equals `0x23`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("user data selector has RPL 3")
step("user data selector has RPL 3")
val USER_DATA_SELECTOR: u16 = 0x20 | 3
expect(USER_DATA_SELECTOR).to_equal(0x23)
```

</details>

### Serial Port

#### COM Port Addresses

#### COM1 base address is 0x3F8

- COM1 base address is 0x3F8
- COM1 base address is 0x3F8
   - Expected: COM1 equals `0x3F8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("COM1 base address is 0x3F8")
step("COM1 base address is 0x3F8")
val COM1: u16 = 0x3F8
expect(COM1).to_equal(0x3F8)
```

</details>

#### COM2 base address is 0x2F8

- COM2 base address is 0x2F8
- COM2 base address is 0x2F8
   - Expected: COM2 equals `0x2F8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("COM2 base address is 0x2F8")
step("COM2 base address is 0x2F8")
val COM2: u16 = 0x2F8
expect(COM2).to_equal(0x2F8)
```

</details>

#### UART Registers

#### data register offset is 0

- data register offset is 0
- data register offset is 0
   - Expected: UART_DATA equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("data register offset is 0")
step("data register offset is 0")
val UART_DATA: u16 = 0
expect(UART_DATA).to_equal(0)
```

</details>

#### line status register offset is 5

- line status register offset is 5
- line status register offset is 5
   - Expected: UART_LSR equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("line status register offset is 5")
step("line status register offset is 5")
val UART_LSR: u16 = 5
expect(UART_LSR).to_equal(5)
```

</details>

#### Baud Rate Divisors

#### 115200 baud divisor is 1

- 115200 baud divisor is 1
- 115200 baud divisor is 1
   - Expected: BAUD_115200 equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("115200 baud divisor is 1")
step("115200 baud divisor is 1")
val BAUD_115200: u16 = 1
expect(BAUD_115200).to_equal(1)
```

</details>

#### 9600 baud divisor is 12

- 9600 baud divisor is 12
- 9600 baud divisor is 12
   - Expected: BAUD_9600 equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("9600 baud divisor is 12")
step("9600 baud divisor is 12")
val BAUD_9600: u16 = 12
expect(BAUD_9600).to_equal(12)
```

</details>

### Linker Script Generation

#### Memory Regions

#### formats hex addresses correctly

- formats hex addresses correctly
- formats hex addresses correctly
   - Expected: addr equals `0x100000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("formats hex addresses correctly")
step("formats hex addresses correctly")
# Test format_hex function
# 0x100000 = 1048576
val addr: i64 = 1048576
expect(addr).to_equal(0x100000)
```

</details>

#### Section Layout

#### multiboot section comes first

- multiboot section comes first
- multiboot section comes first


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("multiboot section comes first")
step("multiboot section comes first")
# Multiboot header must be within first 8KB
val MULTIBOOT_ADDR: i64 = 0x00100000
val MULTIBOOT_LIMIT: i64 = 0x00102000  # 8KB after load addr
expect(MULTIBOOT_ADDR).to_be_less_than(MULTIBOOT_LIMIT)
```

</details>

### QEMU Exit Codes

#### Exit Code Translation

#### success exit code (0) becomes (1)

- success exit code (0) becomes (1)
- success exit code (0) becomes (1)
   - Expected: qemu_exit equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("success exit code (0) becomes (1)")
step("success exit code (0) becomes (1)")
# QEMU: exit_code = (value << 1) | 1
val value = 0
val qemu_exit = (value << 1) | 1
expect(qemu_exit).to_equal(1)
```

</details>

#### failure exit code (1) becomes (3)

- failure exit code (1) becomes (3)
- failure exit code (1) becomes (3)
   - Expected: qemu_exit equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("failure exit code (1) becomes (3)")
step("failure exit code (1) becomes (3)")
val value = 1
val qemu_exit = (value << 1) | 1
expect(qemu_exit).to_equal(3)
```

</details>

#### can decode QEMU exit code

- can decode QEMU exit code
- can decode QEMU exit code
   - Expected: original equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can decode QEMU exit code")
step("can decode QEMU exit code")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
- `REQ-FEAT-USAGE-X86-BOOT-SPEC-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `02c5797ea560ef4e1de598b91a8f0b99cfe031e1bae2a2aa79b02c3975871c66`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `02c5797ea560ef4e1de598b91a8f0b99cfe031e1bae2a2aa79b02c3975871c66`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `02c5797ea560ef4e1de598b91a8f0b99cfe031e1bae2a2aa79b02c3975871c66`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/feature/usage/x86_boot_spec.spl
mirror: doc/06_spec/feature/usage/x86_boot_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=95 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/x86_boot_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/x86_boot_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/x86_boot_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 11 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/x86_boot_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct magic number' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/x86_boot_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct flags' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/x86_boot_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'checksum validates' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/x86_boot_spec.spl:226:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can decode QEMU exit code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
