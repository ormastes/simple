# Bare-Metal Startup Code

> Tests the bare-metal startup code including CRT0 initialization, global constructor invocation, and runtime setup. Verifies that the startup sequence correctly prepares the execution environment before entering the main function.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare-Metal Startup Code

Tests the bare-metal startup code including CRT0 initialization, global constructor invocation, and runtime setup. Verifies that the startup sequence correctly prepares the execution environment before entering the main function.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Baremetal |
| Status | In Progress |
| Source | `test/03_system/feature/baremetal/startup_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the bare-metal startup code including CRT0 initialization, global constructor
invocation, and runtime setup. Verifies that the startup sequence correctly
prepares the execution environment before entering the main function.

## Scenarios

### ARM Cortex-M Startup

#### vector table

<details>
<summary>Advanced: has correct initial SP at entry 0</summary>

#### has correct initial SP at entry 0 _(slow)_

- has correct initial SP at entry 0
   - Expected: vt.initial_sp equals `ARM_STACK_TOP`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct initial SP at entry 0")
val vt = create_arm_vector_table()
expect(vt.initial_sp).to_equal(ARM_STACK_TOP)
```

</details>


</details>

<details>
<summary>Advanced: has reset handler at entry 1 with Thumb bit</summary>

#### has reset handler at entry 1 with Thumb bit _(slow)_

- has reset handler at entry 1 with Thumb bit
   - Expected: check_thumb_bit(vt.reset_handler) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has reset handler at entry 1 with Thumb bit")
val vt = create_arm_vector_table()
expect(check_thumb_bit(vt.reset_handler)).to_equal(true)
expect(vt.reset_handler).to_be_greater_than(ARM_FLASH_BASE)
```

</details>


</details>

<details>
<summary>Advanced: includes all 16 core exception vectors</summary>

#### includes all 16 core exception vectors _(slow)_

- includes all 16 core exception vectors
   - Expected: count equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes all 16 core exception vectors")
val count = count_arm_exception_vectors()
expect(count).to_equal(16)
```

</details>


</details>

<details>
<summary>Advanced: is aligned to 256 bytes minimum</summary>

#### is aligned to 256 bytes minimum _(slow)_

- is aligned to 256 bytes minimum
   - Expected: check_alignment(ARM_FLASH_BASE, ARM_VECTOR_ALIGNMENT) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("is aligned to 256 bytes minimum")
expect(check_alignment(ARM_FLASH_BASE, ARM_VECTOR_ALIGNMENT)).to_equal(true)
```

</details>


</details>

#### reset handler

<details>
<summary>Advanced: copies .data section from flash to RAM</summary>

#### copies .data section from flash to RAM _(slow)_

- copies .data section from flash to RAM
   - Expected: copied[0] equals `10`
   - Expected: copied.len() equals `5`
   - Expected: copied[4] equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("copies .data section from flash to RAM")
val src = [10, 20, 30, 40, 50]
val copied = simulate_data_copy(src)
expect(copied[0]).to_equal(10)
expect(copied.len()).to_equal(5)
expect(copied[4]).to_equal(50)
```

</details>


</details>

<details>
<summary>Advanced: zeros .bss section</summary>

#### zeros .bss section _(slow)_

- zeros .bss section
   - Expected: bss[0] equals `0`
   - Expected: bss.len() equals `8`
   - Expected: bss[7] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zeros .bss section")
val bss = simulate_bss_zero(8)
expect(bss[0]).to_equal(0)
expect(bss.len()).to_equal(8)
expect(bss[7]).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: sets up stack pointer correctly</summary>

#### sets up stack pointer correctly _(slow)_

- sets up stack pointer correctly
   - Expected: check_stack_alignment_for_arch(ARM_STACK_TOP, "arm") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up stack pointer correctly")
expect(ARM_STACK_TOP).to_be_greater_than(0x20000000)
expect(check_stack_alignment_for_arch(ARM_STACK_TOP, "arm")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: enables FPU on Cortex-M4F</summary>

#### enables FPU on Cortex-M4F _(slow)_

- enables FPU on Cortex-M4F
   - Expected: cp10_enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables FPU on Cortex-M4F")
# CPACR CP10/CP11 full access = bits 20-23 set
val cpacr_value = CP10_ENABLE
val cp10_enabled = (cpacr_value & 0x00F00000) != 0
expect(cp10_enabled).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: calls __spl_start_bare</summary>

#### calls __spl_start_bare _(slow)_

- calls __spl_start_bare


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls __spl_start_bare")
# Verify reset handler address is in flash (would branch to __spl_start_bare)
val vt = create_arm_vector_table()
expect(vt.reset_handler).to_be_greater_than(ARM_FLASH_BASE)
expect(vt.reset_handler).to_be_less_than(ARM_FLASH_BASE + 0x100000)
```

</details>


</details>

<details>
<summary>Advanced: loops forever if main returns</summary>

#### loops forever if main returns _(slow)_

- loops forever if main returns
   - Expected: check_thumb_bit(loop_addr) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loops forever if main returns")
# Default infinite loop address is valid
val loop_addr = ARM_FLASH_BASE + 0x1001
expect(check_thumb_bit(loop_addr)).to_equal(true)
```

</details>


</details>

#### exception handlers

<details>
<summary>Advanced: has default handler for all unimplemented interrupts</summary>

#### has default handler for all unimplemented interrupts _(slow)_

- has default handler for all unimplemented interrupts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has default handler for all unimplemented interrupts")
val vt = create_arm_vector_table()
# All exception entries should be non-zero (point to handlers)
expect(vt.nmi).to_be_greater_than(0)
expect(vt.hard_fault).to_be_greater_than(0)
expect(vt.svcall).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: has hard fault handler that saves fault info</summary>

#### has hard fault handler that saves fault info _(slow)_

- has hard fault handler that saves fault info


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has hard fault handler that saves fault info")
# CFSR, HFSR, DFSR, MMFAR, BFAR are SCB registers
val CFSR_ADDR: i64 = 0xE000ED28
val HFSR_ADDR: i64 = 0xE000ED2C
# Addresses are in valid SCB range
expect(CFSR_ADDR).to_be_greater_than(0xE000ED00)
expect(HFSR_ADDR).to_be_greater_than(0xE000ED00)
```

</details>


</details>

### x86_64 Startup

#### multiboot2 header

<details>
<summary>Advanced: has correct magic number</summary>

#### has correct magic number _(slow)_

- has correct magic number
   - Expected: header.magic equals `MULTIBOOT2_MAGIC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct magic number")
val header = create_multiboot2_header()
expect(header.magic).to_equal(MULTIBOOT2_MAGIC)
```

</details>


</details>

<details>
<summary>Advanced: has correct architecture field</summary>

#### has correct architecture field _(slow)_

- has correct architecture field
   - Expected: header.arch equals `MB2_ARCH_X86`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct architecture field")
val header = create_multiboot2_header()
expect(header.arch).to_equal(MB2_ARCH_X86)
```

</details>


</details>

<details>
<summary>Advanced: has correct checksum</summary>

#### has correct checksum _(slow)_

- has correct checksum
   - Expected: validate_mb2_checksum(header) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has correct checksum")
val header = create_multiboot2_header()
expect(validate_mb2_checksum(header)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes framebuffer tag</summary>

#### includes framebuffer tag _(slow)_

- includes framebuffer tag
   - Expected: fb.width equals `1024`
   - Expected: fb.height equals `768`
   - Expected: fb.depth equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes framebuffer tag")
val fb = create_framebuffer_tag()
expect(fb.width).to_equal(1024)
expect(fb.height).to_equal(768)
expect(fb.depth).to_equal(32)
```

</details>


</details>

#### long mode check

<details>
<summary>Advanced: detects CPUID support</summary>

#### detects CPUID support _(slow)_

- detects CPUID support
   - Expected: has_cpuid is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects CPUID support")
# EFLAGS bit 21 toggleable means CPUID supported
val eflags_with_id = 0x200000
val has_cpuid = (eflags_with_id & 0x200000) != 0
expect(has_cpuid).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: detects long mode support</summary>

#### detects long mode support _(slow)_

- detects long mode support
   - Expected: check_long_mode_bit(cpuid_ext) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects long mode support")
val cpuid_ext = 1 << CPUID_LONG_MODE_BIT
expect(check_long_mode_bit(cpuid_ext)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: fails gracefully if no long mode</summary>

#### fails gracefully if no long mode _(slow)_

- fails gracefully if no long mode
   - Expected: check_long_mode_bit(cpuid_ext_no_lm) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("fails gracefully if no long mode")
val cpuid_ext_no_lm = 0
expect(check_long_mode_bit(cpuid_ext_no_lm)).to_equal(false)
```

</details>


</details>

#### page tables

<details>
<summary>Advanced: creates valid PML4 entry</summary>

#### creates valid PML4 entry _(slow)_

- creates valid PML4 entry
   - Expected: check_pml4_entry(pml4_entry) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates valid PML4 entry")
# Present + Writable + PDPT address
val pml4_entry = 0x1003
expect(check_pml4_entry(pml4_entry)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates valid PDPT entry</summary>

#### creates valid PDPT entry _(slow)_

- creates valid PDPT entry
   - Expected: check_pml4_entry(pdpt_entry) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates valid PDPT entry")
val pdpt_entry = 0x2003
expect(check_pml4_entry(pdpt_entry)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates valid PD with huge pages</summary>

#### creates valid PD with huge pages _(slow)_

- creates valid PD with huge pages
   - Expected: check_huge_page(pd_entry) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates valid PD with huge pages")
# PS bit (bit 7) set for 2MB huge pages
val pd_entry = 0x83
expect(check_huge_page(pd_entry)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: identity-maps first 2MB</summary>

#### identity-maps first 2MB _(slow)_

- identity-maps first 2MB
   - Expected: check_pml4_entry(first_pd) is true
   - Expected: check_huge_page(first_pd) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("identity-maps first 2MB")
# First PD entry: base=0, present, writable, huge
val first_pd = 0x83
expect(check_pml4_entry(first_pd)).to_equal(true)
expect(check_huge_page(first_pd)).to_equal(true)
```

</details>


</details>

#### mode transition

<details>
<summary>Advanced: enables PAE in CR4</summary>

#### enables PAE in CR4 _(slow)_

- enables PAE in CR4
   - Expected: (cr4 & CR4_PAE) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables PAE in CR4")
val cr4 = CR4_PAE
expect((cr4 & CR4_PAE) != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets LME bit in EFER</summary>

#### sets LME bit in EFER _(slow)_

- sets LME bit in EFER
   - Expected: (efer & EFER_LME) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets LME bit in EFER")
val efer = EFER_LME
expect((efer & EFER_LME) != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: enables paging in CR0</summary>

#### enables paging in CR0 _(slow)_

- enables paging in CR0
   - Expected: (cr0 & CR0_PG) != 0 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enables paging in CR0")
val cr0 = CR0_PG
expect((cr0 & CR0_PG) != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: loads 64-bit GDT</summary>

#### loads 64-bit GDT _(slow)_

- loads 64-bit GDT
   - Expected: code_seg equals `0x08`
   - Expected: data_seg equals `0x10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("loads 64-bit GDT")
# GDT needs code segment (0x08) and data segment (0x10)
val code_seg: i64 = 0x08
val data_seg: i64 = 0x10
expect(code_seg).to_equal(0x08)
expect(data_seg).to_equal(0x10)
```

</details>


</details>

<details>
<summary>Advanced: jumps to 64-bit code</summary>

#### jumps to 64-bit code _(slow)_

- jumps to 64-bit code
   - Expected: target_selector equals `0x08`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("jumps to 64-bit code")
# Far jump to code segment selector
val target_selector: i64 = 0x08
expect(target_selector).to_equal(0x08)
```

</details>


</details>

#### 64-bit initialization

<details>
<summary>Advanced: zeros BSS section</summary>

#### zeros BSS section _(slow)_

- zeros BSS section
   - Expected: bss[0] equals `0`
   - Expected: bss.len() equals `16`
   - Expected: bss[15] equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zeros BSS section")
val bss = simulate_bss_zero(16)
expect(bss[0]).to_equal(0)
expect(bss.len()).to_equal(16)
expect(bss[15]).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: sets up 64-bit stack</summary>

#### sets up 64-bit stack _(slow)_

- sets up 64-bit stack
   - Expected: check_stack_alignment_for_arch(stack_top, "x86_64") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up 64-bit stack")
val stack_top: i64 = 0x80000
expect(check_stack_alignment_for_arch(stack_top, "x86_64")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: calls __spl_start_bare</summary>

#### calls __spl_start_bare _(slow)_

- calls __spl_start_bare


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls __spl_start_bare")
# Entry point symbol exists and is callable
val entry_addr: i64 = 0x100000
expect(entry_addr).to_be_greater_than(0)
```

</details>


</details>

### RISC-V Startup

#### hart initialization

<details>
<summary>Advanced: disables interrupts on entry</summary>

#### disables interrupts on entry _(slow)_

- disables interrupts on entry
   - Expected: check_interrupts_disabled(mstatus) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("disables interrupts on entry")
val mstatus: i64 = 0x1800
expect(check_interrupts_disabled(mstatus)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up trap vector</summary>

#### sets up trap vector _(slow)_

- sets up trap vector
   - Expected: mode equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up trap vector")
val mtvec: i64 = 0x80000004
val parsed = parse_mtvec(mtvec)
val base = parsed[0]
val mode = parsed[1]
expect(base).to_be_greater_than(0)
expect(mode).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: parks secondary harts in WFI</summary>

#### parks secondary harts in WFI _(slow)_

- parks secondary harts in WFI
   - Expected: should_park is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parks secondary harts in WFI")
# Only hart 0 proceeds, others enter WFI loop
val hart_id: i64 = 1
val should_park = hart_id != 0
expect(should_park).to_equal(true)
```

</details>


</details>

#### primary hart setup

<details>
<summary>Advanced: saves device tree blob address</summary>

#### saves device tree blob address _(slow)_

- saves device tree blob address


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("saves device tree blob address")
# DTB address comes in a1 register
val dtb_addr: i64 = 0x87000000
expect(dtb_addr).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: sets up stack pointer</summary>

#### sets up stack pointer _(slow)_

- sets up stack pointer
   - Expected: check_stack_alignment_for_arch(stack_top, "riscv") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up stack pointer")
val stack_top: i64 = 0x80200000
expect(check_stack_alignment_for_arch(stack_top, "riscv")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: configures mstatus for machine mode</summary>

#### configures mstatus for machine mode _(slow)_

- configures mstatus for machine mode
   - Expected: check_machine_mode(mstatus) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("configures mstatus for machine mode")
val mstatus = MSTATUS_MPP_MACHINE
expect(check_machine_mode(mstatus)).to_equal(true)
```

</details>


</details>

#### memory initialization

<details>
<summary>Advanced: zeros BSS section</summary>

#### zeros BSS section _(slow)_

- zeros BSS section
   - Expected: bss.len() equals `32`
   - Expected: all_zero is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("zeros BSS section")
val bss = simulate_bss_zero(32)
expect(bss.len()).to_equal(32)
var all_zero = true
for val_item in bss:
    if val_item != 0:
        all_zero = false
expect(all_zero).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: copies .data section from flash to RAM</summary>

#### copies .data section from flash to RAM _(slow)_

- copies .data section from flash to RAM
   - Expected: copied[0] equals `100`
   - Expected: copied.len() equals `3`
   - Expected: copied[2] equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("copies .data section from flash to RAM")
val src = [100, 200, 300]
val copied = simulate_data_copy(src)
expect(copied[0]).to_equal(100)
expect(copied.len()).to_equal(3)
expect(copied[2]).to_equal(300)
```

</details>


</details>

#### trap handling

<details>
<summary>Advanced: saves all caller-saved registers</summary>

#### saves all caller-saved registers _(slow)_

- saves all caller-saved registers
   - Expected: saved.len() equals `CALLER_SAVED_REGS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("saves all caller-saved registers")
var regs: [i64] = []
for i in 0..CALLER_SAVED_REGS:
    regs.push(i * 100)
val saved = simulate_register_save(regs)
expect(saved.len()).to_equal(CALLER_SAVED_REGS)
```

</details>


</details>

<details>
<summary>Advanced: reads trap cause from mcause</summary>

#### reads trap cause from mcause _(slow)_

- reads trap cause from mcause


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads trap cause from mcause")
# mcause values: 0-15 = exceptions, bit 63 set = interrupts
val exception_cause: i64 = 5
expect(exception_cause).to_be_less_than(16)
```

</details>


</details>

<details>
<summary>Advanced: reads exception PC from mepc</summary>

#### reads exception PC from mepc _(slow)_

- reads exception PC from mepc
   - Expected: check_alignment(mepc, 4) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reads exception PC from mepc")
val mepc: i64 = 0x80001000
expect(check_alignment(mepc, 4)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: calls trap_handler with correct arguments</summary>

#### calls trap_handler with correct arguments _(slow)_

- calls trap_handler with correct arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls trap_handler with correct arguments")
# trap_handler(mcause, mepc, mtval)
val mcause: i64 = 2
val mepc: i64 = 0x80001000
val mtval: i64 = 0x00000000
expect(mcause).to_be_less_than(16)
expect(mepc).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: restores registers and returns with mret</summary>

#### restores registers and returns with mret _(slow)_

- restores registers and returns with mret
   - Expected: restored[0] equals `regs[0]`
   - Expected: restored.len() equals `regs.len()`
   - Expected: restored[5] equals `regs[5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("restores registers and returns with mret")
var regs: [i64] = []
for i in 0..CALLER_SAVED_REGS:
    regs.push(i * 100)
val saved = simulate_register_save(regs)
val restored = simulate_register_restore(saved)
expect(restored[0]).to_equal(regs[0])
expect(restored.len()).to_equal(regs.len())
expect(restored[5]).to_equal(regs[5])
```

</details>


</details>

#### secondary harts

<details>
<summary>Advanced: sets up per-hart stack</summary>

#### sets up per-hart stack _(slow)_

- sets up per-hart stack
   - Expected: hart1_sp equals `stack_top - HART_STACK_SIZE`
   - Expected: hart2_sp equals `stack_top - 2 * HART_STACK_SIZE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("sets up per-hart stack")
val stack_top: i64 = 0x80200000
val hart1_sp = calculate_hart_stack(1, stack_top)
val hart2_sp = calculate_hart_stack(2, stack_top)
expect(hart1_sp).to_equal(stack_top - HART_STACK_SIZE)
expect(hart2_sp).to_equal(stack_top - 2 * HART_STACK_SIZE)
expect(hart1_sp).to_be_greater_than(hart2_sp)
```

</details>


</details>

<details>
<summary>Advanced: enters WFI loop</summary>

#### enters WFI loop _(slow)_

- enters WFI loop
   - Expected: is_secondary is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("enters WFI loop")
# Secondary harts wait for IPI
val hart_id: i64 = 3
val is_secondary = hart_id != 0
expect(is_secondary).to_equal(true)
```

</details>


</details>

### Cross-Platform Startup

<details>
<summary>Advanced: provides __spl_start_bare symbol</summary>

#### provides __spl_start_bare symbol _(slow)_

- provides __spl_start_bare symbol
   - Expected: symbol_name equals `__spl_start_bare`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides __spl_start_bare symbol")
# All platforms define this entry point
val symbol_name = "__spl_start_bare"
expect(symbol_name).to_equal("__spl_start_bare")
```

</details>


</details>

<details>
<summary>Advanced: calls main with argc=0, argv=NULL</summary>

#### calls main with argc=0, argv=NULL _(slow)_

- calls main with argc=0, argv=NULL
   - Expected: argc equals `0`
   - Expected: argv_null equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls main with argc=0, argv=NULL")
val argc: i64 = 0
val argv_null: i64 = 0
expect(argc).to_equal(0)
expect(argv_null).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: handles main return gracefully</summary>

#### handles main return gracefully _(slow)_

- handles main return gracefully
   - Expected: halt_reached is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles main return gracefully")
# After main returns, system should halt (infinite loop)
val halt_reached = true
expect(halt_reached).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: aligns stack to platform requirements</summary>

#### aligns stack to platform requirements _(slow)_

- aligns stack to platform requirements
   - Expected: check_stack_alignment_for_arch(arm_sp, "arm") is true
   - Expected: check_stack_alignment_for_arch(x86_sp, "x86_64") is true
   - Expected: check_stack_alignment_for_arch(riscv_sp, "riscv") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("aligns stack to platform requirements")
val arm_sp: i64 = 0x20020000
val x86_sp: i64 = 0x80000
val riscv_sp: i64 = 0x80200000
expect(check_stack_alignment_for_arch(arm_sp, "arm")).to_equal(true)
expect(check_stack_alignment_for_arch(x86_sp, "x86_64")).to_equal(true)
expect(check_stack_alignment_for_arch(riscv_sp, "riscv")).to_equal(true)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 50 |
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

- Canonical SPipe generation for source `3ad066ccedfe409b26f9f8c2e1a3fa3b3bc2f0b524e65d9876fe1b7f635471d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ad066ccedfe409b26f9f8c2e1a3fa3b3bc2f0b524e65d9876fe1b7f635471d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ad066ccedfe409b26f9f8c2e1a3fa3b3bc2f0b524e65d9876fe1b7f635471d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/baremetal/startup_spec.spl
mirror: doc/06_spec/03_system/feature/baremetal/startup_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/baremetal/startup_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/baremetal/startup_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/baremetal/startup_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 20 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/baremetal/startup_spec.spl:224:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct initial SP at entry 0' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/startup_spec.spl:230:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has reset handler at entry 1 with Thumb bit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/baremetal/startup_spec.spl:237:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes all 16 core exception vectors' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
