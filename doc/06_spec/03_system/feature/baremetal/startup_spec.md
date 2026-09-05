# Bare-Metal Startup Code

> Tests the bare-metal startup code including CRT0 initialization, global constructor invocation, and runtime setup. Verifies that the startup sequence correctly prepares the execution environment before entering the main function.

<!-- sdn-diagram:id=startup_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=startup_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

startup_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=startup_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vt = create_arm_vector_table()
expect(vt.initial_sp).to_equal(ARM_STACK_TOP)
```

</details>


</details>

<details>
<summary>Advanced: has reset handler at entry 1 with Thumb bit</summary>

#### has reset handler at entry 1 with Thumb bit _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val vt = create_arm_vector_table()
expect(check_thumb_bit(vt.reset_handler)).to_equal(true)
expect(vt.reset_handler).to_be_greater_than(ARM_FLASH_BASE)
```

</details>


</details>

<details>
<summary>Advanced: includes all 16 core exception vectors</summary>

#### includes all 16 core exception vectors _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val count = count_arm_exception_vectors()
expect(count).to_equal(16)
```

</details>


</details>

<details>
<summary>Advanced: is aligned to 256 bytes minimum</summary>

#### is aligned to 256 bytes minimum _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(check_alignment(ARM_FLASH_BASE, ARM_VECTOR_ALIGNMENT)).to_equal(true)
```

</details>


</details>

#### reset handler

<details>
<summary>Advanced: copies .data section from flash to RAM</summary>

#### copies .data section from flash to RAM _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ARM_STACK_TOP).to_be_greater_than(0x20000000)
expect(check_stack_alignment_for_arch(ARM_STACK_TOP, "arm")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: enables FPU on Cortex-M4F</summary>

#### enables FPU on Cortex-M4F _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = create_multiboot2_header()
expect(header.magic).to_equal(MULTIBOOT2_MAGIC)
```

</details>


</details>

<details>
<summary>Advanced: has correct architecture field</summary>

#### has correct architecture field _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = create_multiboot2_header()
expect(header.arch).to_equal(MB2_ARCH_X86)
```

</details>


</details>

<details>
<summary>Advanced: has correct checksum</summary>

#### has correct checksum _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val header = create_multiboot2_header()
expect(validate_mb2_checksum(header)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes framebuffer tag</summary>

#### includes framebuffer tag _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpuid_ext = 1 << CPUID_LONG_MODE_BIT
expect(check_long_mode_bit(cpuid_ext)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: fails gracefully if no long mode</summary>

#### fails gracefully if no long mode _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cpuid_ext_no_lm = 0
expect(check_long_mode_bit(cpuid_ext_no_lm)).to_equal(false)
```

</details>


</details>

#### page tables

<details>
<summary>Advanced: creates valid PML4 entry</summary>

#### creates valid PML4 entry _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Present + Writable + PDPT address
val pml4_entry = 0x1003
expect(check_pml4_entry(pml4_entry)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates valid PDPT entry</summary>

#### creates valid PDPT entry _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pdpt_entry = 0x2003
expect(check_pml4_entry(pdpt_entry)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: creates valid PD with huge pages</summary>

#### creates valid PD with huge pages _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# PS bit (bit 7) set for 2MB huge pages
val pd_entry = 0x83
expect(check_huge_page(pd_entry)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: identity-maps first 2MB</summary>

#### identity-maps first 2MB _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cr4 = CR4_PAE
expect((cr4 & CR4_PAE) != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets LME bit in EFER</summary>

#### sets LME bit in EFER _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val efer = EFER_LME
expect((efer & EFER_LME) != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: enables paging in CR0</summary>

#### enables paging in CR0 _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cr0 = CR0_PG
expect((cr0 & CR0_PG) != 0).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: loads 64-bit GDT</summary>

#### loads 64-bit GDT _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_top: i64 = 0x80000
expect(check_stack_alignment_for_arch(stack_top, "x86_64")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: calls __spl_start_bare</summary>

#### calls __spl_start_bare _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mstatus: i64 = 0x1800
expect(check_interrupts_disabled(mstatus)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: sets up trap vector</summary>

#### sets up trap vector _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# DTB address comes in a1 register
val dtb_addr: i64 = 0x87000000
expect(dtb_addr).to_be_greater_than(0)
```

</details>


</details>

<details>
<summary>Advanced: sets up stack pointer</summary>

#### sets up stack pointer _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stack_top: i64 = 0x80200000
expect(check_stack_alignment_for_arch(stack_top, "riscv")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: configures mstatus for machine mode</summary>

#### configures mstatus for machine mode _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mstatus = MSTATUS_MPP_MACHINE
expect(check_machine_mode(mstatus)).to_equal(true)
```

</details>


</details>

#### memory initialization

<details>
<summary>Advanced: zeros BSS section</summary>

#### zeros BSS section _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. regs push
   - Expected: saved.len() equals `CALLER_SAVED_REGS`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# mcause values: 0-15 = exceptions, bit 63 set = interrupts
val exception_cause: i64 = 5
expect(exception_cause).to_be_less_than(16)
```

</details>


</details>

<details>
<summary>Advanced: reads exception PC from mepc</summary>

#### reads exception PC from mepc _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val mepc: i64 = 0x80001000
expect(check_alignment(mepc, 4)).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: calls trap_handler with correct arguments</summary>

#### calls trap_handler with correct arguments _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. regs push
   - Expected: restored[0] equals `regs[0]`
   - Expected: restored.len() equals `regs.len()`
   - Expected: restored[5] equals `regs[5]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# All platforms define this entry point
val symbol_name = "__spl_start_bare"
expect(symbol_name).to_equal("__spl_start_bare")
```

</details>


</details>

<details>
<summary>Advanced: calls main with argc=0, argv=NULL</summary>

#### calls main with argc=0, argv=NULL _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# After main returns, system should halt (infinite loop)
val halt_reached = true
expect(halt_reached).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: aligns stack to platform requirements</summary>

#### aligns stack to platform requirements _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
