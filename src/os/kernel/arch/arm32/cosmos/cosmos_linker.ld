/* Cosmos+ OpenSSD 8Ch8Way v3.0.0 reserves 0x00100000..0x001fffff
 * for firmware/static memory. DMA starts at 0x00200000.
 */

OUTPUT_ARCH(arm)
OUTPUT_FORMAT("elf32-littlearm")
ENTRY(_start)

MEMORY {
    FIRMWARE : ORIGIN = 0x00100000, LENGTH = 0x00100000
}

SECTIONS {
    . = ORIGIN(FIRMWARE);
    __cosmos_rx_start = .;
    .text : ALIGN(8) {
        KEEP(*(.text.start))
        *(.text*)
    } > FIRMWARE
    .note.cosmos.profile : ALIGN(4) {
        KEEP(*(.note.cosmos.profile))
    } > FIRMWARE
    .rodata : ALIGN(8) { *(.rodata*) } > FIRMWARE
    .ARM.extab : ALIGN(4) { *(.ARM.extab*) } > FIRMWARE
    .ARM.exidx : ALIGN(4) { *(.ARM.exidx*) } > FIRMWARE
    . = ALIGN(0x1000);
    __cosmos_rx_end = .;
    __cosmos_rw_start = .;
    .boot_sync __cosmos_rw_start : ALIGN(4) {
        KEEP(*(.data.boot_sync))
    } > FIRMWARE
    .data : ALIGN(8) { *(.data*) } > FIRMWARE
    .bss (NOLOAD) : ALIGN(8) {
        _sbss = .;
        *(.bss*)
        *(COMMON)
        _ebss = .;
    } > FIRMWARE
    _image_end = .;
    . = ALIGN(0x1000);
    __cosmos_rw_end = .;

    .mmu_table (NOLOAD) : ALIGN(16384) {
        _mmu_table_start = .;
        _mmu_l1_table_start = .;
        KEEP(*(.mmu_table.l1))
        _mmu_l1_table_end = .;
        . = ALIGN(1024);
        _mmu_firmware_l2_table_start = .;
        KEEP(*(.mmu_table.firmware_l2))
        _mmu_firmware_l2_table_end = .;
        . = ALIGN(1024);
        _mmu_ocm_l2_table_start = .;
        KEEP(*(.mmu_table.ocm_l2))
        _mmu_ocm_l2_table_end = .;
        _mmu_table_end = .;
    } > FIRMWARE

    .irq_stacks (NOLOAD) : ALIGN(16) {
        _irq_stacks_start = .;
        _irq_stack_cpu0_bottom = .;
        . += 0x400;
        _irq_stack_cpu0_top = .;
        . = ALIGN(16);
        _irq_stack_cpu1_bottom = .;
        . += 0x400;
        _irq_stack_cpu1_top = .;
        _irq_stacks_end = .;
    } > FIRMWARE

    .stack (NOLOAD) : ALIGN(16) {
        _stack_bottom = .;
        . += 0x10000;
        _stack_top = .;
    } > FIRMWARE
    _firmware_end = .;

    ASSERT(_start == ORIGIN(FIRMWARE),
           "Cosmos vectors must remain at the firmware base")
    ASSERT((cosmos_vectors_end - _start) == 0x20,
           "Cosmos vector table must contain eight ARM entries")
    ASSERT(SIZEOF(.boot_sync) == 4,
           "Cosmos BSS-ready synchronization word must be initialized")
    ASSERT((_sbss & 3) == 0 && (_ebss & 3) == 0,
           "Cosmos BSS bounds must be word aligned")
    ASSERT((_mmu_l1_table_start & 0x3fff) == 0,
           "Cosmos L1 table must be 16 KiB aligned")
    ASSERT((_mmu_l1_table_end - _mmu_l1_table_start) == 0x4000,
           "Cosmos L1 table must contain 4096 entries")
    ASSERT((_mmu_firmware_l2_table_start & 0x3ff) == 0,
           "Cosmos firmware L2 table must be 1 KiB aligned")
    ASSERT((_mmu_firmware_l2_table_end - _mmu_firmware_l2_table_start) == 0x400,
           "Cosmos firmware L2 table must contain 256 entries")
    ASSERT((_mmu_ocm_l2_table_start & 0x3ff) == 0,
           "Cosmos OCM L2 table must be 1 KiB aligned")
    ASSERT((_mmu_ocm_l2_table_end - _mmu_ocm_l2_table_start) == 0x400,
           "Cosmos OCM L2 table must contain 256 entries")
    ASSERT((__cosmos_rx_start & 0xfff) == 0 &&
           (__cosmos_rx_end & 0xfff) == 0 &&
           (__cosmos_rw_start & 0xfff) == 0 &&
           (__cosmos_rw_end & 0xfff) == 0,
           "Cosmos W^X page boundaries must be 4 KiB aligned")
    ASSERT(__cosmos_rx_start == ORIGIN(FIRMWARE) &&
           __cosmos_rx_start < __cosmos_rx_end &&
           __cosmos_rx_end == __cosmos_rw_start &&
           __cosmos_rw_start <= _image_end &&
           _image_end <= __cosmos_rw_end,
           "Cosmos W^X section order is invalid")
    ASSERT(_image_end <= _mmu_table_start,
           "Cosmos image overlaps MMU tables")
    ASSERT(_mmu_table_end <= _irq_stacks_start,
           "Cosmos MMU tables overlap IRQ stacks")
    ASSERT((_irq_stack_cpu0_top & 7) == 0 &&
           (_irq_stack_cpu1_top & 7) == 0,
           "Cosmos IRQ stack tops must be 8-byte aligned")
    ASSERT((_irq_stack_cpu0_top - _irq_stack_cpu0_bottom) == 0x400,
           "Cosmos CPU0 IRQ stack size changed")
    ASSERT((_irq_stack_cpu1_top - _irq_stack_cpu1_bottom) == 0x400,
           "Cosmos CPU1 IRQ stack size changed")
    ASSERT(_irq_stacks_end <= _stack_bottom,
           "Cosmos IRQ stacks overlap boot stack")
    ASSERT(_firmware_end <= 0x00200000,
           "Cosmos firmware/table/stack overlaps official DMA window")
}
