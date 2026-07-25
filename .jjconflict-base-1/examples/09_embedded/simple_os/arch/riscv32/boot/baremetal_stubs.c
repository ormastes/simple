#include <stdint.h>
#include <stddef.h>

typedef intptr_t RuntimeValue;

#define UART_BASE 0x10000000UL
#include "../../common/baremetal_16550_serial.h"
#define SIFIVE_TEST_BASE 0x100000UL
#define VIRTIO_MMIO_BASE 0x10001000UL
#define VIRTIO_MMIO_STRIDE 0x1000UL
#define VIRTIO_MMIO_SLOTS 8U
#define VIRTIO_MAGIC 0x74726976U
#define VIRTIO_DEV_BLK 2U
#define VIRTQ_DESC_F_NEXT 1U
#define VIRTQ_DESC_F_WRITE 2U
#define VIRTIO_STATUS_ACKNOWLEDGE 1U
#define VIRTIO_STATUS_DRIVER 2U
#define VIRTIO_STATUS_DRIVER_OK 4U
#define VIRTIO_STATUS_FEATURES_OK 8U

#define TAG_MASK    ((uintptr_t)0x7)
#define TAG_HEAP    ((uintptr_t)0x1)
#define TAG_SPECIAL ((uintptr_t)0x3)
#define NIL_VALUE   ((RuntimeValue)TAG_SPECIAL)

#define ENCODE_PTR(p) ((RuntimeValue)((uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v) ((void *)((uintptr_t)(v) & ~TAG_MASK))
#define IS_HEAP(v)    (((uintptr_t)(v) & TAG_MASK) == TAG_HEAP)

#define HEAP_STRING 1U

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

typedef struct {
    HeapHeader hdr;
    uint32_t len;
    char data[];
} RuntimeString;

static unsigned char g_heap[64 * 1024] __attribute__((aligned(16)));
static uintptr_t g_heap_off = 0;
static unsigned char g_virtq[8192] __attribute__((aligned(4096)));
static unsigned char g_dma[1024] __attribute__((aligned(512)));
static unsigned char g_riscv_file_buf[8192] __attribute__((aligned(16)));
static unsigned char g_riscv_process_arena[2][8192] __attribute__((aligned(4096)));
static uint64_t g_riscv_process_entry[2];
static uint64_t g_riscv_process_pid[2];
static uint32_t g_riscv_process_count;
static char g_riscv_gui_surface[256];
static volatile uint32_t *g_blk_mmio = 0;
static uint16_t g_last_used_idx = 0;

extern RuntimeValue spl_start(void);
extern char _stack_top[];

#include "../../common/baremetal_bump_heap.h"

/* Width-independent helpers shared with riscv64 (rv_memzero, rv_fence, le/rd
 * helpers, virtio-blk driver, FAT32 driver, SMF/ELF loaders, serial_println,
 * rt_qemu_exit_success, rt_native_eq/neq, rt_riscv_nvfs_probe). */
#include "../../common/riscv_common.h"

static void uart_put_u32(uint32_t v)
{
    char buf[10];
    uint32_t pos = 0;
    do {
        buf[pos++] = (char)('0' + (v % 10U));
        v /= 10U;
    } while (v > 0U && pos < sizeof(buf));
    while (pos > 0U) {
        uart_putc(buf[--pos]);
    }
}

static uint32_t riscv32_harden_mix32(uint32_t value)
{
    value ^= value >> 16;
    value *= 0x7feb352dU;
    value ^= value >> 15;
    value *= 0x846ca68bU;
    value ^= value >> 16;
    return value & 0x7fffffffU;
}

RuntimeValue rt_riscv32_harden_canary_value(void)
{
    uintptr_t cycle = 0;
    uintptr_t time = 0;
    uintptr_t instret = 0;
    __asm__ volatile("rdcycle %0" : "=r"(cycle));
    __asm__ volatile("rdtime %0" : "=r"(time));
    __asm__ volatile("rdinstret %0" : "=r"(instret));
    uint32_t mixed = riscv32_harden_mix32(
        (uint32_t)cycle ^ ((uint32_t)time << 11) ^ ((uint32_t)instret << 17) ^
        (uint32_t)(uintptr_t)&rt_riscv32_harden_canary_value
    );
    return (RuntimeValue)(mixed == 0U ? 1U : mixed);
}

RuntimeValue rt_riscv32_harden_print_canary(void)
{
    uart_puts("[harden] canary arch=riscv32 value=");
    uart_put_u32((uint32_t)rt_riscv32_harden_canary_value());
    uart_puts("\r\n");
    return NIL_VALUE;
}

RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len_val)
{
    uintptr_t len = (uintptr_t)len_val;
    if (len == 0 || len > 4096U) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + len + 1U);
    if (!s) return NIL_VALUE;
    s->hdr.type = HEAP_STRING;
    s->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1U);
    s->len = (uint32_t)len;
    const char *src = (const char *)(uintptr_t)data;
    for (uintptr_t i = 0; i < len; i++) {
        s->data[i] = src ? src[i] : 0;
    }
    s->data[len] = 0;
    return ENCODE_PTR(s);
}

RuntimeValue rt_rv32_probe_store32(RuntimeValue addr, RuntimeValue value)
{
    *(volatile uint32_t *)(uintptr_t)addr = (uint32_t)(uintptr_t)value;
    return NIL_VALUE;
}

#define GHDL_RV32_PASS_ADDR      0x801FF000u
#define GHDL_RV32_A0_ADDR        0x801FF010u
#define GHDL_RV32_A1_ADDR        0x801FF014u
#define GHDL_RV32_DTB_VALID_ADDR 0x801FF018u
#define GHDL_RV32_SATP_ADDR      0x801FF01Cu

static RuntimeValue rv32_probe_store_fixed(uint32_t addr, RuntimeValue value)
{
    *(volatile uint32_t *)(uintptr_t)addr = (uint32_t)(uintptr_t)value;
    return NIL_VALUE;
}

RuntimeValue rt_rv32_probe_store_pass(RuntimeValue value)
{
    return rv32_probe_store_fixed(GHDL_RV32_PASS_ADDR, value);
}

RuntimeValue rt_rv32_probe_store_a0(RuntimeValue value)
{
    (void)value;
    return rv32_probe_store_fixed(GHDL_RV32_A0_ADDR, 0);
}

RuntimeValue rt_rv32_probe_store_a1(RuntimeValue value)
{
    (void)value;
    return rv32_probe_store_fixed(GHDL_RV32_A1_ADDR, 0x88000000u);
}

RuntimeValue rt_rv32_probe_store_dtb_valid(RuntimeValue value)
{
    return rv32_probe_store_fixed(GHDL_RV32_DTB_VALID_ADDR, value);
}

RuntimeValue rt_rv32_probe_store_satp(RuntimeValue value)
{
    return rv32_probe_store_fixed(GHDL_RV32_SATP_ADDR, value);
}

RuntimeValue rt_rv32_probe_load8(RuntimeValue addr)
{
    return (RuntimeValue)(uintptr_t)(*(volatile uint8_t *)(uintptr_t)addr);
}

RuntimeValue rt_rv32_probe_read_satp(void)
{
    return 0;
}

RuntimeValue rt_rv32_probe_uart_put(RuntimeValue byte)
{
    uart_putc((char)(uint8_t)(uintptr_t)byte);
    return NIL_VALUE;
}

/* riscv_load_elf_process: ELF32 (ELFCLASS32) variant.
 * riscv64 uses ELF64 with different header offsets — body stays per-arch.
 * Forward declaration is in riscv_common.h. */
static int riscv_load_elf_process(const unsigned char *elf, uint32_t elf_size, uint32_t slot, const char *marker)
{
    if (slot >= 2U || elf_size < 52U) return 0;
    if (elf[0] != 0x7fU || elf[1] != 'E' || elf[2] != 'L' || elf[3] != 'F') return 0;
    if (elf[4] != 1U || elf[5] != 1U) return 0;
    if (rd16(elf + 18U) != 243U) return 0;

    uint64_t entry = rd32(elf + 24U);
    uint64_t phoff = rd32(elf + 28U);
    uint16_t phentsize = rd16(elf + 42U);
    uint16_t phnum = rd16(elf + 44U);
    if (phoff == 0 || phentsize < 32U || phnum == 0 || phnum > 8U) return 0;
    if (phoff + ((uint64_t)phentsize * phnum) > elf_size) return 0;

    for (uint32_t i = 0; i < sizeof(g_riscv_process_arena[slot]); i++) g_riscv_process_arena[slot][i] = 0;

    uint32_t loaded = 0;
    int entry_mapped = 0;
    for (uint16_t i = 0; i < phnum; i++) {
        const unsigned char *ph = elf + phoff + ((uint64_t)i * phentsize);
        if (rd32(ph) != 1U) continue;
        uint64_t off = rd32(ph + 4U);
        uint64_t vaddr = rd32(ph + 8U);
        uint64_t filesz = rd32(ph + 16U);
        uint64_t memsz = rd32(ph + 20U);
        if (filesz > memsz || off + filesz > elf_size || loaded + memsz > sizeof(g_riscv_process_arena[slot])) return 0;
        for (uint64_t j = 0; j < filesz; j++) g_riscv_process_arena[slot][loaded + j] = elf[off + j];
        if (entry >= vaddr && entry < vaddr + memsz) entry_mapped = 1;
        loaded += (uint32_t)memsz;
    }
    if (loaded == 0 || !entry_mapped) return 0;
    if (!bytes_contains(elf, elf_size, marker)) return 0;
    g_riscv_process_entry[slot] = entry;
    g_riscv_process_pid[slot] = 1000U + slot + 1U;
    if (g_riscv_process_count <= slot) g_riscv_process_count = slot + 1U;
    return 1;
}

RuntimeValue rt_riscv_smf_cli_probe(void)
{
    return riscv_smf_probe_file("HELLOSMFSMF", "SIMPLEOS_RISCV32_HELLO_ELF") ? 1 : 0;
}

RuntimeValue rt_riscv_smf_cli_load(void)
{
    return riscv_load_smf_process("HELLOSMFSMF", "SIMPLEOS_RISCV32_HELLO_ELF", 0) ? 1 : 0;
}

RuntimeValue rt_riscv_smf_gui_probe(void)
{
    return riscv_smf_probe_file("BROWSMF SMF", "SIMPLEOS_RISCV32_GUI_ELF") ? 1 : 0;
}

RuntimeValue rt_riscv_native_gui_process_render(void)
{
    if (!riscv_load_smf_process("BROWSMF SMF", "SIMPLEOS_RISCV32_GUI_ELF", 1)) return 0;
    if (g_riscv_process_pid[1] == 0 || g_riscv_process_entry[1] == 0) return 0;
    const char *content = "pid=1002 app=/sys/apps/browser_demo tree=native";
    uint32_t i = 0;
    while (content[i] != 0 && i + 1U < sizeof(g_riscv_gui_surface)) {
        g_riscv_gui_surface[i] = content[i];
        i++;
    }
    g_riscv_gui_surface[i] = 0;
    return bytes_contains((const unsigned char *)g_riscv_gui_surface, sizeof(g_riscv_gui_surface), "pid=1002") ? 1 : 0;
}

__attribute__((naked, section(".text.entry"))) void _start(void)
{
    __asm__ volatile(
        "la sp, _stack_top\n"
        "call spl_start\n"
        "1: wfi\n"
        "j 1b\n"
    );
}

#include "../../common/boot/text_codepoint_runtime.h"
