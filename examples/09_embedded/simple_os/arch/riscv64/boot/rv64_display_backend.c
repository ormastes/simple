/* VirtIO-GPU display backend for riscv64 entries under examples/.
 *
 * native-build derives its boot directory as `<entry>.parent()/boot`, so this
 * directory is the boot set for every riscv64 entry here -- and it carried no
 * PCI or VirtIO-GPU code at all. The real driver lives in the src/ boot dir,
 * which only src/os/kernel/arch/riscv64/user_entry.spl reaches. Rather than
 * copy it (two divergent VirtIO-GPU drivers is exactly the duplicate-sibling
 * trap this tree keeps hitting), both boot dirs now #include one shared
 * fragment, so there is a single implementation.
 *
 * Keep it libc-free: no includes, no malloc, no formatted I/O.
 */

typedef long long spl_i64;
typedef unsigned long long spl_u64;
typedef unsigned int spl_u32;
typedef unsigned short spl_u16;
typedef unsigned char spl_u8;

/* Page allocation policy is pure Simple; the DMA/virtqueue setup below consumes
 * pages from that owner. Declared under its `spl_`-prefixed name because that
 * is the seed mangler's keep-the-ABI-name convention -- see the note in
 * src/os/kernel/arch/riscv64/noalloc_pmm_runtime.spl. */
spl_u64 spl_riscv_noalloc_alloc_page(void);

/* UART transport stays in C, matching the ownership split stated in
 * freestanding_runtime.c ("C retains transport, UART, MMIO and session
 * state"). Extracted from that file, which never compiled and so never linked
 * this anywhere. */
#define RT_RISCV_UART_BASE 0x10000000ULL

static void uart_put_byte(spl_u8 byte) {
    *(volatile spl_u8 *)RT_RISCV_UART_BASE = byte;
}

void rt_riscv_uart_put(spl_u64 byte) {
    uart_put_byte((spl_u8)byte);
}

#include "../../../../../../src/os/kernel/arch/riscv64/boot/rv64_display_backend.inc.c"
