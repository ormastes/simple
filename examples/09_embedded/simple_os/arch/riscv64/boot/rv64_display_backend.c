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
 * pages from that owner. */
spl_u64 rt_riscv_noalloc_alloc_page(void);

#include "../../../../../../src/os/kernel/arch/riscv64/boot/rv64_display_backend.inc.c"
