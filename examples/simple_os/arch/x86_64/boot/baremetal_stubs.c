/*
 * baremetal_stubs.c -- x86_64 baremetal runtime stubs
 *
 * Provides:
 *   - Multiboot1 header (with framebuffer request, in .multiboot section)
 *   - Heap allocator (malloc/free/realloc/calloc), rt_alloc
 *   - Memory primitives (memcpy/memset/memmove/memcmp/strlen)
 *   - Serial I/O (rt_println_value, serial_println)
 *   - Framebuffer helpers (rt_framebuffer_copy, rt_fb_fill_rect)
 *   - Multiboot info accessors (rt_multiboot_fb_addr, etc.)
 */

#include <stddef.h>
#include <stdint.h>

/* ================================================================
 * Multiboot1 header — placed in .multiboot (linker script keeps it early)
 *
 * flags bit 0 = page-align modules
 * flags bit 1 = provide memory info
 * flags bit 2 = provide video mode fields
 * ================================================================ */

#define MB_MAGIC   0x1BADB002
#define MB_FLAGS   0x00000007  /* page-align | meminfo | video */
#define MB_CKSUM   (-(MB_MAGIC + MB_FLAGS))

struct multiboot_header {
    uint32_t magic;
    uint32_t flags;
    uint32_t checksum;
    /* address fields (unused when bit 16 clear) */
    uint32_t header_addr;
    uint32_t load_addr;
    uint32_t load_end_addr;
    uint32_t bss_end_addr;
    uint32_t entry_addr;
    /* video fields (flags bit 2) */
    uint32_t mode_type;   /* 0 = linear fb */
    uint32_t width;
    uint32_t height;
    uint32_t depth;
};

__attribute__((section(".multiboot"), aligned(4), used))
static const struct multiboot_header mb_hdr = {
    .magic       = MB_MAGIC,
    .flags       = MB_FLAGS,
    .checksum    = (uint32_t)MB_CKSUM,
    .header_addr = 0, .load_addr = 0, .load_end_addr = 0,
    .bss_end_addr = 0, .entry_addr = 0,
    .mode_type   = 0,    /* linear framebuffer */
    .width       = 1024,
    .height      = 768,
    .depth       = 32,
};

/* ================================================================
 * Multiboot info — saved by _start (crt0.s) or set to 0
 * ================================================================ */

static uint32_t g_mb_magic = 0;
static uint32_t g_mb_info  = 0;

void rt_set_multiboot_info(uint32_t magic, uint32_t info_ptr) {
    g_mb_magic = magic;
    g_mb_info  = info_ptr;
}

/* Multiboot info struct offsets (Multiboot1 spec) */
#define MBI_FLAGS       0
#define MBI_FB_ADDR     88
#define MBI_FB_PITCH    92
#define MBI_FB_WIDTH    96
#define MBI_FB_HEIGHT   100
#define MBI_FB_BPP      104

static uint32_t mbi_read32(uint32_t offset) {
    if (g_mb_info == 0) return 0;
    return *(volatile uint32_t *)(uintptr_t)(g_mb_info + offset);
}

int64_t rt_multiboot_fb_addr(void)   { return (int64_t)mbi_read32(MBI_FB_ADDR); }
int64_t rt_multiboot_fb_pitch(void)  { return (int64_t)mbi_read32(MBI_FB_PITCH); }
int64_t rt_multiboot_fb_width(void)  { return (int64_t)mbi_read32(MBI_FB_WIDTH); }
int64_t rt_multiboot_fb_height(void) { return (int64_t)mbi_read32(MBI_FB_HEIGHT); }
int64_t rt_multiboot_fb_bpp(void)    { return (int64_t)mbi_read32(MBI_FB_BPP); }
int64_t rt_multiboot_magic(void)     { return (int64_t)g_mb_magic; }

/* Check if multiboot info has framebuffer info (flags bit 12) */
int64_t rt_multiboot_has_fb(void) {
    if (g_mb_info == 0) return 0;
    uint32_t flags = mbi_read32(MBI_FLAGS);
    return (flags & (1 << 12)) ? 1 : 0;
}

/* ================================================================
 * Serial I/O — COM1 at 0x3F8
 * ================================================================ */

static inline void outb(uint16_t port, uint8_t val) {
    __asm__ volatile ("outb %0, %1" : : "a"(val), "Nd"(port));
}
static inline uint8_t inb(uint16_t port) {
    uint8_t ret;
    __asm__ volatile ("inb %1, %0" : "=a"(ret) : "Nd"(port));
    return ret;
}

#define COM1 0x3F8

static int g_serial_inited = 0;

static void serial_ensure_init(void) {
    if (g_serial_inited) return;
    outb(COM1 + 1, 0x00);  /* Disable interrupts */
    outb(COM1 + 3, 0x80);  /* DLAB on */
    outb(COM1 + 0, 0x01);  /* 115200 baud */
    outb(COM1 + 1, 0x00);
    outb(COM1 + 3, 0x03);  /* 8N1, DLAB off */
    outb(COM1 + 2, 0xC7);  /* FIFO */
    outb(COM1 + 4, 0x0B);  /* RTS/DSR */
    g_serial_inited = 1;
}

static void serial_putc(char c) {
    serial_ensure_init();
    while (!(inb(COM1 + 5) & 0x20))
        ;
    outb(COM1, (uint8_t)c);
}

static void serial_puts(const char *s) {
    while (*s) serial_putc(*s++);
}

/* rt_println_value — called by Simple's `print` statement on bare metal */
void rt_println_value(const char *s) {
    serial_ensure_init();
    if (s) serial_puts(s);
    serial_putc('\r');
    serial_putc('\n');
}

/* serial_println — callable from Simple via extern fn */
void serial_println(const char *s) {
    rt_println_value(s);
}

/* ================================================================
 * Framebuffer fill — rt_fb_fill_rect
 * Fill a rectangle at (x,y,w,h) with a 32-bit ARGB color.
 * ================================================================ */

void rt_fb_fill_rect(int64_t fb_addr, int64_t pitch,
                     int64_t x, int64_t y, int64_t w, int64_t h,
                     int64_t color) {
    volatile uint32_t *fb = (volatile uint32_t *)(uintptr_t)fb_addr;
    uint32_t c = (uint32_t)color;
    int64_t stride = pitch / 4; /* pitch in bytes -> stride in pixels */
    for (int64_t row = y; row < y + h; row++) {
        for (int64_t col = x; col < x + w; col++) {
            fb[row * stride + col] = c;
        }
    }
}

/* ================================================================
 * Heap allocator -- 16MB bump allocator, 16-byte aligned
 * ================================================================ */

static char _heap[16 * 1024 * 1024]; /* 16 MB */
static size_t _heap_offset = 0;

void *malloc(size_t size) {
    size = (size + 15) & ~(size_t)15;
    if (_heap_offset + size > sizeof(_heap)) return 0;
    void *ptr = &_heap[_heap_offset];
    _heap_offset += size;
    return ptr;
}

void free(void *ptr) {
    (void)ptr; /* bump allocator -- no reclaim */
}

void *realloc(void *ptr, size_t old_size, size_t new_size) {
    void *new_ptr = malloc(new_size);
    if (ptr && new_ptr) {
        size_t copy = old_size < new_size ? old_size : new_size;
        __builtin_memcpy(new_ptr, ptr, copy);
    }
    return new_ptr;
}

void *calloc(size_t n, size_t size) {
    size_t total = n * size;
    void *ptr = malloc(total);
    if (ptr) __builtin_memset(ptr, 0, total);
    return ptr;
}

/* ================================================================
 * Simple runtime allocator -- rt_alloc
 * ================================================================ */

void *rt_alloc(int64_t size) {
    return malloc((size_t)size);
}

/* ================================================================
 * Memory primitives -- required by compiler-generated code
 * ================================================================ */

void *memcpy(void *dst, const void *src, size_t n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

void *memset(void *s, int c, size_t n) {
    unsigned char *p = (unsigned char *)s;
    for (size_t i = 0; i < n; i++) p[i] = (unsigned char)c;
    return s;
}

void *memmove(void *dst, const void *src, size_t n) {
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    if (d < s) {
        for (size_t i = 0; i < n; i++) d[i] = s[i];
    } else {
        for (size_t i = n; i > 0; i--) d[i - 1] = s[i - 1];
    }
    return dst;
}

int memcmp(const void *s1, const void *s2, size_t n) {
    const unsigned char *a = (const unsigned char *)s1;
    const unsigned char *b = (const unsigned char *)s2;
    for (size_t i = 0; i < n; i++) {
        if (a[i] != b[i]) return (int)a[i] - (int)b[i];
    }
    return 0;
}

size_t strlen(const char *s) {
    size_t len = 0;
    while (s[len]) len++;
    return len;
}

/* ================================================================
 * Framebuffer bulk copy -- rt_framebuffer_copy
 * ================================================================ */

void rt_framebuffer_copy(uint64_t dst_addr, int64_t *src, uint32_t count) {
    volatile uint32_t *dst = (volatile uint32_t *)(uintptr_t)dst_addr;
    for (uint32_t i = 0; i < count; i++) {
        dst[i] = (uint32_t)src[i];
    }
}
