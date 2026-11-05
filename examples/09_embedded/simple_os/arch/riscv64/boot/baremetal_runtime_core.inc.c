#include <stdint.h>
#include <stddef.h>

typedef intptr_t RuntimeValue;

#define UART_BASE 0x10000000UL
#define SIMPLEOS_RV64_FDT_CONSOLE 1
#include "../../common/baremetal_16550_serial.h"
#define SIFIVE_TEST_BASE 0x100000UL
#define VIRTIO_MMIO_BASE 0x10001000UL
#define VIRTIO_MMIO_STRIDE 0x1000UL
#define VIRTIO_MMIO_SLOTS 8U
#define VIRTIO_MAGIC 0x74726976U
#define VIRTIO_DEV_NET 1U
#define VIRTIO_DEV_BLK 2U
#define VIRTQ_DESC_F_NEXT 1U
#define VIRTQ_DESC_F_WRITE 2U
#define VIRTIO_STATUS_ACKNOWLEDGE 1U
#define VIRTIO_STATUS_DRIVER 2U
#define VIRTIO_STATUS_DRIVER_OK 4U
#define VIRTIO_STATUS_FEATURES_OK 8U

#define TAG_MASK    ((uintptr_t)0x7)
#define TAG_INT     ((uintptr_t)0x0)
#define TAG_HEAP    ((uintptr_t)0x1)
#define TAG_FLOAT   ((uintptr_t)0x2)
#define TAG_SPECIAL ((uintptr_t)0x3)
#define NIL_VALUE   ((RuntimeValue)TAG_SPECIAL)
/* Codegen tags (src/compiler_rust/compiler/src/codegen/llvm/instructions.rs
 * `tagged_bool_const`): true = 11, false = 19. Spelled out because this file
 * is #included into a TU that does not see arch/common/baremetal_runtime.h
 * (same reason the literals are spelled out in rt_value_unbox_int below). */
#define TRUE_VALUE  ((RuntimeValue)11)
#define FALSE_VALUE ((RuntimeValue)19)
_Static_assert(TRUE_VALUE == 11, "TRUE_VALUE must match codegen tagged true (11)");
_Static_assert(FALSE_VALUE == 19, "FALSE_VALUE must match codegen tagged false (19)");

#define ENCODE_INT(v) ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3) | TAG_INT))
#define DECODE_INT(v) ((int64_t)(v) >> 3)
#define ENCODE_PTR(p) ((RuntimeValue)((uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v) ((void *)((uintptr_t)(v) & ~TAG_MASK))
#define IS_INT(v)     (((uintptr_t)(v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v)    (((uintptr_t)(v) & TAG_MASK) == TAG_HEAP)

#define HEAP_STRING 1U
#define HEAP_ARRAY  2U
#define HEAP_ENUM   7U
/* Distinct from HEAP_STRING so a string-builder handle can never be read back
 * as a RuntimeString by rt_string_len / rt_string_data — the two structs have
 * different layouts and a shared tag would silently return garbage. */
#define HEAP_STRING_BUILDER 8U
/* Closure objects. Distinct tag so rt_closure_func_ptr can refuse a handle
 * that is not actually a closure instead of reading a foreign field. */
#define HEAP_CLOSURE 9U
/* Declared with the other heap kinds rather than beside the dict
 * implementation further down, because rt_len / rt_index_get / rt_index_set
 * above it must all recognise a dict receiver. */
#define HEAP_DICT 11U

/* Defined with the dict implementation further down this TU. */
uint64_t     simpleos_dict_count(RuntimeValue dict);
RuntimeValue simpleos_dict_lookup(RuntimeValue dict, RuntimeValue key);
int8_t       simpleos_dict_store(RuntimeValue dict, RuntimeValue key, RuntimeValue item);

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

typedef struct {
    HeapHeader hdr;
    uint64_t len;   /* MUST be uint64_t: codegen inlines .len() as an i64 load at offset 8 and places data at offset 16 (see doc/08_tracking/bug/x64_rt_extras_runtime_string_layout_mismatch.md) */
    char data[];
} RuntimeString;
_Static_assert(offsetof(RuntimeString, len) == 8, "RuntimeString.len must sit at offset 8: codegen inlines .len() as an i64 load there");
_Static_assert(offsetof(RuntimeString, data) == 16, "RuntimeString.data must sit at offset 16 to match compiler-emitted string objects");

typedef struct {
    HeapHeader hdr;
    uint64_t len;
    uint64_t cap;
    RuntimeValue *items;
} RuntimeArray;

typedef struct {
    HeapHeader hdr;
    uint32_t enum_id;
    uint32_t discriminant;
    RuntimeValue payload;
} RuntimeEnum;

/* Pure-Simple driver/service receipts and PCM staging outgrow the historical
 * 64 KiB bootstrap heap. Keep a fixed, linker-accounted 1 MiB arena. */
/* The bump arena is the region the LINKER SCRIPT already reserves for it:
 * arch/common/linker_riscv_common.ld carves a 64 MB `.heap` between
 * __heap_start and __heap_end and documents it as "for bump allocator", but
 * nothing ever read those symbols -- the arena was a 1 MiB static array and the
 * 64 MB stayed dead address space. 1 MiB cannot hold the in-guest Simple
 * frontend: the riscv64 build-and-run row exhausted it inside make_core_lexer,
 * rv_alloc returned NULL, and the unchecked store faulted with tval=0. `.heap`
 * is NOLOAD, so using it costs the kernel Image no bytes. g_heap_off stays in
 * .bss (zeroed by crt0); rv_alloc does not require a zeroed arena, and
 * rv_calloc zeroes what it hands out. */
extern unsigned char __heap_start[];
extern unsigned char __heap_end[];
/* The HIGH half of the linker-reserved `.heap`. See the matching comment in
 * baremetal_stubs.c: the two riscv64 runtime TUs each keep a private bump
 * cursor, so they must own disjoint halves of the region. */
#define RV_HEAP_BASE (__heap_start + ((size_t)(__heap_end - __heap_start) / 2U))
#define RV_HEAP_SIZE ((size_t)(__heap_end - __heap_start) / 2U)
static uintptr_t g_heap_off = 0;
static unsigned char g_virtq[8192] __attribute__((aligned(4096)));
static unsigned char g_dma[1024] __attribute__((aligned(512)));
static unsigned char g_riscv_file_buf[8192] __attribute__((aligned(16)));
static unsigned char g_riscv_process_arena[2][8192] __attribute__((aligned(4096)));
static uint64_t g_riscv_process_entry[2];
static uint64_t g_riscv_process_pid[2];
static uint32_t g_riscv_process_count;
uint64_t g_fb_addr = 0;
uint64_t g_fb_w = 0;
static char g_riscv_gui_surface[256];
static volatile uint32_t *g_blk_mmio = 0;
static uint16_t g_last_used_idx = 0;

extern RuntimeValue spl_start(void);
extern char _stack_top[];

static void serial_puts(const char *s);
static int g_rv_heap_exhausted_reported = 0;
static void rv_report_heap_exhausted(void)
{
    if (g_rv_heap_exhausted_reported) return;
    g_rv_heap_exhausted_reported = 1;
    serial_puts("[rv64] FATAL bump heap exhausted (high half) - rv_alloc returned NULL\r\n");
}
#define RV_HEAP_EXHAUSTED_REPORT() rv_report_heap_exhausted()
#define BAREMETAL_ENABLE_ALIGNED_ALLOC 1
/* Kernel-stack guard at the allocation funnel (see boot_entry.c). Defined in
 * boot_entry.c, the one riscv64 boot TU with no duplicate twin, so this hook
 * cannot be shadowed by the OTHER definition the way rt_index_set was. */
void rv64_stack_guard_check(void);
#define RV_ALLOC_GUARD_CHECK() rv64_stack_guard_check()
#include "../../common/baremetal_bump_heap.h"

/* Width-independent helpers shared with riscv32 (rv_memzero, rv_fence, le/rd
 * helpers, virtio-blk driver, FAT32 driver, SMF/ELF loaders, serial_println,
 * rt_qemu_exit_success, rt_native_eq/neq, rt_riscv_nvfs_probe). */
#include "../../common/riscv_common.h"

RuntimeValue rt_qemu_exit_failure(void)
{
    *(volatile uint32_t *)SIFIVE_TEST_BASE = 0x3333U;
    return NIL_VALUE;
}

static RuntimeValue *runtime_array_inline_items(RuntimeArray *a)
{
    return (RuntimeValue *)((unsigned char *)a + sizeof(RuntimeArray));
}

static RuntimeValue *runtime_array_items(RuntimeArray *a)
{
    if (!a) return 0;
    return a->items ? a->items : runtime_array_inline_items(a);
}

static uint64_t simpleos_raw_or_encoded_int(RuntimeValue v)
{
    return IS_INT(v) ? (uint64_t)DECODE_INT(v) : (uint64_t)v;
}

void *malloc(size_t size)
{
    return rv_alloc(size);
}

void free(void *ptr)
{
    (void)ptr;
}

void *calloc(size_t n, size_t size)
{
    size_t total = n * size;
    void *ptr = rv_alloc(total);
    if (ptr) {
        unsigned char *bytes = (unsigned char *)ptr;
        for (size_t i = 0; i < total; i++) bytes[i] = 0;
    }
    return ptr;
}

void *realloc(void *ptr, size_t size)
{
    void *next = rv_alloc(size);
    if (!next || !ptr) return next;
    unsigned char *dst = (unsigned char *)next;
    const unsigned char *src = (const unsigned char *)ptr;
    for (size_t i = 0; i < size; i++) dst[i] = src[i];
    return next;
}

void *memcpy(void *dst, const void *src, size_t n)
{
    unsigned char *d = (unsigned char *)dst;
    const unsigned char *s = (const unsigned char *)src;
    for (size_t i = 0; i < n; i++) d[i] = s[i];
    return dst;
}

int memcmp(const void *a, const void *b, size_t n)
{
    const unsigned char *pa = (const unsigned char *)a;
    const unsigned char *pb = (const unsigned char *)b;
    for (size_t i = 0; i < n; i++) {
        if (pa[i] != pb[i]) return (int)pa[i] - (int)pb[i];
    }
    return 0;
}

RuntimeValue rt_alloc(RuntimeValue sz)
{
    size_t bytes = (size_t)sz;
    void *ptr = calloc(1, bytes);
    return ptr ? (RuntimeValue)(uintptr_t)ptr : 0;
}

/* Port #45 of the freestanding riscv64 runtime surface.
 *
 * Reached only once module-global initializers actually RUN in-guest: a
 * struct-literal module global lowers to `rt_struct_alloc`. Before
 * boot_entry.c called `__simple_call_module_inits`, every `__module_init_*`
 * was garbage-collected out of the link, so this symbol was never referenced
 * and its absence was invisible.
 *
 * Deliberately NOT a port of the hosted implementation
 * (src/runtime/runtime_memory.c:455), which registers each allocation in an
 * rwlock-guarded tracking table read back by `rt_struct_receiver_valid`.
 * Neither that table nor that validator exists in this freestanding runtime
 * (grep of this boot directory: zero hits for both), so replicating the
 * bookkeeping would add a structure nothing reads. The load-bearing contract
 * is the one the hosted version shares with `rt_alloc`: RAW byte count in
 * (not an encoded RuntimeValue), RAW zeroed pointer out (not encoded), NULL
 * on a non-positive size or on allocation failure. */
uint8_t *rt_struct_alloc(int64_t size)
{
    if (size <= 0) return (uint8_t *)0;
    return (uint8_t *)calloc(1, (size_t)size);
}

RuntimeValue f64_to_bits(RuntimeValue val)
{
    uint64_t fbits = (uint64_t)val >> 3;
    return ENCODE_INT((int64_t)fbits);
}

RuntimeValue spl_f64_to_bits(RuntimeValue val)
{
    return f64_to_bits(val);
}

__attribute__((weak)) RuntimeValue rt_dma_alloc(RuntimeValue size, RuntimeValue align)
{
    size_t bytes = (size_t)simpleos_raw_or_encoded_int(size);
    size_t alignment = (size_t)simpleos_raw_or_encoded_int(align);
    void *ptr = rv_alloc_aligned(bytes, alignment);
    return ptr ? (RuntimeValue)(uintptr_t)ptr : 0;
}

static void serial_puts(const char *s)
{
    uart_puts(s);
}

static void serial_putchar(char c)
{
    uart_putc(c);
}

void log_raw_println(RuntimeValue msg)
{
    if (IS_HEAP(msg)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(msg);
        if (s && s->hdr.type == HEAP_STRING && s->len < 4096U) {
            for (uint32_t i = 0; i < s->len; i++) uart_putc(s->data[i]);
        }
    }
    uart_putc('\r');
    uart_putc('\n');
}

static void serial_put_dec(int64_t value)
{
    char buf[32];
    uint32_t pos = 0;
    uint64_t raw = (uint64_t)(value < 0 ? -value : value);
    if (value == 0) {
        uart_putc('0');
        return;
    }
    while (raw > 0 && pos < sizeof(buf)) {
        buf[pos++] = (char)('0' + (raw % 10U));
        raw /= 10U;
    }
    if (value < 0 && pos < sizeof(buf)) buf[pos++] = '-';
    while (pos > 0) uart_putc(buf[--pos]);
}

static void serial_put_hex(uint32_t value)
{
    static const char hex[] = "0123456789abcdef";
    for (int shift = 28; shift >= 0; shift -= 4) {
        uart_putc(hex[(value >> shift) & 0xFU]);
    }
}

RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len_val)
{
    uintptr_t len = (uintptr_t)len_val;
    if (len > 4096U) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + len + 1U);
    if (!s) return NIL_VALUE;
    s->hdr.type = HEAP_STRING;
    s->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1U);
    s->len = (uint64_t)len;
    const char *src = (const char *)(uintptr_t)data;
    for (uintptr_t i = 0; i < len; i++) {
        s->data[i] = src ? src[i] : 0;
    }
    s->data[len] = 0;
    return ENCODE_PTR(s);
}

static RuntimeValue rt_string_from_cstr(const char *cstr)
{
    uintptr_t len = 0;
    while (cstr && cstr[len] != 0) len++;
    return rt_string_new((RuntimeValue)(uintptr_t)cstr, (RuntimeValue)len);
}

RuntimeValue rt_string_concat(RuntimeValue a, RuntimeValue b)
{
    RuntimeString *sa = IS_HEAP(a) ? (RuntimeString *)DECODE_PTR(a) : 0;
    RuntimeString *sb = IS_HEAP(b) ? (RuntimeString *)DECODE_PTR(b) : 0;
    /* Type-check both sides. Without this a builder or array handle is read
     * through the RuntimeString layout, taking `len` from a foreign field and
     * copying out of a foreign region — the same class of silent corruption as
     * the rt_string_builder_push signature defect above. */
    if (sa && sa->hdr.type != HEAP_STRING) sa = 0;
    if (sb && sb->hdr.type != HEAP_STRING) sb = 0;
    uintptr_t la = sa ? sa->len : 0;
    uintptr_t lb = sb ? sb->len : 0;
    RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + la + lb + 1U);
    if (!out) return NIL_VALUE;
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(RuntimeString) + la + lb + 1U);
    out->len = (uint64_t)(la + lb);
    for (uintptr_t i = 0; i < la; i++) out->data[i] = sa->data[i];
    for (uintptr_t i = 0; i < lb; i++) out->data[la + i] = sb->data[i];
    out->data[la + lb] = 0;
    return ENCODE_PTR(out);
}

RuntimeValue rt_value_to_string(RuntimeValue value)
{
    if (IS_HEAP(value)) {
        HeapHeader *hdr = (HeapHeader *)DECODE_PTR(value);
        if (hdr && hdr->type == HEAP_STRING) return value;
        if (hdr && hdr->type == HEAP_ARRAY) return rt_string_from_cstr("<array>");
        return rt_string_from_cstr("<object>");
    }
    if (value == NIL_VALUE) return rt_string_from_cstr("nil");

    int64_t n = IS_INT(value) ? DECODE_INT(value) : (int64_t)value;
    char buf[32];
    uintptr_t pos = 0;
    uint64_t raw = (uint64_t)(n < 0 ? -n : n);
    if (n == 0) buf[pos++] = '0';
    while (raw > 0 && pos < sizeof(buf)) {
        buf[pos++] = (char)('0' + (raw % 10U));
        raw /= 10U;
    }
    if (n < 0) buf[pos++] = '-';
    RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + pos + 1U);
    if (!out) return NIL_VALUE;
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(RuntimeString) + pos + 1U);
    out->len = (uint32_t)pos;
    for (uintptr_t i = 0; i < pos; i++) out->data[i] = buf[pos - 1U - i];
    out->data[pos] = 0;
    return ENCODE_PTR(out);
}

RuntimeValue rt_to_string(RuntimeValue value)
{
    return rt_value_to_string(value);
}

static RuntimeValue rt_array_push_handle(RuntimeValue arr, RuntimeValue value)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY) return NIL_VALUE;
    if (a->len >= a->cap) {
        uint64_t new_cap = a->cap ? a->cap * 2U : 16U;
        /* Keep growth bounded by the 64 KiB freestanding bump heap. The
         * array header remains stable while its item storage moves. */
        if (new_cap > 4096U) return NIL_VALUE;
        RuntimeValue *grown = (RuntimeValue *)rv_alloc((size_t)new_cap * sizeof(RuntimeValue));
        if (!grown) return NIL_VALUE;
        RuntimeValue *old_items = runtime_array_items(a);
        for (uint64_t i = 0; i < a->len; i++) grown[i] = old_items[i];
        for (uint64_t i = a->len; i < new_cap; i++) grown[i] = NIL_VALUE;
        a->items = grown;
        a->cap = new_cap;
    }
    runtime_array_items(a)[a->len++] = value;
    return arr;
}

RuntimeValue rt_array_new(RuntimeValue cap_val)
{
    uint64_t cap = simpleos_raw_or_encoded_int(cap_val);
    if (cap == 0) cap = 16;
    if (cap < 16) cap = 16;
    RuntimeArray *a = (RuntimeArray *)rv_alloc(sizeof(RuntimeArray) + cap * sizeof(RuntimeValue));
    if (!a) return NIL_VALUE;
    a->hdr.type = HEAP_ARRAY;
    a->hdr.size = (uint32_t)(sizeof(RuntimeArray) + cap * sizeof(RuntimeValue));
    a->len = 0;
    a->cap = cap;
    a->items = runtime_array_inline_items(a);
    for (uint64_t i = 0; i < cap; i++) a->items[i] = NIL_VALUE;
    return ENCODE_PTR(a);
}

RuntimeValue rt_array_new_with_cap(int64_t cap)
{
    return rt_array_new((RuntimeValue)cap);
}

int8_t rt_array_push(RuntimeValue arr, RuntimeValue value)
{
    return rt_array_push_handle(arr, value) != NIL_VALUE;
}

RuntimeValue rt_array_pop(RuntimeValue arr)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    if (!a || a->hdr.type != HEAP_ARRAY || a->len == 0) return NIL_VALUE;
    RuntimeValue *items = runtime_array_items(a);
    a->len--;
    RuntimeValue value = items[a->len];
    items[a->len] = NIL_VALUE;
    return value;
}

RuntimeValue rt_array_get(RuntimeValue arr, RuntimeValue idx)
{
    if (!IS_HEAP(arr)) return NIL_VALUE;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    int64_t i = (int64_t)idx;
    if (!a || a->hdr.type != HEAP_ARRAY || i < 0 || (uint64_t)i >= a->len) return NIL_VALUE;
    return runtime_array_items(a)[i];
}

int8_t rt_array_set(RuntimeValue arr, RuntimeValue idx, RuntimeValue value)
{
    if (!IS_HEAP(arr)) return 0;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    int64_t i = (int64_t)idx;
    if (!a || a->hdr.type != HEAP_ARRAY || i < 0 || (uint64_t)i >= a->len) return 0;
    runtime_array_items(a)[i] = value;
    return 1;
}

RuntimeValue rt_array_len(RuntimeValue arr)
{
    if (!IS_HEAP(arr)) return 0;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(arr);
    return (!a || a->hdr.type != HEAP_ARRAY) ? 0 : (RuntimeValue)a->len;
}

RuntimeValue rt_arm_array_len_u32(RuntimeValue arr)
{
    RuntimeArray *tagged = IS_HEAP(arr) ? (RuntimeArray *)DECODE_PTR(arr) : (RuntimeArray *)0;
    if (tagged && tagged->hdr.type == HEAP_ARRAY && tagged->len <= tagged->cap)
        return (RuntimeValue)tagged->len;
    RuntimeArray *raw = (RuntimeArray *)(uintptr_t)(uint64_t)arr;
    if (raw && raw->hdr.type == HEAP_ARRAY && raw->len <= raw->cap)
        return (RuntimeValue)raw->len;
    return 0;
}

RuntimeValue rt_tuple_new(RuntimeValue len_rv)
{
    uint64_t len = simpleos_raw_or_encoded_int(len_rv);
    RuntimeArray *a = (RuntimeArray *)rv_alloc(sizeof(RuntimeArray) + len * sizeof(RuntimeValue));
    if (!a) return NIL_VALUE;
    a->hdr.type = HEAP_ARRAY;
    a->hdr.size = (uint32_t)(sizeof(RuntimeArray) + len * sizeof(RuntimeValue));
    a->len = len;
    a->cap = len;
    a->items = runtime_array_inline_items(a);
    for (uint64_t i = 0; i < len; i++) a->items[i] = NIL_VALUE;
    return ENCODE_PTR(a);
}

RuntimeValue rt_tuple_get(RuntimeValue tuple, RuntimeValue index)
{
    return rt_array_get(tuple, index);
}

RuntimeValue rt_tuple_set(RuntimeValue tuple, RuntimeValue index, RuntimeValue value)
{
    return rt_array_set(tuple, index, value);
}

uint8_t rt_mmio_read_u8(uint64_t addr)
{
    return *(volatile uint8_t *)(uintptr_t)addr;
}

RuntimeValue rt_volatile_read_u8(RuntimeValue addr)
{
    return (RuntimeValue)(uint64_t)*(volatile uint8_t *)(uintptr_t)(uint64_t)addr;
}

uint16_t rt_mmio_read_u16(uint64_t addr)
{
    return *(volatile uint16_t *)(uintptr_t)addr;
}

uint64_t rt_mmio_read_u32(uint64_t addr)
{
    return (uint64_t)*(volatile uint32_t *)(uintptr_t)addr;
}

uint64_t rt_mmio_read_u64(uint64_t addr)
{
    return *(volatile uint64_t *)(uintptr_t)addr;
}

void rt_mmio_write_u8(uint64_t addr, uint8_t value)
{
    *(volatile uint8_t *)(uintptr_t)addr = value;
}

void rt_mmio_write_u16(uint64_t addr, uint16_t value)
{
    *(volatile uint16_t *)(uintptr_t)addr = value;
}

void rt_mmio_write_u32(uint64_t addr, uint32_t value)
{
    *(volatile uint32_t *)(uintptr_t)addr = value;
}

void rt_mmio_write_u64(uint64_t addr, uint64_t value)
{
    *(volatile uint64_t *)(uintptr_t)addr = value;
}

RuntimeValue rt_len(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    HeapHeader *hdr = (HeapHeader *)DECODE_PTR(value);
    if (!hdr) return 0;
    if (hdr->type == HEAP_STRING) return (RuntimeValue)((RuntimeString *)hdr)->len;
    if (hdr->type == HEAP_ARRAY) return (RuntimeValue)((RuntimeArray *)hdr)->len;
    /* Dicts answer their pair count rather than a flat 0. Same defect family as
     * the rt_index_get/rt_index_set dict gaps below: a kind this function does
     * not recognise gets a plausible-looking answer instead of an honest one,
     * and `d.len() == 0` on a populated dict reads as "empty" everywhere. */
    if (hdr->type == HEAP_DICT) return (RuntimeValue)simpleos_dict_count(value);
    return 0;
}

/* Forward declaration: rt_string_char_at is defined further down this TU, but
 * rt_index_get below must route text subscripts to it. */
RuntimeValue rt_string_char_at(RuntimeValue str, RuntimeValue idx);

RuntimeValue rt_index_get(RuntimeValue value, RuntimeValue index)
{
    if (!IS_HEAP(value)) return NIL_VALUE;
    HeapHeader *hdr = (HeapHeader *)DECODE_PTR(value);
    if (!hdr) return NIL_VALUE;
    /* DICT FIRST, and deliberately BEFORE the IS_INT(index) guard: a dict key
     * is an arbitrary RuntimeValue (this lane's real case is
     * `Dict<SymbolId, HirFunction>`, whose key is a heap struct handle, not an
     * int). The old `if (!IS_INT(index)) return NIL_VALUE;` opening line
     * rejected every such key before the receiver was even examined. */
    if (hdr->type == HEAP_DICT) return simpleos_dict_lookup(value, index);
    if (!IS_INT(index)) return NIL_VALUE;
    if (hdr->type == HEAP_ARRAY) return rt_array_get(value, (RuntimeValue)DECODE_INT(index));
    /* A TEXT subscript (`s[i]`) lowers to rt_index_get exactly like an array
     * subscript does, but this function used to recognise only HEAP_ARRAY and
     * fall through to NIL for every string — so `s[i]` was nil for EVERY index,
     * and any scanner built on it (redact's _is_key_char/_run_* loops, the
     * caret component row) silently produced an empty result rather than
     * failing. rt_string_char_at already existed and was simply never reached
     * from here. It takes a RAW index (`int64_t i = (int64_t)idx`), hence the
     * DECODE_INT, matching the rt_array_get call above. Byte-indexed, which is
     * the same basis as this runtime's rt_len for strings.
     * Measured 2026-08-31: in-guest probe `acc = acc + s[i]` over 5 chars
     * returned "" before this change and the source text after it. */
    if (hdr->type == HEAP_STRING) return rt_string_char_at(value, (RuntimeValue)DECODE_INT(index));
    return NIL_VALUE;
}

RuntimeValue rt_index_set(RuntimeValue value, RuntimeValue index, RuntimeValue item)
{
    /* Receiver kind is decided FIRST. This function used to open with
     * `if (!IS_INT(index)) return 0;` and then unconditionally call
     * rt_array_set — it never looked at what it was writing INTO. For a DICT
     * receiver with a non-int key that opening line returned 0 immediately and
     * THE WRITE WAS SILENTLY DROPPED; for an int key it would have scribbled
     * through the array path into a dict's memory.
     *
     * This is the exact mirror of the rt_index_get HEAP_ARRAY-only defect fixed
     * directly above, one notch further along, and it is what stalled the
     * riscv64 in-guest interpreter row: HIR lowering populates
     * `HirModule.functions : Dict<SymbolId, HirFunction>` with `d[sym] = fn`,
     * which lowers to rt_index_set with a heap-struct key. Every one of those
     * writes was discarded, so the dict stayed EMPTY, `.values()` yielded
     * nothing, the `f.name == "main"` loop body never executed once, and
     * InterpreterBackendImpl.interpret_hir_module reported
     * "module has no main function" — with no trap and no error, because
     * dropping a write is silent by construction.
     *
     * (The `hir.functions.len() > 0` guard upstream still passed, which is why
     * this looked like an iteration/compare defect rather than an empty dict:
     * `.len()` did not route here at all.) */
    if (IS_HEAP(value)) {
        HeapHeader *hdr = (HeapHeader *)DECODE_PTR(value);
        if (hdr && hdr->type == HEAP_DICT) {
            return (RuntimeValue)simpleos_dict_store(value, index, item);
        }
    }
    if (!IS_INT(index)) return 0;
    return rt_array_set(value, (RuntimeValue)DECODE_INT(index), item);
}

RuntimeValue rt_enum_new(RuntimeValue enum_id_rv, RuntimeValue disc_rv, RuntimeValue payload)
{
    RuntimeEnum *e = (RuntimeEnum *)rv_alloc(sizeof(RuntimeEnum));
    if (!e) return NIL_VALUE;
    e->hdr.type = HEAP_ENUM;
    e->hdr.size = (uint32_t)sizeof(RuntimeEnum);
    e->enum_id = (uint32_t)(int32_t)enum_id_rv;
    e->discriminant = (uint32_t)(int32_t)disc_rv;
    e->payload = payload;
    return ENCODE_PTR(e);
}

RuntimeValue rt_enum_payload(RuntimeValue value)
{
    if (!IS_HEAP(value)) return value;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    return (!e || e->hdr.type != HEAP_ENUM) ? value : e->payload;
}

RuntimeValue rt_enum_check_discriminant(RuntimeValue value, RuntimeValue expected)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return 0;
    return e->discriminant == (uint32_t)(int32_t)expected ? 1 : 0;
}

RuntimeValue rt_string_char_at(RuntimeValue str, RuntimeValue idx)
{
    if (!IS_HEAP(str)) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    int64_t i = (int64_t)idx;
    if (!s || s->hdr.type != HEAP_STRING || i < 0 || (uint32_t)i >= s->len) return NIL_VALUE;
    return rt_string_new((RuntimeValue)(uintptr_t)(s->data + i), 1);
}

RuntimeValue rt_string_chars(RuntimeValue str)
{
    RuntimeString *s = IS_HEAP(str) ? (RuntimeString *)DECODE_PTR(str) : (RuntimeString *)0;
    RuntimeValue arr = rt_array_new(ENCODE_INT(s && s->hdr.type == HEAP_STRING ? s->len : 0));
    if (!s || s->hdr.type != HEAP_STRING) return arr;
    for (uint32_t i = 0; i < s->len;) {
        uint8_t lead = (uint8_t)s->data[i];
        uint32_t width = 1;
        if (lead >= 0xC2 && lead <= 0xDF && i + 2 <= s->len) width = 2;
        else if (lead >= 0xE0 && lead <= 0xEF && i + 3 <= s->len) width = 3;
        else if (lead >= 0xF0 && lead <= 0xF4 && i + 4 <= s->len) width = 4;
        arr = rt_array_push_handle(arr, rt_string_new((RuntimeValue)(uintptr_t)&s->data[i], (RuntimeValue)width));
        i += width;
    }
    return arr;
}

RuntimeValue rt_string_eq(RuntimeValue a, RuntimeValue b)
{
    if (!IS_HEAP(a) || !IS_HEAP(b)) return 0;
    RuntimeString *sa = (RuntimeString *)DECODE_PTR(a);
    RuntimeString *sb = (RuntimeString *)DECODE_PTR(b);
    if (!sa || !sb || sa->hdr.type != HEAP_STRING || sb->hdr.type != HEAP_STRING) return 0;
    if (sa->len != sb->len) return 0;
    for (uint32_t i = 0; i < sa->len; i++) {
        if (sa->data[i] != sb->data[i]) return 0;
    }
    return 1;
}

RuntimeValue rt_string_starts_with(RuntimeValue str, RuntimeValue prefix)
{
    if (!IS_HEAP(str) || !IS_HEAP(prefix)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    RuntimeString *p = (RuntimeString *)DECODE_PTR(prefix);
    if (!s || !p || s->hdr.type != HEAP_STRING || p->hdr.type != HEAP_STRING) return 0;
    if (p->len > s->len) return 0;
    for (uint32_t i = 0; i < p->len; i++) {
        if (s->data[i] != p->data[i]) return 0;
    }
    return 1;
}

RuntimeValue rt_string_replace_all(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val)
{
    if (!IS_HEAP(str) || !IS_HEAP(old_val) || !IS_HEAP(new_val)) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    RuntimeString *o = (RuntimeString *)DECODE_PTR(old_val);
    RuntimeString *n = (RuntimeString *)DECODE_PTR(new_val);
    if (!s || !o || !n || s->hdr.type != HEAP_STRING || o->hdr.type != HEAP_STRING || n->hdr.type != HEAP_STRING) {
        return NIL_VALUE;
    }
    if (o->len == 0 || o->len > s->len) return str;

    uint32_t count = 0;
    for (uint32_t i = 0; o->len <= s->len - i;) {
        uint32_t j = 0;
        while (j < o->len && s->data[i + j] == o->data[j]) j++;
        if (j == o->len) {
            count++;
            i += o->len;
        } else {
            i++;
        }
    }
    if (count == 0) return str;

    uint64_t out_len_wide =
        (uint64_t)s->len - (uint64_t)count * o->len + (uint64_t)count * n->len;
    if (out_len_wide > (uint64_t)UINT32_MAX - sizeof(RuntimeString) - 1U) return str;
    uint32_t out_len = (uint32_t)out_len_wide;
    RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + out_len + 1U);
    if (!out) return str;
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(RuntimeString) + out_len + 1U);
    out->len = out_len;

    uint32_t in = 0;
    uint32_t out_i = 0;
    while (in < s->len) {
        uint32_t j = 0;
        while (j < o->len && j < s->len - in && s->data[in + j] == o->data[j]) j++;
        if (j == o->len) {
            for (uint32_t k = 0; k < n->len; k++) out->data[out_i++] = n->data[k];
            in += o->len;
        } else {
            out->data[out_i++] = s->data[in++];
        }
    }
    out->data[out_len] = 0;
    return ENCODE_PTR(out);
}

RuntimeValue rt_string_replace(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val)
{
    return rt_string_replace_all(str, old_val, new_val);
}

RuntimeValue rt_string_to_upper(RuntimeValue str)
{
    if (!IS_HEAP(str)) return str;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s || s->hdr.type != HEAP_STRING) return str;
    RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + s->len + 1U);
    if (!out) return str;
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1U);
    out->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) {
        char c = s->data[i];
        out->data[i] = (c >= 'a' && c <= 'z') ? (char)(c - ('a' - 'A')) : c;
    }
    out->data[s->len] = 0;
    return ENCODE_PTR(out);
}

RuntimeValue rt_string_to_lower(RuntimeValue str)
{
    if (!IS_HEAP(str)) return str;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s || s->hdr.type != HEAP_STRING) return str;
    RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + s->len + 1U);
    if (!out) return str;
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(RuntimeString) + s->len + 1U);
    out->len = s->len;
    for (uint32_t i = 0; i < s->len; i++) {
        char c = s->data[i];
        out->data[i] = (c >= 'A' && c <= 'Z') ? (char)(c + ('a' - 'A')) : c;
    }
    out->data[s->len] = 0;
    return ENCODE_PTR(out);
}

static int rt_is_ascii_whitespace(char c)
{
    return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

RuntimeValue rt_string_trim(RuntimeValue str)
{
    if (!IS_HEAP(str)) return str;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s || s->hdr.type != HEAP_STRING || s->len == 0) return str;

    uint32_t start = 0;
    while (start < s->len && rt_is_ascii_whitespace(s->data[start])) start++;

    uint32_t end = s->len;
    while (end > start && rt_is_ascii_whitespace(s->data[end - 1])) end--;

    uint32_t out_len = end - start;
    RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + out_len + 1U);
    if (!out) return str;
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(RuntimeString) + out_len + 1U);
    out->len = out_len;
    for (uint32_t i = 0; i < out_len; i++) out->data[i] = s->data[start + i];
    out->data[out_len] = 0;
    return ENCODE_PTR(out);
}

RuntimeValue str_byte_at_impl(RuntimeValue str, RuntimeValue idx) __asm__("str.byte_at");
RuntimeValue str_byte_at_impl(RuntimeValue str, RuntimeValue idx)
{
    if (!IS_HEAP(str)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    int64_t i = (int64_t)idx;
    if (!s || s->hdr.type != HEAP_STRING || i < 0 || (uint32_t)i >= s->len) return 0;
    return (RuntimeValue)(uint8_t)s->data[i];
}

static uint64_t harden_mix64(uint64_t value)
{
    value ^= value >> 30;
    value *= 0xbf58476d1ce4e5b9ULL;
    value ^= value >> 27;
    value *= 0x94d049bb133111ebULL;
    value ^= value >> 31;
    return value;
}

RuntimeValue rt_riscv_harden_canary_value(void)
{
    uint64_t cycle = 0;
    uint64_t time = 0;
    uint64_t instret = 0;
    __asm__ volatile("rdcycle %0" : "=r"(cycle));
    __asm__ volatile("rdtime %0" : "=r"(time));
    __asm__ volatile("rdinstret %0" : "=r"(instret));
    uint64_t mixed = harden_mix64(
        cycle ^ (time << 17) ^ (instret << 33) ^ (uintptr_t)&rt_riscv_harden_canary_value
    );
    mixed &= 0x7fffffffffffffffULL;
    return (RuntimeValue)(mixed == 0 ? 1 : mixed);
}


/* ---------------------------------------------------------------------------
 * Runtime surface needed by REAL product modules, not just hello world.
 *
 * Added 2026-08-31 while bringing the toolchain components (caret, the linter,
 * the MCP dispatcher, the test-runner parser) up in-guest on riscv64. The
 * hello-world lane only ever needed serial output, so this baremetal runtime
 * stopped at ~113 rt_* entry points; the moment a real product module is linked
 * in, ld.lld reports the rest as undefined and the freestanding link dies.
 *
 * These are PORTS of the existing hosted ABI in src/runtime/runtime_native.c
 * into the baremetal runtime — exactly what the rest of this file already is —
 * NOT new rt_* symbols. Every name here is already declared in
 * src/runtime/runtime.h and already implemented for hosted targets; the
 * semantics are copied from there and the encoding is adapted to this file's
 * tagging (raw int64 in/out for lengths, indices and booleans, RuntimeValue for
 * strings and arrays), which is the convention rt_array_len and
 * rt_string_starts_with above already follow.
 *
 * Bounded on purpose: allocation goes through rv_alloc, which draws on the
 * 64 KiB freestanding bump heap, so the array helpers inherit the same growth
 * ceiling rt_array_push_handle enforces.
 * ------------------------------------------------------------------------ */

RuntimeValue rt_string_ends_with(RuntimeValue str, RuntimeValue suffix)
{
    if (!IS_HEAP(str) || !IS_HEAP(suffix)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    RuntimeString *p = (RuntimeString *)DECODE_PTR(suffix);
    if (!s || !p || s->hdr.type != HEAP_STRING || p->hdr.type != HEAP_STRING) return 0;
    if (p->len > s->len) return 0;
    uint32_t off = s->len - p->len;
    for (uint32_t i = 0; i < p->len; i++) {
        if (s->data[off + i] != p->data[i]) return 0;
    }
    return 1;
}

/* UTF-8 codepoint at a CODEPOINT index (not a byte index) — matching the
 * hosted rt_string_char_code_at, and matching rt_string_chars above, which
 * already walks the same UTF-8 widths. Indexing bytes here would disagree with
 * `for ch in s` and silently return half a character on non-ASCII input. */
RuntimeValue rt_string_char_code_at(RuntimeValue str, RuntimeValue index)
{
    if (!IS_HEAP(str)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    if (!s || s->hdr.type != HEAP_STRING) return 0;
    int64_t want = (int64_t)index;
    if (want < 0) return 0;

    int64_t seen = 0;
    for (uint32_t i = 0; i < s->len;) {
        uint8_t lead = (uint8_t)s->data[i];
        uint32_t width = 1;
        uint32_t cp = lead;
        if (lead >= 0xC2 && lead <= 0xDF && i + 2 <= s->len) {
            width = 2; cp = (uint32_t)(lead & 0x1F);
        } else if (lead >= 0xE0 && lead <= 0xEF && i + 3 <= s->len) {
            width = 3; cp = (uint32_t)(lead & 0x0F);
        } else if (lead >= 0xF0 && lead <= 0xF4 && i + 4 <= s->len) {
            width = 4; cp = (uint32_t)(lead & 0x07);
        }
        for (uint32_t k = 1; k < width; k++) {
            cp = (cp << 6) | (uint32_t)((uint8_t)s->data[i + k] & 0x3F);
        }
        if (seen == want) return (RuntimeValue)(int64_t)cp;
        seen++;
        i += width;
    }
    return 0;
}

/* strcmp semantics, sign-normalised to -1/0/1. There is no libc here, so the
 * comparison walks the bytes directly. */
RuntimeValue rt_text_cmp_any(RuntimeValue left, RuntimeValue right)
{
    RuntimeString *a = IS_HEAP(left) ? (RuntimeString *)DECODE_PTR(left) : (RuntimeString *)0;
    RuntimeString *b = IS_HEAP(right) ? (RuntimeString *)DECODE_PTR(right) : (RuntimeString *)0;
    if (a && a->hdr.type != HEAP_STRING) a = 0;
    if (b && b->hdr.type != HEAP_STRING) b = 0;
    uint32_t la = a ? a->len : 0;
    uint32_t lb = b ? b->len : 0;
    uint32_t n = la < lb ? la : lb;
    for (uint32_t i = 0; i < n; i++) {
        uint8_t ca = (uint8_t)a->data[i];
        uint8_t cb = (uint8_t)b->data[i];
        if (ca != cb) return (RuntimeValue)(int64_t)(ca < cb ? -1 : 1);
    }
    if (la == lb) return 0;
    return (RuntimeValue)(int64_t)(la < lb ? -1 : 1);
}

/* Slice over a string (byte range) or an array (element range), honouring a
 * step, with Python-style negative-index normalisation — same contract as the
 * hosted rt_slice(value, start, end, step). */
RuntimeValue rt_slice(RuntimeValue value, RuntimeValue start_v, RuntimeValue end_v, RuntimeValue step_v)
{
    int64_t step = (int64_t)step_v;
    if (step == 0) step = 1;
    if (!IS_HEAP(value)) return value;

    HeapHeader *h = (HeapHeader *)DECODE_PTR(value);
    if (!h) return value;

    int64_t n;
    if (h->type == HEAP_STRING) {
        n = (int64_t)((RuntimeString *)h)->len;
    } else if (h->type == HEAP_ARRAY) {
        n = (int64_t)((RuntimeArray *)h)->len;
    } else {
        return value;
    }

    int64_t start = (int64_t)start_v;
    int64_t end = (int64_t)end_v;
    if (start < 0) start += n;
    if (end < 0) end += n;
    if (start < 0) start = 0;
    if (end > n) end = n;

    if (h->type == HEAP_STRING) {
        RuntimeString *s = (RuntimeString *)h;

        /* The contiguous forward slice — which is what `.substring(a, b)`
         * lowers to and is overwhelmingly the common case — is served by ONE
         * allocation. The obvious char-by-char concat loop is not merely slow
         * here: rv_alloc draws on a 64 KiB bump heap that never frees, so two
         * allocations per character exhausted it inside a single
         * json_find scan over a 47-byte string and the guest hung with no trap
         * message (measured 2026-08-31, the caret row stalled right after
         * printing its built message). Bulk-copying is the fix, not a
         * micro-optimisation. */
        if (step == 1) {
            int64_t take = end - start;
            if (take <= 0) return rt_string_new((RuntimeValue)(uintptr_t)"", 0);
            return rt_string_new((RuntimeValue)(uintptr_t)(s->data + start), (RuntimeValue)take);
        }

        /* Strided/reverse slices are rare; build the bytes into one buffer
         * first so this path still costs a single allocation. */
        int64_t count = 0;
        if (step > 0) { for (int64_t i = start; i < end; i += step) count++; }
        else { for (int64_t i = start; i > end; i += step) { if (i >= 0 && i < n) count++; } }
        if (count <= 0) return rt_string_new((RuntimeValue)(uintptr_t)"", 0);
        char *buf = (char *)rv_alloc((size_t)count + 1U);
        if (!buf) return NIL_VALUE;
        int64_t w = 0;
        if (step > 0) { for (int64_t i = start; i < end; i += step) buf[w++] = s->data[i]; }
        else { for (int64_t i = start; i > end; i += step) { if (i >= 0 && i < n) buf[w++] = s->data[i]; } }
        buf[w] = 0;
        return rt_string_new((RuntimeValue)(uintptr_t)buf, (RuntimeValue)w);
    }

    RuntimeArray *a = (RuntimeArray *)h;
    RuntimeValue out = rt_array_new(ENCODE_INT(16));
    RuntimeValue *items = runtime_array_items(a);
    if (step > 0) {
        for (int64_t i = start; i < end; i += step) out = rt_array_push_handle(out, items[i]);
    } else {
        for (int64_t i = start; i > end; i += step) {
            if (i < 0 || i >= n) continue;
            out = rt_array_push_handle(out, items[i]);
        }
    }
    return out;
}

RuntimeValue rt_string_join(RuntimeValue array_value, RuntimeValue separator)
{
    RuntimeValue out = rt_string_new((RuntimeValue)(uintptr_t)"", 0);
    if (!IS_HEAP(array_value)) return out;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(array_value);
    if (!a || a->hdr.type != HEAP_ARRAY) return out;
    RuntimeValue *items = runtime_array_items(a);
    for (uint64_t i = 0; i < a->len; i++) {
        if (i != 0) out = rt_string_concat(out, separator);
        out = rt_string_concat(out, items[i]);
    }
    return out;
}

/* `for x in <text>` must bind one 1-char text per CODEPOINT, not per byte.
 * The hosted rt_for_iterable routes text through rt_string_chars for exactly
 * that reason (a byte walk ran 6 times over a 5-character "café," and bound
 * garbage); rt_string_chars above already does the UTF-8 walk, so this is the
 * same fix in the same shape. Dicts do not exist in this runtime, so the
 * hosted dict-entries branch has no counterpart here. */
RuntimeValue rt_for_iterable(RuntimeValue collection)
{
    if (IS_HEAP(collection)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(collection);
        if (h && h->type == HEAP_STRING) return rt_string_chars(collection);
    }
    return collection;
}

/* rt_value_int MUST tag. The comment that used to sit here claimed "this
 * runtime has no separate boxed-integer representation" and returned `value`
 * verbatim. That premise was false, and the identity body was the root cause of
 * `for x in <array>` binding a good element on iteration 1 and nil on every
 * later iteration in freestanding riscv64
 * (doc/08_tracking/bug/freestanding_riscv64_for_in_array_yields_nil_after_first_element_2026-08-31.md).
 *
 * The link this file participates in also contains baremetal_stubs.c, whose
 * rt_index_get opens with `if (!IS_INT(index)) return NIL_VALUE;` — i.e. it
 * REQUIRES a TAG_INT-encoded index, using the very TAG_MASK/TAG_INT/DECODE_INT
 * macros this file defines at lines 22-32 and then declined to use here. MIR
 * lowering of a counted `for` emits BoxInt on the induction variable, cranelift
 * lowers BoxInt to `call rt_value_int`, and the identity body handed
 * rt_index_get a RAW index:
 *
 *   raw 0 -> 0 & 7 == 0 -> IS_INT true  -> DECODE_INT(0) == 0 -> element 0, CORRECT
 *   raw 1..6            -> IS_INT false -> NIL_VALUE
 *
 * which is exactly the observed "correct once, nil thereafter" signature.
 *
 * Tagging here matches the hosted runtime contract, under which rt_index_get
 * takes a TAGGED index and rt_array_get takes a RAW one (runtime_native.c
 * calls `rt_array_get(arr, i)` with a bare loop counter). rt_index_get already
 * bridges the two by DECODE_INT-ing before it delegates. The unbox side needs
 * no change: rt_value_unbox_int below routes through
 * simpleos_raw_or_encoded_int, which accepts either form. */
RuntimeValue rt_value_int(RuntimeValue value)
{
    return ENCODE_INT(value);
}

/* The TAGGED-BOOL arm is load-bearing and was missing until 2026-09-01.
 *
 * simpleos_raw_or_encoded_int is `IS_INT(v) ? DECODE_INT(v) : v` -- it decodes
 * TAG_INT and passes EVERYTHING ELSE through verbatim. A Simple bool is not
 * TAG_INT: codegen encodes `true` as 11 and `false` as 19, both TAG_SPECIAL.
 * So an unboxed `false` came back as 19, and every consumer that tests the
 * result for non-zero read it as TRUE -- 19 is non-zero, and so is 11, so BOTH
 * bools answered true.
 *
 * That is the whole of the riscv64 row-2 hang. `parse_statement` destructures
 * `try_parse_bare_ident_string_call()`'s `return (false, 0)` early exit through
 * rt_tuple_get -> rt_value_unbox_int -> `bnez`; the flag read `true`, so
 * parse_expr() was never called, no token was consumed, and parse_block()'s
 * `while true:` spun allocating until the bump arena was gone.
 *
 * The contract this restores is not invented here. It is what the canonical
 * hosted runtime does (src/compiler_rust/runtime/src/value/sffi/value_ops.rs:80-87,
 * SPECIAL_TRUE -> 1, SPECIAL_FALSE -> 0), what the codegen comments already
 * describe as the decision table ("tagged true/false -> 1/0",
 * codegen/instr/mod.rs:1598), and what the SIBLING freestanding implementation
 * in arch/common/boot/freestanding_value_registry_impl.h:112-119 already
 * implements. This definition was simply an incomplete port of the same name.
 *
 * The literals 11 and 19 are spelled out rather than using the
 * TAGGED_BOOL_TRUE/FALSE macros in arch/common/baremetal_runtime.h: this file
 * is #included into a TU that does not see that header (it was tried, and the
 * build failed with "use of undeclared identifier 'TAGGED_BOOL_TRUE'"), and the
 * sibling implementation in freestanding_value_registry_impl.h:112 spells them
 * out the same way.
 *
 * Do NOT push the bool arm down into simpleos_raw_or_encoded_int: its other
 * callers pass sizes, capacities and lengths, where a raw 11 or 19 is a
 * legitimate count and must NOT be rewritten to 1 or 0. */
RuntimeValue rt_value_unbox_int(RuntimeValue value)
{
    if (value == 11) return 1;  /* tagged true  */
    if (value == 19) return 0;  /* tagged false */
    return (RuntimeValue)(int64_t)simpleos_raw_or_encoded_int(value);
}

/* Second tranche of hosted-ABI ports, added for the test-runner component row
 * (std.nogc_sync_mut.test_runner.test_executor_parsing.parse_test_output).
 * Same status as the tranche above: ports of names already declared in
 * src/runtime/runtime.h and already implemented for hosted targets, NOT new
 * rt_* symbols. Signatures are taken from that header verbatim. */

/* Byte (not codepoint) access, matching the hosted rt_string_byte_at. This is
 * deliberately the BYTE form even though rt_string_char_code_at above is the
 * codepoint form — they are different entry points with different contracts,
 * and parse_test_output's scanners want bytes. */
RuntimeValue rt_string_byte_at(RuntimeValue str, RuntimeValue index)
{
    if (!IS_HEAP(str)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    int64_t i = (int64_t)index;
    if (!s || s->hdr.type != HEAP_STRING || i < 0 || (uint32_t)i >= s->len) return 0;
    return (RuntimeValue)(int64_t)(uint8_t)s->data[i];
}

/* Substring containment for text; element containment for an array. The hosted
 * rt_contains is polymorphic over both, so this is too. */
/* Forward declaration: rt_contains's dict arm delegates here, but the dict
 * section (and the RuntimeDict type) is defined later in this TU. Signature
 * matches src/runtime/runtime.h:746 and the definition below. */
int8_t rt_dict_contains(int64_t dict, int64_t key);

RuntimeValue rt_contains(RuntimeValue collection, RuntimeValue value)
{
    if (!IS_HEAP(collection)) return 0;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(collection);
    if (!h) return 0;

    if (h->type == HEAP_STRING) {
        RuntimeString *s = (RuntimeString *)h;
        if (!IS_HEAP(value)) return 0;
        RuntimeString *needle = (RuntimeString *)DECODE_PTR(value);
        if (!needle || needle->hdr.type != HEAP_STRING) return 0;
        if (needle->len == 0) return 1;
        if (needle->len > s->len) return 0;
        for (uint32_t i = 0; i + needle->len <= s->len; i++) {
            uint32_t j = 0;
            while (j < needle->len && s->data[i + j] == needle->data[j]) j++;
            if (j == needle->len) return 1;
        }
        return 0;
    }

    if (h->type == HEAP_ARRAY) {
        RuntimeArray *a = (RuntimeArray *)h;
        RuntimeValue *items = runtime_array_items(a);
        for (uint64_t i = 0; i < a->len; i++) {
            if (items[i] == value) return 1;
            if (rt_string_eq(items[i], value)) return 1;
        }
        return 0;
    }

    /* DICT arm -- hosted parity, and the SAME defect family as the tag-11 gap
     * in the inline `.len()` path and the dict arm added to rt_len above.
     * `.has` / `.contains` / `.contains_key` on a Dict lower to rt_contains,
     * NOT to rt_dict_contains (codegen/llvm/emitter.rs:324 and
     * codegen/instr/closures_structs.rs:117 map all of them to "rt_contains"),
     * and the hosted rt_contains answers dicts via rt_core_dict_has
     * (runtime_native.c). This port handled only HEAP_STRING and HEAP_ARRAY
     * and fell through to `return 0`, so EVERY `dict.has(k)` answered FALSE
     * in-guest on a dict that provably held the key.
     *
     * MEASURED 2026-09-01, in-guest under real OpenSBI v1.4 fw_payload, nonce
     * 8d03ec284ec3be32, from the build-and-run row's own run half:
     *
     *     FAIL run error: function 'add' not found
     *       [PROBE hit=N hasidx=Y dictlen=2 vals=2]
     *
     * i.e. the interpreter's name index held BOTH functions (dictlen=2, built
     * from the same 2 module functions, vals=2), and `.has("add")` still said
     * no. resolve_function_by_name then fail-closed on has_fn_index and never
     * ran the linear scan that would have found it.
     *
     * Key rule is delegated to rt_dict_contains (defined at the dict section
     * below) so the two cannot drift. It is CALLED, not spelled inline: the
     * RuntimeDict type is not declared until line ~2101, well after this
     * function, so an inline `RuntimeDict *d = ...` here is an undeclared-type
     * error that fails this whole TU and cascades into the link. (Measured --
     * that is exactly what the first attempt at this fix did.) A file-scope
     * forward declaration is placed immediately above rt_contains; its
     * signature matches src/runtime/runtime.h:746 and the definition below. */
    if (h->type == HEAP_DICT) {
        return rt_dict_contains((int64_t)collection, (int64_t)value) ? 1 : 0;
    }
    return 0;
}

/* Split on a delimiter, returning an array of strings. An empty delimiter
 * returns the whole input as a single element rather than exploding into
 * characters — that is the hosted behaviour and callers rely on it. Each piece
 * is ONE allocation (rt_string_new over the byte range), never a per-character
 * concat: the freestanding bump heap never frees, so the concat form is what
 * exhausted it in the rt_slice incident recorded above. */
RuntimeValue rt_string_split(RuntimeValue value, RuntimeValue delimiter)
{
    RuntimeValue out = rt_array_new(ENCODE_INT(16));
    if (!IS_HEAP(value)) return out;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(value);
    if (!s || s->hdr.type != HEAP_STRING) return out;

    RuntimeString *d = IS_HEAP(delimiter) ? (RuntimeString *)DECODE_PTR(delimiter) : (RuntimeString *)0;
    if (d && d->hdr.type != HEAP_STRING) d = 0;
    if (!d || d->len == 0) {
        return rt_array_push_handle(out, value);
    }

    uint32_t start = 0;
    for (uint32_t i = 0; i + d->len <= s->len;) {
        uint32_t j = 0;
        while (j < d->len && s->data[i + j] == d->data[j]) j++;
        if (j == d->len) {
            out = rt_array_push_handle(
                out, rt_string_new((RuntimeValue)(uintptr_t)(s->data + start), (RuntimeValue)(i - start)));
            i += d->len;
            start = i;
        } else {
            i++;
        }
    }
    out = rt_array_push_handle(
        out, rt_string_new((RuntimeValue)(uintptr_t)(s->data + start), (RuntimeValue)(s->len - start)));
    return out;
}

/* Decimal parse with an optional sign, skipping leading/trailing ASCII space.
 * Non-numeric input yields 0, matching the hosted rt_string_to_int. */
RuntimeValue rt_string_to_int(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(value);
    if (!s || s->hdr.type != HEAP_STRING) return 0;

    uint32_t i = 0;
    while (i < s->len && (s->data[i] == ' ' || s->data[i] == '\t' ||
                          s->data[i] == '\n' || s->data[i] == '\r')) i++;
    int64_t sign = 1;
    if (i < s->len && (s->data[i] == '-' || s->data[i] == '+')) {
        if (s->data[i] == '-') sign = -1;
        i++;
    }
    int64_t acc = 0;
    int saw_digit = 0;
    while (i < s->len && s->data[i] >= '0' && s->data[i] <= '9') {
        acc = acc * 10 + (int64_t)(s->data[i] - '0');
        saw_digit = 1;
        i++;
    }
    if (!saw_digit) return 0;
    return (RuntimeValue)(sign * acc);
}

/* Third tranche of hosted-ABI ports, added for the dev-tool component row
 * (compiler.tools.lint._LintMain.os_freestanding_lints). Same status as the
 * two tranches above: ports, not new rt_* symbols.
 *
 * The enum accessors sit alongside the pre-existing rt_enum_check_discriminant
 * (line 526) and read the same RuntimeEnum layout; the lint rule needs the raw
 * discriminant and enum id because it returns Option<OsFreestandingWarning>
 * and the caller matches on it. */

RuntimeValue rt_enum_discriminant(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return 0;
    return (RuntimeValue)(int64_t)e->discriminant;
}

RuntimeValue rt_enum_id(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return 0;
    return (RuntimeValue)(int64_t)e->enum_id;
}

/* Index of the first occurrence, or -1. Polymorphic over text (substring
 * search, byte offsets) and array (element search), mirroring rt_contains
 * above and the hosted rt_find. -1 for "absent" is load-bearing: callers
 * branch on `< 0`, so returning 0 would read as "found at the start". */
RuntimeValue rt_find(RuntimeValue collection, RuntimeValue value)
{
    if (!IS_HEAP(collection)) return (RuntimeValue)(int64_t)-1;
    HeapHeader *h = (HeapHeader *)DECODE_PTR(collection);
    if (!h) return (RuntimeValue)(int64_t)-1;

    if (h->type == HEAP_STRING) {
        RuntimeString *s = (RuntimeString *)h;
        if (!IS_HEAP(value)) return (RuntimeValue)(int64_t)-1;
        RuntimeString *needle = (RuntimeString *)DECODE_PTR(value);
        if (!needle || needle->hdr.type != HEAP_STRING) return (RuntimeValue)(int64_t)-1;
        if (needle->len == 0) return 0;
        if (needle->len > s->len) return (RuntimeValue)(int64_t)-1;
        for (uint32_t i = 0; i + needle->len <= s->len; i++) {
            uint32_t j = 0;
            while (j < needle->len && s->data[i + j] == needle->data[j]) j++;
            if (j == needle->len) return (RuntimeValue)(int64_t)i;
        }
        return (RuntimeValue)(int64_t)-1;
    }

    if (h->type == HEAP_ARRAY) {
        RuntimeArray *a = (RuntimeArray *)h;
        RuntimeValue *items = runtime_array_items(a);
        for (uint64_t i = 0; i < a->len; i++) {
            if (items[i] == value) return (RuntimeValue)(int64_t)i;
            if (rt_string_eq(items[i], value)) return (RuntimeValue)(int64_t)i;
        }
    }
    return (RuntimeValue)(int64_t)-1;
}

/* Fourth tranche of hosted-ABI ports: the STRING BUILDER.
 *
 * Found by probe, not by reading codegen: `acc = acc + x` inside a loop does
 * not lower to repeated rt_string_concat — codegen rewrites it into a builder
 * (rt_string_builder_new / _push / _finish, with rt_string_data + rt_string_len
 * to read the appended piece). The freestanding riscv64 runtime had none of
 * these, so a product module that accumulates a string in a loop fails to link
 * here. Ports of names already declared in src/runtime/runtime.h, not new rt_*
 * symbols.
 *
 * Because the bump heap never frees, growth DOUBLES rather than reallocating
 * per push — per-append reallocation is exactly the pattern that exhausted the
 * heap in the rt_slice incident recorded above.
 */

typedef struct {
    HeapHeader hdr;
    uint32_t len;
    uint32_t cap;
    char *data;
} RuntimeStringBuilder;

RuntimeValue rt_string_len(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(value);
    if (!s || s->hdr.type != HEAP_STRING) return 0;
    return (RuntimeValue)(int64_t)s->len;
}

RuntimeValue rt_string_data(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(value);
    if (!s || s->hdr.type != HEAP_STRING) return 0;
    return (RuntimeValue)(uintptr_t)s->data;
}

RuntimeValue rt_string_builder_new(void)
{
    RuntimeStringBuilder *b = (RuntimeStringBuilder *)rv_alloc(sizeof(RuntimeStringBuilder));
    if (!b) return NIL_VALUE;
    /* Tagged as a DISTINCT heap type so a builder handle can never be read as a
     * RuntimeString by rt_string_len / rt_string_data above. */
    b->hdr.type = HEAP_STRING_BUILDER;
    b->hdr.size = (uint32_t)sizeof(RuntimeStringBuilder);
    b->len = 0;
    b->cap = 64;
    b->data = (char *)rv_alloc(b->cap);
    if (!b->data) return NIL_VALUE;
    b->data[0] = 0;
    return ENCODE_PTR(b);
}

RuntimeValue rt_string_builder_len(RuntimeValue builder)
{
    if (!IS_HEAP(builder)) return 0;
    RuntimeStringBuilder *b = (RuntimeStringBuilder *)DECODE_PTR(builder);
    if (!b || b->hdr.type != HEAP_STRING_BUILDER) return 0;
    return (RuntimeValue)(int64_t)b->len;
}

/* Signature MUST match the hosted contract: runtime.h:405 declares
 *   int64_t rt_string_builder_push(int64_t handle, int64_t string);
 * — TWO arguments, and the second is a tagged string HANDLE, not a raw char*
 * with a separate length. This port previously took (builder, data, len) and
 * cast argument 2 straight to `const char *`, so codegen's 2-argument call
 * made it copy bytes out of the string object's HEADER and take a garbage
 * length from an uninitialised register. That is why an in-guest
 * `acc = acc + "x"` loop produced NUL bytes instead of text (probe step 9a)
 * and then hung (step 9b), and it is the defect behind the caret row's empty
 * `extract_json_string` result and the test-runner row's wrong counts. */
RuntimeValue rt_string_builder_push(RuntimeValue builder, RuntimeValue string)
{
    if (!IS_HEAP(builder)) return builder;
    RuntimeStringBuilder *b = (RuntimeStringBuilder *)DECODE_PTR(builder);
    if (!b || b->hdr.type != HEAP_STRING_BUILDER) return builder;

    RuntimeString *s = IS_HEAP(string) ? (RuntimeString *)DECODE_PTR(string) : (RuntimeString *)0;
    if (!s || s->hdr.type != HEAP_STRING) return builder;
    uint32_t add = (uint32_t)s->len;
    const char *src = s->data;
    if (add == 0) return builder;

    if (b->len + add + 1U > b->cap) {
        uint32_t want = b->cap ? b->cap : 64U;
        while (want < b->len + add + 1U) want *= 2U;
        char *grown = (char *)rv_alloc(want);
        if (!grown) return builder;
        for (uint32_t i = 0; i < b->len; i++) grown[i] = b->data[i];
        b->data = grown;
        b->cap = want;
    }
    for (uint32_t i = 0; i < add; i++) b->data[b->len + i] = src[i];
    b->len += add;
    b->data[b->len] = 0;
    return builder;
}

RuntimeValue rt_string_builder_finish(RuntimeValue builder)
{
    if (!IS_HEAP(builder)) return rt_string_new((RuntimeValue)(uintptr_t)"", 0);
    RuntimeStringBuilder *b = (RuntimeStringBuilder *)DECODE_PTR(builder);
    if (!b || b->hdr.type != HEAP_STRING_BUILDER) {
        return rt_string_new((RuntimeValue)(uintptr_t)"", 0);
    }
    return rt_string_new((RuntimeValue)(uintptr_t)b->data, (RuntimeValue)(int64_t)b->len);
}

RuntimeValue rt_string_builder_free(RuntimeValue builder)
{
    /* The bump heap never frees; this exists so the symbol resolves. */
    (void)builder;
    return NIL_VALUE;
}

/* ---------------------------------------------------------------------------
 * Closures.
 *
 * PORT, not a new symbol: rt_closure_new / rt_closure_set_capture /
 * rt_closure_get_capture / rt_closure_func_ptr are all declared in
 * src/runtime/runtime.h (lines 664-667) and defined for the hosted target in
 * src/runtime/runtime_native.c (rt_closure_new at :8042). What follows is the
 * same contract re-expressed against this file's bump heap and tagged-value
 * encoding, so a freestanding image can carry a closure-valued struct field.
 *
 * The MCP dispatcher needs exactly this: DispatchEntry.handler is a closure,
 * so without these four symbols the component kernel does not LINK. Stubbing
 * them would produce a dispatcher that silently handles nothing, which is why
 * they are implemented rather than stubbed.
 *
 * Differences from the hosted definition, and why each is correct here:
 *   * calloc -> rv_alloc plus an explicit fill. rv_alloc does NOT zero, and
 *     zeroing would be wrong anyway: NIL_VALUE is TAG_SPECIAL (0x3), not 0, so
 *     the captures are filled with NIL_VALUE explicitly rather than relying on
 *     allocator behaviour.
 *   * rt_core_register_closure is dropped. That call exists hosted so the GC
 *     can trace closures; this runtime has no collector and never frees, so
 *     every closure is already immortal — the property registration buys.
 *   * func_ptr is stored raw (not tagged). Codegen passes and expects a raw
 *     code address on both lanes; tagging it here would corrupt the
 *     indirect call.
 * ------------------------------------------------------------------------- */

typedef struct {
    HeapHeader   hdr;
    uint64_t     func_ptr;
    uint64_t     capture_count;
    RuntimeValue captures[];
} RuntimeClosure;

/* Reject a handle that is not a closure rather than reading a foreign field. */
static RuntimeClosure *as_closure(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeClosure *c = (RuntimeClosure *)DECODE_PTR(value);
    if (!c || c->hdr.type != HEAP_CLOSURE) return 0;
    return c;
}

/* PARAMETER WIDTHS ARE NOT FREE CHOICES — they are the codegen ABI, declared in
 * src/compiler_rust/compiler/src/codegen/runtime_sffi.rs:678-681:
 *   rt_closure_new         (I64, I32)      -> I64
 *   rt_closure_set_capture (I64, I32, I64) -> I8
 *   rt_closure_get_capture (I64, I32)      -> I64
 *   rt_closure_func_ptr    (I64)           -> I64
 * and matched by the Rust runtime (value/objects.rs:177,198,213,227), whose
 * index/count parameters are `u32`. Declaring these as 64-bit RuntimeValue —
 * as this port first did — leaves the upper half of the register undefined, so
 * the count/index read as garbage, the capture lookup falls out of range, and
 * the indirect call goes through a NULL func_ptr. That is a trap, and it is
 * exactly what the mcp row did in-guest. */
RuntimeValue rt_closure_new(RuntimeValue func_ptr, uint32_t capture_count)
{
    int64_t count = (int64_t)capture_count;
    if (!func_ptr || count < 0) return NIL_VALUE;
    /* Bounded like every other allocation in this file: the arena is 1 MiB. */
    if (count > 4096) return NIL_VALUE;
    RuntimeClosure *c = (RuntimeClosure *)rv_alloc(
        sizeof(RuntimeClosure) + (size_t)count * sizeof(RuntimeValue));
    if (!c) return NIL_VALUE;
    c->hdr.type = HEAP_CLOSURE;
    c->hdr.size = (uint32_t)(sizeof(RuntimeClosure) + (size_t)count * sizeof(RuntimeValue));
    c->func_ptr = (uint64_t)(uintptr_t)func_ptr;
    c->capture_count = (uint64_t)count;
    for (int64_t i = 0; i < count; i++) c->captures[i] = NIL_VALUE;
    return ENCODE_PTR(c);
}

/* Returns I8 per the codegen spec, not a tagged RuntimeValue. */
int8_t rt_closure_set_capture(RuntimeValue closure, uint32_t index, RuntimeValue value)
{
    RuntimeClosure *c = as_closure(closure);
    if (!c || (uint64_t)index >= c->capture_count) return 0;
    c->captures[index] = value;
    return 1;
}

RuntimeValue rt_closure_get_capture(RuntimeValue closure, uint32_t index)
{
    RuntimeClosure *c = as_closure(closure);
    if (!c || (uint64_t)index >= c->capture_count) return NIL_VALUE;
    return c->captures[index];
}

RuntimeValue rt_closure_func_ptr(RuntimeValue closure)
{
    RuntimeClosure *c = as_closure(closure);
    return c ? (RuntimeValue)(uintptr_t)c->func_ptr : 0;
}

/* ---------------------------------------------------------------------------
 * Four more PORTS of hosted names, needed by the MCP dispatch closure:
 *   rt_string_bytes  (runtime.h:402, runtime_native.c:2754)
 *   rt_array_concat  (runtime.h:505, runtime_native.c:7218)
 *   rt_native_cmp    (runtime.h:677, runtime_native.c:3798)
 *   rt_bytes_to_text (runtime.c:3633 / runtime_native.c:6946 — defined hosted
 *                     but NOT declared in runtime.h; still a port of an
 *                     existing hosted name, not a new symbol)
 *
 * The hosted array carries FLAG_BYTES / FLAG_U64_PACKED and switches element
 * width on them. This runtime's RuntimeArray has no flags — every element is a
 * RuntimeValue slot — so the ports are the same CONTRACT expressed in the one
 * representation this file has, rather than a transcription of code whose
 * branches cannot exist here.
 * ------------------------------------------------------------------------- */

RuntimeValue rt_string_bytes(RuntimeValue str)
{
    RuntimeString *s = IS_HEAP(str) ? (RuntimeString *)DECODE_PTR(str) : (RuntimeString *)0;
    if (s && s->hdr.type != HEAP_STRING) s = 0;
    RuntimeValue arr = rt_array_new(ENCODE_INT(s ? (int64_t)s->len : 0));
    if (!s) return arr;
    /* ENCODE_INT, not a raw byte. The hosted BUGFIX note at
     * runtime_native.c:2757 says a `[u8]` element read masks with & 0xFF
     * WITHOUT untagging, so a tagged slot would hand back the tag's low byte —
     * true hosted, FALSE on this lane, and copying it here was the defect.
     *
     * Measured in-guest 2026-09-01 with RAW storage: `"MCP_RTT_PAYLOAD".bytes()`
     * read back element 0 = 77 and element 14 = 68 correctly, but element 2
     * (byte 80 = 'P') came back as 10 — i.e. this lane's `[u8]` read DOES
     * untag, via the `IS_INT(v) ? DECODE_INT(v) : v` rule that
     * simpleos_raw_or_encoded_int spells out. TAG_INT is 0, so every raw byte
     * that happens to be a multiple of 8 is indistinguishable from an encoded
     * int and is silently divided by 8. In `MCP_RTT_PAYLOAD` exactly the two
     * 'P' bytes (80) are multiples of 8, and both became '\n' (80>>3 = 10):
     * `_bytes_text` rebuilt "MC\n_RTT_\nAYLOAD" — right length, wrong bytes —
     * which is the whole of the mcp row's "lost the payload" failure.
     *
     * Storing tagged also matches what the rest of this arch tree already
     * does: freestanding_runtime.c's rt_text_to_bytes pushes rt_int(byte), and
     * rt_bytes_from_raw documents its slots as "tagged int (byte << 3)".
     * rt_bytes_to_text below already accepts either form, so nothing that
     * consumes these arrays needs to change. */
    for (uint64_t i = 0; i < s->len; i++) {
        arr = rt_array_push_handle(arr, ENCODE_INT((int64_t)(uint8_t)s->data[i]));
    }
    return arr;
}

RuntimeValue rt_bytes_to_text(RuntimeValue bytes_value)
{
    RuntimeArray *a = IS_HEAP(bytes_value) ? (RuntimeArray *)DECODE_PTR(bytes_value) : (RuntimeArray *)0;
    if (a && a->hdr.type != HEAP_ARRAY) a = 0;
    if (!a || a->len == 0) {
        return rt_string_new((RuntimeValue)(uintptr_t)"", 0);
    }
    /* Same 4096 bound every other allocating string entry in this file uses. */
    if (a->len > 4096U) return rt_string_new((RuntimeValue)(uintptr_t)"", 0);
    RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + (size_t)a->len + 1U);
    if (!out) return NIL_VALUE;
    out->hdr.type = HEAP_STRING;
    out->hdr.size = (uint32_t)(sizeof(RuntimeString) + (size_t)a->len + 1U);
    out->len = a->len;
    RuntimeValue *items = runtime_array_items(a);
    /* Tolerate both slot forms: rt_string_bytes stores raw bytes, but an array
     * built in Simple as plain ints arrives tag-encoded. */
    for (uint64_t i = 0; i < a->len; i++) {
        out->data[i] = (char)(uint8_t)(simpleos_raw_or_encoded_int(items[i]) & 0xFFU);
    }
    out->data[a->len] = 0;
    return ENCODE_PTR(out);
}

RuntimeValue rt_array_concat(RuntimeValue left, RuntimeValue right)
{
    RuntimeArray *a = IS_HEAP(left) ? (RuntimeArray *)DECODE_PTR(left) : (RuntimeArray *)0;
    RuntimeArray *b = IS_HEAP(right) ? (RuntimeArray *)DECODE_PTR(right) : (RuntimeArray *)0;
    if (a && a->hdr.type != HEAP_ARRAY) a = 0;
    if (b && b->hdr.type != HEAP_ARRAY) b = 0;
    uint64_t la = a ? a->len : 0;
    uint64_t lb = b ? b->len : 0;
    RuntimeValue out = rt_array_new(ENCODE_INT((int64_t)(la + lb)));
    if (out == NIL_VALUE) return NIL_VALUE;
    if (a) {
        RuntimeValue *ia = runtime_array_items(a);
        for (uint64_t i = 0; i < la; i++) out = rt_array_push_handle(out, ia[i]);
    }
    if (b) {
        RuntimeValue *ib = runtime_array_items(b);
        for (uint64_t i = 0; i < lb; i++) out = rt_array_push_handle(out, ib[i]);
    }
    return out;
}

RuntimeValue rt_native_cmp(RuntimeValue left, RuntimeValue right)
{
    RuntimeString *sa = IS_HEAP(left) ? (RuntimeString *)DECODE_PTR(left) : (RuntimeString *)0;
    RuntimeString *sb = IS_HEAP(right) ? (RuntimeString *)DECODE_PTR(right) : (RuntimeString *)0;
    if (sa && sa->hdr.type != HEAP_STRING) sa = 0;
    if (sb && sb->hdr.type != HEAP_STRING) sb = 0;
    /* Text on either side routes to the text comparator, exactly as hosted. */
    if (sa || sb) return rt_text_cmp_any(left, right);
    /* The hosted float branch has no counterpart here: this runtime never boxes
     * f64 (TAG_FLOAT values are raw bit patterns, see f64_to_bits), so an
     * ordered float compare would be a guess. Integers only. */
    int64_t a = (int64_t)simpleos_raw_or_encoded_int(left);
    int64_t b = (int64_t)simpleos_raw_or_encoded_int(right);
    if (a < b) return (RuntimeValue)(int64_t)-1;
    if (a > b) return (RuntimeValue)(int64_t)1;
    return 0;
}

/* ===========================================================================
 * FOURTH TRANCHE — hosted-ABI ports for the in-guest INTERPRETER row.
 *
 * Same status as the three tranches above: these are PORTS of symbols that
 * already exist in the hosted runtime (src/runtime/runtime_native.c,
 * src/runtime/runtime.c) and in the x86_64 baremetal siblings
 * (arch/x86_64/boot/{baremetal_stubs,rt_extras,auto_stubs,
 * runtime_service_owners}.c). Not one new rt_* symbol is invented here.
 *
 * WHY THEY LIVE IN THIS FILE rather than a new translation unit: every one of
 * them needs the bump heap (rv_alloc), the tag macros, and the RuntimeString /
 * RuntimeArray layouts, all of which are `static` or file-local here. A
 * separate TU would need a second heap, and two heaps in one image is the
 * defect, not the fix.
 *
 * THE ABI IS TAKEN FROM CODEGEN, NOT FROM THE SIBLINGS. The authority is
 * src/compiler_rust/compiler/src/codegen/runtime_sffi.rs's RuntimeFuncSpec
 * table, which is what cranelift actually emits calls against. Where a sibling
 * disagrees with that table the table wins, and the disagreements are real:
 *
 *   - rt_dict_new   : table (I64)->(I64); x86_64 baremetal declares `(void)`.
 *   - rt_env_get    : table (I64,I64)->(I64) i.e. RAW ptr+len, matching
 *                     runtime_native.c; x86_64 baremetal takes one tagged
 *                     RuntimeValue.
 *   - rt_value_float / rt_value_as_float : the table says (F64)->(I64) and
 *                     (I64)->(F64). On riscv64 an F64 travels in fa0, an I64
 *                     in a0 — they are DIFFERENT REGISTER FILES. x86_64's
 *                     rt_extras.c declares both sides as RuntimeValue, which
 *                     happens to be survivable nowhere and is simply drift.
 *                     Getting this wrong here reads an untouched fa0.
 *
 * That is the same failure class as the rt_value_int identity body documented
 * at line 951: a signature that merely links is not a signature that works.
 * =========================================================================== */

/* --- float boxing ---------------------------------------------------------
 * f64_to_bits (line 182) established this file's legacy TAG_FLOAT form as
 * `(bits << 3) | TAG_FLOAT`, which DISCARDS the top 3 bits of the double —
 * the sign and two exponent bits. That is lossy enough to turn a negative
 * number positive, so rt_value_float must not use it. Floats are boxed in a
 * heap cell instead, which is exact. f64_to_bits itself is left untouched --
 * it is reached only by spl_f64_to_bits and predates this pair -- and
 * rt_value_as_float below still decodes the legacy shifted form, so values
 * produced by either scheme read back correctly. */
#define HEAP_FLOAT 10U

typedef struct {
    HeapHeader hdr;
    double value;
} RuntimeFloat;

RuntimeValue rt_value_float(double f)
{
    RuntimeFloat *cell = (RuntimeFloat *)rv_alloc(sizeof(RuntimeFloat));
    if (!cell) return NIL_VALUE;
    cell->hdr.type = HEAP_FLOAT;
    cell->hdr.size = (uint32_t)sizeof(RuntimeFloat);
    cell->value = f;
    return ENCODE_PTR(cell);
}

double rt_value_as_float(RuntimeValue value)
{
    if (IS_HEAP(value)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(value);
        if (h && h->type == HEAP_FLOAT) return ((RuntimeFloat *)h)->value;
        return 0.0;
    }
    /* Legacy shifted TAG_FLOAT, and plain integers, both round-trip. */
    if (((uintptr_t)value & TAG_MASK) == TAG_FLOAT) {
        uint64_t bits = (uint64_t)value >> 3;
        double out;
        __builtin_memcpy(&out, &bits, sizeof(out));
        return out;
    }
    return (double)(int64_t)simpleos_raw_or_encoded_int(value);
}

RuntimeValue rt_value_as_int(RuntimeValue value)
{
    if (IS_HEAP(value)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(value);
        if (h && h->type == HEAP_FLOAT) return (RuntimeValue)(int64_t)((RuntimeFloat *)h)->value;
        return 0;
    }
    return (RuntimeValue)(int64_t)simpleos_raw_or_encoded_int(value);
}

/* --- diagnostics and traps ------------------------------------------------ */

static void simpleos_serial_put_i64(int64_t v)
{
    serial_put_dec(v);
}

static void simpleos_serial_put_string_value(RuntimeValue v)
{
    if (!IS_HEAP(v)) { serial_put_dec((int64_t)simpleos_raw_or_encoded_int(v)); return; }
    HeapHeader *h = (HeapHeader *)DECODE_PTR(v);
    if (!h) { serial_puts("<nil>"); return; }
    if (h->type == HEAP_STRING) {
        RuntimeString *s = (RuntimeString *)h;
        for (uint64_t i = 0; i < s->len; i++) serial_putchar(s->data[i]);
        return;
    }
    if (h->type == HEAP_FLOAT) {
        /* Integral part plus three fractional digits: enough to be readable
         * without dragging a full dtoa into a freestanding image. */
        double d = ((RuntimeFloat *)h)->value;
        if (d < 0) { serial_putchar('-'); d = -d; }
        int64_t whole = (int64_t)d;
        serial_put_dec(whole);
        serial_putchar('.');
        double frac = d - (double)whole;
        for (int i = 0; i < 3; i++) {
            frac *= 10.0;
            int digit = (int)frac;
            serial_putchar((char)('0' + digit));
            frac -= (double)digit;
        }
        return;
    }
    RuntimeValue as_text = rt_value_to_string(v);
    if (as_text != v && IS_HEAP(as_text)) { simpleos_serial_put_string_value(as_text); return; }
    serial_puts("<value>");
}

void rt_print_value(RuntimeValue value)
{
    simpleos_serial_put_string_value(value);
}

void rt_println_value(RuntimeValue value)
{
    simpleos_serial_put_string_value(value);
    serial_putchar('\r');
    serial_putchar('\n');
}

void rt_eprint_value(RuntimeValue value)
{
    /* One UART, so stderr and stdout share it; the tag is what distinguishes
     * them in a transcript. */
    serial_puts("[stderr] ");
    simpleos_serial_put_string_value(value);
    serial_putchar('\r');
    serial_putchar('\n');
}

RuntimeValue rt_raw_i64_to_string(RuntimeValue raw)
{
    /* RAW (untagged) int in, string out — the "raw" in the name is the whole
     * contract, so it must NOT go through simpleos_raw_or_encoded_int. */
    char buf[24];
    int64_t v = (int64_t)raw;
    int neg = v < 0;
    uint64_t mag = neg ? (uint64_t)(-(v + 1)) + 1U : (uint64_t)v;
    int i = (int)sizeof(buf);
    buf[--i] = 0;
    if (mag == 0) buf[--i] = '0';
    while (mag > 0 && i > 0) { buf[--i] = (char)('0' + (mag % 10U)); mag /= 10U; }
    if (neg && i > 0) buf[--i] = '-';
    return rt_string_from_cstr(&buf[i]);
}

void rt_panic(RuntimeValue msg_ptr, uint64_t msg_len)
{
    /* RAW ptr + len per the codegen table, matching runtime_native.c. */
    serial_puts("\r\n[PANIC] ");
    const char *p = (const char *)(uintptr_t)msg_ptr;
    if (p) {
        for (uint64_t i = 0; i < msg_len && i < 512U; i++) serial_putchar(p[i]);
    }
    serial_puts("\r\n");
    rt_qemu_exit_failure();
    for (;;) { __asm__ volatile("wfi"); }
}

RuntimeValue rt_function_not_found(RuntimeValue name_ptr, uint64_t name_len)
{
    serial_puts("[WARN] unresolved fn: ");
    const char *p = (const char *)(uintptr_t)name_ptr;
    if (p) {
        for (uint64_t i = 0; i < name_len && i < 128U; i++) serial_putchar(p[i]);
    }
    serial_puts("\r\n");
    return NIL_VALUE;
}

/* rt_unwrap_or_trap MUST TRAP. This is the symbol behind the 2026-08-18
 * NULL-GOT SIGSEGV: codegen emitted the call, nothing defined it, the link
 * tolerated the undefined symbol, and the NULL GOT slot became a jump to
 * address 0. A body that quietly returns NIL_VALUE would be strictly worse
 * than that crash, because it would convert a hard failure into a silently
 * wrong value that propagates. Unwrapping a nil is a program defect, so it
 * halts the guest loudly and non-zero. */
RuntimeValue rt_unwrap_or_trap(RuntimeValue value)
{
    if (value == NIL_VALUE) {
        serial_puts("\r\n[TRAP] rt_unwrap_or_trap: unwrapped a nil optional\r\n");
        rt_qemu_exit_failure();
        for (;;) { __asm__ volatile("wfi"); }
    }
    /* AND IT MUST ALSO ACTUALLY UNWRAP. Until 2026-09-01 this function's ONLY
     * check was the `== NIL_VALUE` one above, so a boxed `Some(x)` was returned
     * VERBATIM -- the caller got the 24-byte RuntimeEnum WRAPPER where the
     * payload belonged. That is not a cosmetic divergence: the wrapper is
     * handed on as a struct/class receiver, and the first field load past its
     * 32-byte allocation slot reads the NEXT bump allocation's HeapHeader.
     *
     * That is exactly the riscv64 in-guest build-and-run row's blocker
     * (doc/08_tracking/bug/riscv64_in_guest_interp_resets_on_cross_function_call_2026-09-01.md).
     * The interpreter resolves a CALLEE through
     * `resolve_function_by_name(...) -> HirFunction?` and then
     * `cf_target_hit.unwrap()` (70.backend/backend/interpreter_calls.spl:138,181),
     * so `call_hir_function` received a Some-box instead of the HirFunction.
     * Its by-value COW copy of the 248-byte `fn_` parameter then read offset 32
     * of a 32-byte object and found `0x0000003200000001` -- which, read through
     * this TU's own `HeapHeader {uint32_t type; uint32_t size;}`, is
     * type=1 (HEAP_STRING) size=50: a neighbouring RuntimeString's header. It
     * carries TAG_HEAP in its low bits, so the clone's tag test accepted it and
     * dereferenced `size << 32` as an address -> scause=5 load access fault at
     * stval=0x3200000000. The interpreter row stayed GREEN throughout because
     * it reaches call_hir_function only via the `.values()` + typed-local path
     * (interpreter.spl:190-196), which never wraps an optional.
     *
     * This is NOT a new behaviour invented here. It is a PORT of semantics that
     * already exist twice in this tree, and the same defect was already
     * diagnosed and fixed on the x86_64 freestanding sibling:
     *   - src/runtime/runtime_native.c:12972 (the hosted C definition)
     *   - src/runtime/simple_core/core_values.spl:142 (the canonical pure-Simple one)
     *   - examples/09_embedded/simple_os/arch/common/boot/freestanding_value_registry_impl.h:149,
     *     whose comment describes this identical failure -- "every `.unwrap()`
     *     fell through returning the WRAPPER instead of the payload ... the
     *     first field load off it faults" -- for the L5 VFS blocker
     *     (vfs_l5_fat32core_open_faults_on_new_file_write_2026-08-31.md).
     * That fix landed in the COMMON header and in the x86_64 lane; riscv64
     * carries its own duplicate definition in THIS file, which shadows the
     * sibling for this lane and was never brought along. A tree-wide grep for
     * rt_unwrap_or_trap finds the GOOD sibling and looks green -- the exact
     * duplicate-definition trap this boot directory has been bitten by before.
     *
     * DISCRIMINANT FORMS: both are accepted, deliberately. The hosted C
     * definition accepts `discriminant == 0 || == SPL_HASH_SOME` for Some and
     * `1 || SPL_HASH_NONE` for None, because simple-core constructs canonical
     * Options with ORDINAL discriminants (Some=0, None=1) while native lowering
     * identifies Ok/Err by the stable 32-bit variant-name hashes. Accepting
     * only the hashes would leave this function still returning the wrapper for
     * an ordinal-built Option. Mirrored here rather than narrowed.
     *
     * Identification is by heap header, the same basis rt_enum_id /
     * rt_enum_discriminant / rt_enum_payload in this TU already use, so a
     * non-enum value still returns verbatim exactly as before. */
    if (!IS_HEAP(value)) return value;
    RuntimeEnum *e = (RuntimeEnum *)DECODE_PTR(value);
    if (!e || e->hdr.type != HEAP_ENUM) return value;
    {
        const uint32_t some_hash = 4053299545u, none_hash = 2371748697u;
        const uint32_t ok_hash   = 2405352012u, err_hash  = 4200179024u;
        if (e->enum_id == 1u) {
            if (e->discriminant == 0u || e->discriminant == some_hash) return e->payload;
            if (e->discriminant == 1u || e->discriminant == none_hash) {
                serial_puts("\r\n[TRAP] rt_unwrap_or_trap: .unwrap() called on None\r\n");
                rt_qemu_exit_failure();
                for (;;) { __asm__ volatile("wfi"); }
            }
            return value;
        }
        if (e->discriminant == ok_hash) return e->payload;
        if (e->discriminant == err_hash) {
            serial_puts("\r\n[TRAP] rt_unwrap_or_trap: .unwrap() called on Err\r\n");
            rt_qemu_exit_failure();
            for (;;) { __asm__ volatile("wfi"); }
        }
    }
    return value;
}

/* --- generic collection operations ---------------------------------------
 * Receivers are TAGGED handles, exactly as rt_len / rt_contains above take
 * them. Indices returned to Simple are RAW, matching rt_array_len. */

static RuntimeArray *simpleos_array_from_handle(RuntimeValue v)
{
    if (!IS_HEAP(v)) return 0;
    RuntimeArray *a = (RuntimeArray *)DECODE_PTR(v);
    if (!a || a->hdr.type != HEAP_ARRAY) return 0;
    return a;
}

RuntimeValue rt_push(RuntimeValue receiver, RuntimeValue value)
{
    return rt_array_push_handle(receiver, value);
}

RuntimeValue rt_pop(RuntimeValue receiver)
{
    RuntimeArray *a = simpleos_array_from_handle(receiver);
    if (a) return rt_array_pop(receiver);
    if (IS_HEAP(receiver)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(receiver);
        if (s && s->hdr.type == HEAP_STRING) {
            if (s->len == 0) return rt_string_new(0, 0);
            return rt_string_new((RuntimeValue)(uintptr_t)(s->data + s->len - 1), 1);
        }
    }
    return NIL_VALUE;
}

RuntimeValue rt_clear(RuntimeValue receiver)
{
    RuntimeArray *a = simpleos_array_from_handle(receiver);
    if (a) {
        RuntimeValue *items = runtime_array_items(a);
        for (uint64_t i = 0; i < a->len; i++) items[i] = NIL_VALUE;
        a->len = 0;
        return receiver;
    }
    if (IS_HEAP(receiver)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(receiver);
        if (s && s->hdr.type == HEAP_STRING) return rt_string_new(0, 0);
    }
    return receiver;
}

RuntimeValue rt_index_of(RuntimeValue receiver, RuntimeValue needle)
{
    RuntimeArray *a = simpleos_array_from_handle(receiver);
    if (a) {
        RuntimeValue *items = runtime_array_items(a);
        for (uint64_t i = 0; i < a->len; i++) {
            if (items[i] == needle) return (RuntimeValue)(int64_t)i;
            if (rt_string_eq(items[i], needle)) return (RuntimeValue)(int64_t)i;
        }
        return (RuntimeValue)(int64_t)-1;
    }
    if (IS_HEAP(receiver) && IS_HEAP(needle)) {
        RuntimeString *s = (RuntimeString *)DECODE_PTR(receiver);
        RuntimeString *n = (RuntimeString *)DECODE_PTR(needle);
        if (s && n && s->hdr.type == HEAP_STRING && n->hdr.type == HEAP_STRING) {
            if (n->len == 0) return 0;
            if (n->len <= s->len) {
                for (uint64_t i = 0; i + n->len <= s->len; i++) {
                    uint64_t j = 0;
                    while (j < n->len && s->data[i + j] == n->data[j]) j++;
                    if (j == n->len) return (RuntimeValue)(int64_t)i;
                }
            }
        }
    }
    /* Fails CLOSED: -1, never a plausible 0. */
    return (RuntimeValue)(int64_t)-1;
}

/* rt_string_rfind(value, needle) -- the riscv64 freestanding definition of an
 * EXISTING runtime symbol (src/runtime/runtime.h:684), not a new one. The
 * interpreter row's link fails with
 * `ld.lld: error: undefined symbol: rt_string_rfind`, referenced from
 * compiler__hir__hir_lowering___Items__module_lowering__hir_module_package_name.
 *
 * Semantics copied from the hosted rt_string_rfind in src/runtime/runtime_native.c:
 * last index at which `needle` occurs, -1 when absent or either side is not a
 * string, and `s->len` for an EMPTY needle (not 0 — the hosted runtime returns
 * the end position, and a package-name split that got 0 here would silently
 * take the whole string).
 *
 * Return is a RAW int64, matching rt_index_of directly above and this
 * runtime's rt_len — NOT ENCODE_INT. Getting that backwards is the
 * rt_string_bytes tagging defect over again. */
RuntimeValue rt_string_rfind(RuntimeValue value, RuntimeValue needle)
{
    if (!IS_HEAP(value) || !IS_HEAP(needle)) return (RuntimeValue)(int64_t)-1;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(value);
    RuntimeString *n = (RuntimeString *)DECODE_PTR(needle);
    if (!s || !n || s->hdr.type != HEAP_STRING || n->hdr.type != HEAP_STRING) {
        return (RuntimeValue)(int64_t)-1;
    }
    if (n->len == 0) return (RuntimeValue)(int64_t)s->len;
    if (n->len > s->len) return (RuntimeValue)(int64_t)-1;
    for (uint64_t i = (uint64_t)(s->len - n->len) + 1U; i-- > 0;) {
        uint64_t j = 0;
        while (j < n->len && s->data[i + j] == n->data[j]) j++;
        if (j == n->len) return (RuntimeValue)(int64_t)i;
    }
    return (RuntimeValue)(int64_t)-1;
}

RuntimeValue rt_sort(RuntimeValue receiver)
{
    RuntimeArray *a = simpleos_array_from_handle(receiver);
    if (!a || a->len < 2) return receiver;
    RuntimeValue *items = runtime_array_items(a);
    for (uint64_t i = 1; i < a->len; i++) {
        RuntimeValue key = items[i];
        int64_t j = (int64_t)i - 1;
        while (j >= 0 && (int64_t)rt_native_cmp(items[j], key) > 0) {
            items[j + 1] = items[j];
            j--;
        }
        items[j + 1] = key;
    }
    return receiver;
}

RuntimeValue rt_collection_remove(RuntimeValue receiver, RuntimeValue key)
{
    RuntimeArray *a = simpleos_array_from_handle(receiver);
    if (!a) return NIL_VALUE;
    int64_t index = (int64_t)simpleos_raw_or_encoded_int(key);
    if (index < 0 || (uint64_t)index >= a->len) return NIL_VALUE;
    RuntimeValue *items = runtime_array_items(a);
    RuntimeValue removed = items[index];
    for (uint64_t i = (uint64_t)index; i + 1U < a->len; i++) items[i] = items[i + 1U];
    a->len--;
    items[a->len] = NIL_VALUE;
    return removed;
}

RuntimeValue rt_array_copy(RuntimeValue arr)
{
    RuntimeArray *a = simpleos_array_from_handle(arr);
    if (!a) return NIL_VALUE;
    RuntimeValue out = rt_array_new(ENCODE_INT((int64_t)(a->len ? a->len : 16U)));
    if (out == NIL_VALUE) return NIL_VALUE;
    RuntimeValue *src = runtime_array_items(a);
    for (uint64_t i = 0; i < a->len; i++) out = rt_array_push_handle(out, src[i]);
    return out;
}

/* The bump heap (g_heap / rv_alloc) never reclaims — `free` above is already a
 * documented no-op — so freeing one array is a no-op too. Stated rather than
 * silently omitted: the hosted contract is "this array may be reused", and
 * doing nothing satisfies it; doing something would be a use-after-free. */
void rt_array_free(RuntimeValue arr)
{
    (void)arr;
}

int8_t rt_array_extend_i64(int64_t dst, int64_t src, int64_t count)
{
    RuntimeArray *d = simpleos_array_from_handle((RuntimeValue)dst);
    RuntimeArray *s = simpleos_array_from_handle((RuntimeValue)src);
    if (!d || !s || count < 0) return 0;
    if ((uint64_t)count > s->len) return 0;
    RuntimeValue *si = runtime_array_items(s);
    RuntimeValue handle = (RuntimeValue)dst;
    for (int64_t i = 0; i < count; i++) {
        if (rt_array_push_handle(handle, si[i]) == NIL_VALUE) return 0;
    }
    return 1;
}

/* Transient-array scopes are a hosted arena optimisation: the hosted runtime
 * opens a scope, lets short-lived arrays be reclaimed wholesale at its close,
 * and promotes anything that outlives it. This runtime's heap is a pure bump
 * allocator with no reclamation at all, so every array is already effectively
 * promoted and every scope boundary is a no-op that legitimately SUCCEEDS —
 * this is not a stub standing in for missing work, it is the correct answer
 * for an allocator that never frees. Returning 0 (failure) here would be the
 * wrong answer, since nothing failed. */
int8_t rt_transient_array_scope_begin(void) { return 1; }
int8_t rt_transient_array_scope_pause(void) { return 1; }
int8_t rt_transient_array_scope_end(void)   { return 1; }
int8_t rt_transient_heap_promote(int64_t value) { (void)value; return 1; }
/* Promotion share window: a pure walk-avoidance optimisation in the hosted
 * runtimes. With nothing ever reclaimed there is no walk to avoid, so no
 * window ever opens (begin 0 = "no window", promotion unchanged; end 0 =
 * "none was open"), per the runtime.h contract. */
int8_t rt_transient_heap_promote_share_begin(void) { return 0; }
int8_t rt_transient_heap_promote_share_end(void) { return 0; }

/* --- dictionaries ---------------------------------------------------------
 * No dict existed in this arch tree at all.
 *
 * HISTORY, because the previous note here was actively misleading and cost a
 * lane: it said rt_dict_set / rt_dict_get were "deliberately NOT defined here
 * because nothing in this link calls them". The premise was wrong. The
 * interpreter lane's dict traffic does not arrive as `.set()` / `.get()` — it
 * arrives as SUBSCRIPT (`d[k] = v`, `d[k]`), which lowers to
 * rt_index_set / rt_index_get, and those two DID exist and silently dropped
 * every dict write (see the comment on rt_index_set above). So "nothing calls
 * them" was true of the names and false of the operation, and the resulting
 * hole was invisible precisely because a dropped write raises nothing.
 *
 * Both entry points are therefore defined below, over this same layout, and
 * the subscript path routes into the shared helpers rather than duplicating
 * the lookup rule.
 *
 * KEY EQUALITY is raw-handle identity first, then rt_string_eq — the rule
 * rt_dict_contains already used, kept deliberately rather than widened. Struct
 * keys (SymbolId) compare by handle identity, which is correct for every use on
 * this lane: the keys handed to `d[k]` come back out of `.keys()`/`.values()`
 * as the SAME handles, and the interpreter's `main` lookup iterates `.values()`
 * and never re-derives a key. A structural comparator for arbitrary struct keys
 * is a real gap, but it is a DIFFERENT one, and inventing it here unpinned
 * would be exactly the ABI drift the old note rightly warned about.
 *
 * CAPACITY: rt_dict_new caps at 1024 with no growth. A store past capacity
 * FAILS LOUD on serial and returns 0 rather than dropping the pair — a silent
 * drop here is the very defect this block exists to end.
 *
 * HEAP_DICT itself is #defined up with the other heap kinds, because rt_len /
 * rt_index_get / rt_index_set all sit above this point and must recognise a
 * dict receiver. */

typedef struct {
    HeapHeader hdr;
    uint64_t len;
    uint64_t cap;
    RuntimeValue *keys;
    RuntimeValue *vals;
} RuntimeDict;

RuntimeValue rt_dict_new(int64_t cap_hint)
{
    uint64_t cap = (uint64_t)(cap_hint > 0 ? cap_hint : 16);
    if (cap < 16U) cap = 16U;
    if (cap > 1024U) cap = 1024U;
    RuntimeDict *d = (RuntimeDict *)rv_alloc(sizeof(RuntimeDict) + cap * 2U * sizeof(RuntimeValue));
    if (!d) return NIL_VALUE;
    d->hdr.type = HEAP_DICT;
    d->hdr.size = (uint32_t)(sizeof(RuntimeDict) + cap * 2U * sizeof(RuntimeValue));
    d->len = 0;
    d->cap = cap;
    d->keys = (RuntimeValue *)((unsigned char *)d + sizeof(RuntimeDict));
    d->vals = d->keys + cap;
    for (uint64_t i = 0; i < cap; i++) { d->keys[i] = NIL_VALUE; d->vals[i] = NIL_VALUE; }
    return ENCODE_PTR(d);
}

static RuntimeDict *simpleos_dict_from_handle(RuntimeValue v)
{
    if (!IS_HEAP(v)) return 0;
    RuntimeDict *d = (RuntimeDict *)DECODE_PTR(v);
    if (!d || d->hdr.type != HEAP_DICT) return 0;
    return d;
}

int8_t rt_dict_contains(int64_t dict, int64_t key)
{
    RuntimeDict *d = simpleos_dict_from_handle((RuntimeValue)dict);
    if (!d) return 0;
    for (uint64_t i = 0; i < d->len; i++) {
        if (d->keys[i] == (RuntimeValue)key) return 1;
        if (rt_string_eq(d->keys[i], (RuntimeValue)key)) return 1;
    }
    return 0;
}

/* Shared key rule for the store/lookup entry points below: raw handle identity
 * first, then rt_string_eq for text keys — the identical rule rt_dict_contains
 * above spells out inline, kept in one place here so the new paths cannot drift
 * from each other. */
static int simpleos_dict_key_eq(RuntimeValue a, RuntimeValue b)
{
    if (a == b) return 1;
    return rt_string_eq(a, b) ? 1 : 0;
}

/* Slot index of `key`, or -1. */
static int64_t simpleos_dict_find_slot(RuntimeDict *d, RuntimeValue key)
{
    for (uint64_t i = 0; i < d->len; i++) {
        if (simpleos_dict_key_eq(d->keys[i], key)) return (int64_t)i;
    }
    return -1;
}

uint64_t simpleos_dict_count(RuntimeValue dict)
{
    RuntimeDict *d = simpleos_dict_from_handle(dict);
    return d ? d->len : 0;
}

RuntimeValue simpleos_dict_lookup(RuntimeValue dict, RuntimeValue key)
{
    RuntimeDict *d = simpleos_dict_from_handle(dict);
    if (!d) return NIL_VALUE;
    int64_t slot = simpleos_dict_find_slot(d, key);
    return slot < 0 ? NIL_VALUE : d->vals[slot];
}

int8_t simpleos_dict_store(RuntimeValue dict, RuntimeValue key, RuntimeValue item)
{
    RuntimeDict *d = simpleos_dict_from_handle(dict);
    if (!d) return 0;
    int64_t slot = simpleos_dict_find_slot(d, key);
    if (slot >= 0) { d->vals[slot] = item; return 1; }
    if (d->len >= d->cap) {
        /* LOUD, never silent. rt_dict_new does not grow, and a dropped pair
         * here would reproduce exactly the invisible-write defect this block
         * was written to end. */
        serial_puts("\r\n[FATAL] rt_dict_set: dictionary capacity exhausted, "
                    "refusing to drop a key\r\n");
        return 0;
    }
    d->keys[d->len] = key;
    d->vals[d->len] = item;
    d->len++;
    return 1;
}

/* rt_dict_set -- the riscv64 freestanding definition of an EXISTING runtime
 * symbol (src/runtime/runtime.h:746, `int8_t rt_dict_set(int64_t, int64_t,
 * int64_t)`), not a new one.
 *
 * THIS IS THE riscv64 IN-GUEST INTERPRETER ROW'S BLOCKER. Measured from the
 * kept link objects of the pre-fix build: `nm -u mod_*.o` lists rt_dict_set as
 * REFERENCED by generated guest code, and no boot TU defined it. It did not
 * surface as a link error because this lane's "Freestanding unresolved
 * precheck deferred to linker" bridge supplies a silent stub for it — a call
 * that succeeds and does nothing, which is the worst possible failure mode and
 * the one this tree has now been bitten by three times.
 *
 * Consequence: every insertion into `HirModule.functions` was discarded, the
 * dict stayed empty, `module.functions.values()` yielded an empty array, the
 * `f.name == "main"` loop in InterpreterBackendImpl.interpret_hir_module never
 * executed its body once, and the row failed with "module has no main
 * function" — with the HIR itself perfectly well-formed. That is why the
 * symptom pointed at iteration or text compare: both were innocent.
 *
 * Returns int8_t 1/0 (success/failure), matching the hosted declaration. */
int8_t rt_dict_set(int64_t dict, int64_t key, int64_t value)
{
    return simpleos_dict_store((RuntimeValue)dict, (RuntimeValue)key, (RuntimeValue)value);
}

/* rt_dict_get / rt_dict_len mirror the hosted signatures
 * (runtime.h:745, and `int64_t rt_dict_len(int64_t)` returning a RAW count,
 * the same basis as this runtime's rt_len). Defined because a dict that can be
 * written must be readable and measurable by name, not only by subscript. */
int64_t rt_dict_get(int64_t dict, int64_t key)
{
    return (int64_t)simpleos_dict_lookup((RuntimeValue)dict, (RuntimeValue)key);
}

int64_t rt_dict_len(int64_t dict)
{
    RuntimeDict *d = simpleos_dict_from_handle((RuntimeValue)dict);
    return d ? (int64_t)d->len : 0;
}

int64_t rt_dict_keys(int64_t dict)
{
    RuntimeDict *d = simpleos_dict_from_handle((RuntimeValue)dict);
    RuntimeValue out = rt_array_new(ENCODE_INT(16));
    if (!d || out == NIL_VALUE) return (int64_t)out;
    for (uint64_t i = 0; i < d->len; i++) out = rt_array_push_handle(out, d->keys[i]);
    return (int64_t)out;
}

int64_t rt_dict_values(int64_t dict)
{
    RuntimeDict *d = simpleos_dict_from_handle((RuntimeValue)dict);
    RuntimeValue out = rt_array_new(ENCODE_INT(16));
    if (!d || out == NIL_VALUE) return (int64_t)out;
    for (uint64_t i = 0; i < d->len; i++) out = rt_array_push_handle(out, d->vals[i]);
    return (int64_t)out;
}

/* --- process environment --------------------------------------------------
 * A baremetal guest still has no process environment: no exec, no envp, and
 * nothing outside the guest that could have set a variable. What it DOES have,
 * once in-guest compilation runs, is a guest that sets and reads back its own
 * keys: `parse_and_build_module`
 * (src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl) stashes
 * `SIMPLE_BOOTSTRAP_LEX_SOURCE` / `_LEX_PATH`, parses, and restores them on
 * scope exit -- checking the result and `panic`ing on failure (line 1441).
 *
 * The previous always-fail stubs were an honest answer to "what did the
 * PROCESS environment contain" (nothing), but the frontend is not asking that.
 * It is using the environment as its own scratch storage, so answering
 * "absent" to a key this guest itself just set is not truthfulness, it is a
 * wrong answer -- and it panicked the in-guest interpreter with
 * `failed to restore SIMPLE_BOOTSTRAP_LEX_SOURCE for
 * src/os/rv64_interp_hello.spl` the moment module-global initializers started
 * running and execution reached that far
 * (doc/08_tracking/bug/riscv64_freestanding_env_set_unbacked_blocks_in_guest_parse_2026-09-01.md).
 *
 * So: a guest-local table, holding exactly and only what this guest stored.
 * A key never set still reports ABSENCE (nil / the caller's default), so
 * "set to empty" stays distinguishable from "not set" -- the property the old
 * comment was protecting is preserved, and no inherited process environment is
 * fabricated. `rt_env_remove` keeps returning failure for an absent key.
 *
 * Fixed capacity, no growth: the frontend uses a handful of keys and a
 * baremetal guest must not depend on an unbounded allocator here. A set that
 * would exceed the table fails rather than silently dropping a key. */
#define SIMPLEOS_ENV_MAX_ENTRIES 32U

typedef struct {
    char *key;
    uint64_t key_len;
    char *value;
    uint64_t value_len;
} SimpleosEnvEntry;

static SimpleosEnvEntry simpleos_env_table[SIMPLEOS_ENV_MAX_ENTRIES];
static unsigned simpleos_env_count = 0U;

static int simpleos_env_key_eq(const SimpleosEnvEntry *e, const char *key, uint64_t key_len)
{
    if (!e->key || e->key_len != key_len) return 0;
    for (uint64_t i = 0; i < key_len; i++) {
        if (e->key[i] != key[i]) return 0;
    }
    return 1;
}

static SimpleosEnvEntry *simpleos_env_find(const char *key, uint64_t key_len)
{
    if (!key) return (SimpleosEnvEntry *)0;
    for (unsigned i = 0; i < simpleos_env_count; i++) {
        if (simpleos_env_key_eq(&simpleos_env_table[i], key, key_len)) {
            return &simpleos_env_table[i];
        }
    }
    return (SimpleosEnvEntry *)0;
}

static char *simpleos_env_dup(const char *src, uint64_t len)
{
    char *out = (char *)calloc(1, (size_t)len + 1U);
    if (!out) return (char *)0;
    for (uint64_t i = 0; i < len; i++) out[i] = src ? src[i] : 0;
    out[len] = 0;
    return out;
}

/* Deliberately NOT rt_string_new: that helper refuses any length above 4096
 * (see its guard). A stashed lexer SOURCE routinely exceeds that, and a
 * silently truncated restore would corrupt the parse in a way far harder to
 * find than an outright failure. Same layout, no cap. */
static RuntimeValue simpleos_env_string(const char *src, uint64_t len)
{
    RuntimeString *s = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + (uintptr_t)len + 1U);
    if (!s) return NIL_VALUE;
    s->hdr.type = HEAP_STRING;
    s->hdr.size = (uint32_t)(sizeof(RuntimeString) + (uintptr_t)len + 1U);
    s->len = len;
    for (uint64_t i = 0; i < len; i++) s->data[i] = src ? src[i] : 0;
    s->data[len] = 0;
    return ENCODE_PTR(s);
}

RuntimeValue rt_env_get(RuntimeValue key_ptr, uint64_t key_len)
{
    SimpleosEnvEntry *e = simpleos_env_find((const char *)(uintptr_t)key_ptr, key_len);
    if (!e) return NIL_VALUE;
    return simpleos_env_string(e->value, e->value_len);
}

int64_t rt_env_get_i64(RuntimeValue key_ptr, uint64_t key_len, int64_t default_value)
{
    SimpleosEnvEntry *e = simpleos_env_find((const char *)(uintptr_t)key_ptr, key_len);
    if (!e || e->value_len == 0U) return default_value;

    const char *v = e->value;
    uint64_t i = 0;
    int negative = 0;
    if (v[0] == '-') { negative = 1; i = 1; }
    else if (v[0] == '+') { i = 1; }
    if (i >= e->value_len) return default_value;

    int64_t acc = 0;
    for (; i < e->value_len; i++) {
        if (v[i] < '0' || v[i] > '9') return default_value;
        acc = acc * 10 + (int64_t)(v[i] - '0');
    }
    return negative ? -acc : acc;
}

int8_t rt_env_set(RuntimeValue key_ptr, uint64_t key_len, RuntimeValue value_ptr, uint64_t value_len)
{
    const char *key = (const char *)(uintptr_t)key_ptr;
    const char *value = (const char *)(uintptr_t)value_ptr;
    if (!key) return 0;

    char *stored = simpleos_env_dup(value, value_len);
    if (!stored) return 0;

    SimpleosEnvEntry *e = simpleos_env_find(key, key_len);
    if (e) {
        /* The old value is intentionally not freed: this runtime's allocator
         * has no free list, so a free would be a no-op that reads as one. */
        e->value = stored;
        e->value_len = value_len;
        return 1;
    }

    if (simpleos_env_count >= SIMPLEOS_ENV_MAX_ENTRIES) return 0;
    char *stored_key = simpleos_env_dup(key, key_len);
    if (!stored_key) return 0;
    e = &simpleos_env_table[simpleos_env_count];
    e->key = stored_key;
    e->key_len = key_len;
    e->value = stored;
    e->value_len = value_len;
    simpleos_env_count++;
    return 1;
}

int8_t rt_env_remove(RuntimeValue key_ptr, uint64_t key_len)
{
    (void)key_ptr; (void)key_len;
    return 0;
}

RuntimeValue rt_platform_name(void)
{
    return rt_string_from_cstr("riscv64-baremetal-simpleos");
}

int8_t rt_is_debug_mode_enabled(void)
{
    /* Gated by the environment on hosted; no environment here, so: off. */
    return 0;
}

/* --- filesystem -----------------------------------------------------------
 * This arch's only filesystem support is the read-only FAT32 reader in
 * arch/common/riscv_common.h, which resolves 8.3 names inside /SYS/APPS and
 * nothing else — it has no generic path resolution and no write path at all.
 * So these fail CLOSED rather than pretend. That distinction matters: an
 * rt_file_exists that returned 1 would send the caller down a read path that
 * cannot work, and an rt_file_write_text that returned success would silently
 * discard the caller's data. Wiring a general VFS is a real piece of work with
 * its own lane; inventing one inside a runtime port would not be a port. */
int8_t rt_file_exists(RuntimeValue path_ptr, uint64_t path_len)
{
    (void)path_ptr; (void)path_len;
    return 0;
}

int8_t rt_file_is_regular_no_follow(RuntimeValue path_ptr, uint64_t path_len)
{
    (void)path_ptr; (void)path_len;
    return 0;
}

int8_t rt_file_remove(RuntimeValue path_ptr, uint64_t path_len)
{
    (void)path_ptr; (void)path_len;
    return 0;
}

int8_t rt_file_write_text(RuntimeValue path_ptr, uint64_t path_len,
                          RuntimeValue content_ptr, uint64_t content_len)
{
    (void)path_ptr; (void)path_len; (void)content_ptr; (void)content_len;
    return 0;
}

RuntimeValue rt_file_read_text_rv(RuntimeValue path_value)
{
    (void)path_value;
    return NIL_VALUE;
}

/* The hosted probe pair counts rt_file_exists calls so a caller can assert it
 * did not stat in a hot loop. Begin hands back the current count as a token;
 * end returns how many happened since. With rt_file_exists failing closed the
 * counter never advances, so the honest answer is a genuine zero rather than a
 * fabricated one. */
static int64_t g_file_exists_probe_calls = 0;

int64_t rt_file_exists_probe_begin(void)
{
    return g_file_exists_probe_calls;
}

int64_t rt_file_exists_probe_end(int64_t token)
{
    int64_t delta = g_file_exists_probe_calls - token;
    return delta < 0 ? 0 : delta;
}

/* --- time -----------------------------------------------------------------
 * The `time` CSR is the architectural wall clock on RV64 and QEMU's virt board
 * drives it at 10 MHz, which is also what OpenSBI reports in the device tree
 * as timebase-frequency. */
#define RV64_TIMEBASE_HZ 10000000ULL

static uint64_t rv64_read_time(void)
{
    uint64_t t;
    __asm__ volatile("rdtime %0" : "=r"(t));
    return t;
}

int64_t rt_time_now_monotonic_ms(void)
{
    return (int64_t)(rv64_read_time() / (RV64_TIMEBASE_HZ / 1000ULL));
}

/* No RTC and no NTP in this guest, so there is no way to know the Unix epoch.
 * Returning microseconds SINCE BOOT would be a wrong wall-clock answer dressed
 * as a right one — a caller differencing two of them still gets a correct
 * elapsed time, but a caller formatting one gets 1970. Zero is the unambiguous
 * "unknown", and it is what a caller can actually test for. */
int64_t rt_time_now_unix_micros(void)
{
    return 0;
}

/* --- string -> float ------------------------------------------------------
 * Returns a BOXED value (codegen unboxes it with rt_value_as_float right
 * after the call — see codegen/instr/closures_structs.rs:1711), so the return
 * type is I64, not F64. */
RuntimeValue rt_string_to_float(RuntimeValue value)
{
    if (!IS_HEAP(value)) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(value);
    if (!s || s->hdr.type != HEAP_STRING || s->len == 0) return NIL_VALUE;

    uint64_t i = 0;
    while (i < s->len && (s->data[i] == ' ' || s->data[i] == '\t' ||
                          s->data[i] == '\n' || s->data[i] == '\r')) i++;
    int neg = 0;
    if (i < s->len && (s->data[i] == '+' || s->data[i] == '-')) {
        neg = (s->data[i] == '-');
        i++;
    }
    double whole = 0.0;
    int any_digit = 0;
    while (i < s->len && s->data[i] >= '0' && s->data[i] <= '9') {
        whole = whole * 10.0 + (double)(s->data[i] - '0');
        any_digit = 1;
        i++;
    }
    if (i < s->len && s->data[i] == '.') {
        i++;
        double scale = 0.1;
        while (i < s->len && s->data[i] >= '0' && s->data[i] <= '9') {
            whole += (double)(s->data[i] - '0') * scale;
            scale *= 0.1;
            any_digit = 1;
            i++;
        }
    }
    if (!any_digit) return NIL_VALUE;
    /* Decimal exponent, so "1e3" and "2.5E-2" parse as they do hosted. */
    if (i < s->len && (s->data[i] == 'e' || s->data[i] == 'E')) {
        uint64_t save = i;
        i++;
        int eneg = 0;
        if (i < s->len && (s->data[i] == '+' || s->data[i] == '-')) {
            eneg = (s->data[i] == '-');
            i++;
        }
        int edigits = 0;
        int exp = 0;
        while (i < s->len && s->data[i] >= '0' && s->data[i] <= '9' && exp < 4096) {
            exp = exp * 10 + (s->data[i] - '0');
            edigits = 1;
            i++;
        }
        if (!edigits) {
            i = save; /* a trailing 'e' with no digits is not an exponent */
        } else {
            for (int k = 0; k < exp; k++) whole = eneg ? whole * 0.1 : whole * 10.0;
        }
    }
    return rt_value_float(neg ? -whole : whole);
}

/* --- weak-FFI integer call thunk -----------------------------------------
 * Direct port of runtime_native.c:7493. Not an rt_* symbol, but the same kind
 * of thing: the compiler's sugar-registry path (apply_rule_ast) emits a call
 * to it, and it had no freestanding definition.
 *
 * `args_value` is a TAGGED array handle and each element is decoded on the way
 * out, exactly as the hosted body decodes with rt_core_as_int — passing tagged
 * values straight through to a native callee would hand it 8x the intended
 * integer. Guarded identically to hosted: a null pointer, a negative or >8
 * argument count, or an array shorter than nargs all return 0 rather than
 * jumping through an unvalidated pointer. */
int64_t spl_wffi_call_i64(int64_t fptr, int64_t args_value, int64_t nargs)
{
    typedef int64_t (*Fn0)(void);
    typedef int64_t (*Fn1)(int64_t);
    typedef int64_t (*Fn2)(int64_t, int64_t);
    typedef int64_t (*Fn3)(int64_t, int64_t, int64_t);
    typedef int64_t (*Fn4)(int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn5)(int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn6)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn7)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*Fn8)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);

    if (fptr == 0 || nargs < 0 || nargs > 8) return 0;
    int64_t raw[8] = {0};
    if (nargs > 0) {
        RuntimeArray *args = simpleos_array_from_handle((RuntimeValue)args_value);
        if (!args || (uint64_t)nargs > args->len) return 0;
        RuntimeValue *items = runtime_array_items(args);
        for (int64_t i = 0; i < nargs; i++) {
            raw[i] = (int64_t)simpleos_raw_or_encoded_int(items[i]);
        }
    }
    switch (nargs) {
        case 0: return ((Fn0)(uintptr_t)fptr)();
        case 1: return ((Fn1)(uintptr_t)fptr)(raw[0]);
        case 2: return ((Fn2)(uintptr_t)fptr)(raw[0], raw[1]);
        case 3: return ((Fn3)(uintptr_t)fptr)(raw[0], raw[1], raw[2]);
        case 4: return ((Fn4)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3]);
        case 5: return ((Fn5)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4]);
        case 6: return ((Fn6)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4], raw[5]);
        case 7: return ((Fn7)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6]);
        case 8: return ((Fn8)(uintptr_t)fptr)(raw[0], raw[1], raw[2], raw[3], raw[4], raw[5], raw[6], raw[7]);
        default: return 0;
    }
}

/* ---------------------------------------------------------------------------
 * Ports of three hosted concurrency-primitive constructors.
 *
 * Needed because #209 ("freestanding boot never ran module-global
 * initializers") made every `__module_init_*` in the entry closure LIVE. Their
 * module-level globals construct a mutex, an atomic counter and a thread-local
 * slot, so --gc-sections no longer discards those three references and the
 * riscv64 component link failed with exactly three undefined symbols:
 *   rt_mutex_new         (runtime_native.c:3988; src/lib/nogc_sync_mut/concurrent/mutex.spl:11)
 *   rt_atomic_int_new    (runtime_native.c:676;  src/lib/nogc_sync_mut/atomic.spl:32)
 *   rt_thread_local_new  (compiler_rust/runtime/src/value/sffi/sync.rs:128;
 *                         src/lib/nogc_sync_mut/sffi/concurrent.spl:258)
 * Ports of existing hosted names, not new rt_* symbols.
 *
 * ONLY these three are defined, deliberately, for the same reason stated at the
 * dictionary block above: the load/store/lock/unlock siblings are not pinned
 * down by any caller in this link, and writing an entry point no caller has
 * pinned down is how ABI drift gets introduced. If one of them is ever reached
 * it fails CLOSED at link time with a named undefined symbol rather than
 * silently returning a wrong value.
 *
 * This image is single-hart with no preemption inside these paths, so the
 * atomic/mutex state is plain memory — the seq_cst machinery the hosted
 * versions carry has nothing to order against here.
 * ------------------------------------------------------------------------- */

#define HEAP_MUTEX 12U

typedef struct {
    HeapHeader hdr;
    RuntimeValue value;
    uint32_t locked;
} RuntimeMutex;

RuntimeValue rt_mutex_new(RuntimeValue initial)
{
    RuntimeMutex *m = (RuntimeMutex *)rv_alloc(sizeof(RuntimeMutex));
    if (!m) return NIL_VALUE;
    m->hdr.type = HEAP_MUTEX;
    m->hdr.size = (uint32_t)sizeof(RuntimeMutex);
    m->value = initial;
    m->locked = 0;
    return ENCODE_PTR(m);
}

/* Hosted returns a RAW pointer as the handle (`(int64_t)(intptr_t)value`), not
 * a tagged value, and rt_atomic_int_load casts it straight back — so this port
 * must do the same rather than ENCODE_PTR. */
typedef struct {
    int64_t value;
} RuntimeAtomicInt;

int64_t rt_atomic_int_new(int64_t initial)
{
    RuntimeAtomicInt *a = (RuntimeAtomicInt *)rv_alloc(sizeof(RuntimeAtomicInt));
    if (!a) return 0;
    a->value = (int64_t)simpleos_raw_or_encoded_int((RuntimeValue)initial);
    return (int64_t)(intptr_t)a;
}

/* Hosted hands out a monotonically increasing opaque id from a counter that
 * starts at 1, so 0 stays available as "no slot". Same contract here. */
int64_t rt_thread_local_new(void)
{
    static int64_t g_thread_local_next = 1;
    return g_thread_local_next++;
}

/* ---------------------------------------------------------------------------
 * Fifth tranche: the 2026-11-05 compiler-growth gap (bug record
 * doc/08_tracking/bug/riscv64_in_guest_kernel_link_blocked_35_symbols_2026-11-05.md).
 *
 * The in-guest INTERPRETER kernel link (--entry-closure over
 * interpreter_hello_entry.spl) failed with 33 undefined symbols in four
 * buckets. Signatures follow the ABI authority documented above (this file's
 * header and the rt_dict_new block): src/compiler_rust/compiler/src/codegen/
 * runtime_sffi.rs's RuntimeFuncSpec table, checked per symbol below; where a
 * freestanding sibling disagrees with that table, the table wins.
 *
 * The honesty rule is the one the aarch64 freestanding runtime states at its
 * SPL_P10_TRAP block, mirrored here verbatim in intent: (1) REAL SEMANTICS
 * where the computation is host-independent; (2) a DEFINED answer ONLY where
 * it is the true one for this lane and the caller is written to recognise it;
 * (3) a NAMED LOUD TRAP for everything else. A plausible-looking wrong value
 * is never allowed.
 * ------------------------------------------------------------------------- */

/* Named fail-closed trap shared by every admitted stub below. Prints the
 * symbol name over the same serial sink as rt_unwrap_or_trap (this file's
 * diagnostics section) and parks the hart in WFI, exactly like the aarch64
 * sibling's rt_trap_unimplemented. A silent park is indistinguishable from
 * any other guest wedge, so this MUST print. */
static void rv_runtime_trap_unimplemented(const char *symbol)
{
    serial_puts("\r\n[TRAP] rv64 freestanding kernel runtime: `");
    serial_puts(symbol ? symbol : "(null)");
    serial_puts("` was called. No host subsystem backs this entry point in the "
                "in-guest S-mode kernel.\r\n[TRAP] Named trap stub, not an "
                "implementation. Core parked.\r\n");
    for (;;) {
        __asm__ volatile("wfi");
    }
}

/* Arity is spelled per the RuntimeFuncSpec table, but a trap body never
 * returns and never reads an argument, so the shape is only documentation. */
#define RV_RUNTIME_TRAP_N(name)                                  \
    int64_t name(void) {                                         \
        rv_runtime_trap_unimplemented(#name);                    \
        return 0;                                                \
    }
#define RV_RUNTIME_TRAP_1(name)                                  \
    int64_t name(int64_t a) {                                    \
        (void)a;                                                 \
        rv_runtime_trap_unimplemented(#name);                    \
        return 0;                                                \
    }
#define RV_RUNTIME_TRAP_2(name)                                  \
    int64_t name(int64_t a, int64_t b) {                         \
        (void)a; (void)b;                                        \
        rv_runtime_trap_unimplemented(#name);                    \
        return 0;                                                \
    }
#define RV_RUNTIME_TRAP_3(name)                                  \
    int64_t name(int64_t a, int64_t b, int64_t c) {              \
        (void)a; (void)b; (void)c;                               \
        rv_runtime_trap_unimplemented(#name);                    \
        return 0;                                                \
    }
#define RV_RUNTIME_TRAP_5(name)                                  \
    int64_t name(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) { \
        (void)a; (void)b; (void)c; (void)d; (void)e;             \
        rv_runtime_trap_unimplemented(#name);                    \
        return 0;                                                \
    }

/* ---- Bucket 1: pure computation (7). Real semantics, no host dependency. -- */

/* (I64)->(I64), runtime_sffi.rs:899. Same rule as the hosted twin
 * (runtime_native.c:10900): the raw data pointer of the array, 0 when the
 * value is not an array. Inline-item arrays report the inline slot, matching
 * runtime_array_items above. */
int64_t rt_array_data_ptr_text(int64_t collection)
{
    RuntimeArray *a = (RuntimeArray *)0;
    if (IS_HEAP(collection)) {
        RuntimeArray *candidate = (RuntimeArray *)DECODE_PTR(collection);
        if (candidate && candidate->hdr.type == HEAP_ARRAY) a = candidate;
    }
    if (!a) return 0;
    return (int64_t)(intptr_t)runtime_array_items(a);
}

/* (I64)->(I8), runtime_sffi.rs:680. Elements are TAGGED ints (the [i64] and
 * [u8] spellings in utf8.spl / text_bytes.spl are the same physical array), so
 * every element goes through simpleos_raw_or_encoded_int, the same decode the
 * aarch64 sibling's rt_index_arg performs. The codec table is the one
 * src/lib/common/encoding/utf8.spl documents. Semantics follow the hosted
 * twin (runtime_native.c:12441): a value that is not a decodable byte array
 * is REFUSED (0), not reported valid -- the aarch64 sibling answers 1 for a
 * non-array input and that divergence is recorded rather than copied. */
static int64_t rv_utf8_find_invalid(int64_t bytes_value)
{
    if (!IS_HEAP(bytes_value)) return 0;
    RuntimeArray *array = (RuntimeArray *)DECODE_PTR(bytes_value);
    if (!array || array->hdr.type != HEAP_ARRAY) return 0;
    uint64_t i = 0;
    while (i < array->len) {
        uint32_t b0 = (uint32_t)(simpleos_raw_or_encoded_int(array->items[i]) & 0xFF);
        int64_t need;
        uint32_t cp;
        if (b0 < 0x80U) need = 1;
        else if (b0 >= 0xC2U && b0 <= 0xDFU) need = 2;
        else if (b0 >= 0xE0U && b0 <= 0xEFU) need = 3;
        else if (b0 >= 0xF0U && b0 <= 0xF4U) need = 4;
        else return (int64_t)i;
        if (i + (uint64_t)need > array->len) return (int64_t)i;
        if (need == 1) {
            i += 1;
            continue;
        }
        for (int64_t k = 1; k < need; k++) {
            uint32_t bk = (uint32_t)(simpleos_raw_or_encoded_int(array->items[i + (uint64_t)k]) & 0xFF);
            if ((bk & 0xC0U) != 0x80U) return (int64_t)i;
        }
        {
            uint32_t b1 = need > 1 ? (uint32_t)(simpleos_raw_or_encoded_int(array->items[i + 1]) & 0xFF) : 0U;
            uint32_t b2 = need > 2 ? (uint32_t)(simpleos_raw_or_encoded_int(array->items[i + 2]) & 0xFF) : 0U;
            uint32_t b3 = need > 3 ? (uint32_t)(simpleos_raw_or_encoded_int(array->items[i + 3]) & 0xFF) : 0U;
            if (need == 2) {
                cp = ((b0 & 0x1FU) << 6) | (b1 & 0x3FU);
                if (cp < 0x80U) return (int64_t)i;
            } else if (need == 3) {
                cp = ((b0 & 0x0FU) << 12) | ((b1 & 0x3FU) << 6) | (b2 & 0x3FU);
                if (cp < 0x800U) return (int64_t)i;
                if (cp >= 0xD800U && cp <= 0xDFFFU) return (int64_t)i;
            } else {
                cp = ((b0 & 0x07U) << 18) | ((b1 & 0x3FU) << 12) |
                     ((b2 & 0x3FU) << 6) | (b3 & 0x3FU);
                if (cp < 0x10000U || cp > 0x10FFFFU) return (int64_t)i;
            }
        }
        i += (uint64_t)need;
    }
    return -1;
}

int8_t rt_utf8_validate(int64_t bytes_value)
{
    if (!IS_HEAP(bytes_value)) return 0;
    {
        RuntimeArray *array = (RuntimeArray *)DECODE_PTR(bytes_value);
        if (!array || array->hdr.type != HEAP_ARRAY) return 0;
    }
    return rv_utf8_find_invalid(bytes_value) < 0 ? 1 : 0;
}

/* (I64,I64)->(I64), runtime_sffi.rs:420. Raw-address read with a tagged
 * result, the x86_64 freestanding sibling's exact body (rt_extras.c:381):
 * the address and offset are raw words, the loaded word is ENCODE_INT'd. */
int64_t rt_ptr_read_i64(int64_t addr, int64_t offset)
{
    int64_t *p = (int64_t *)((uintptr_t)addr + (uintptr_t)offset);
    return (int64_t)ENCODE_INT(*p);
}

/* (I64)->(I64) and (I64,I64,I64)->(I8), runtime_sffi.rs:345,348. These are
 * the load/CAS siblings of rt_atomic_int_new above (this file's fourth
 * tranche): the handle is the RAW cell pointer that rt_atomic_int_new
 * returns, and the stored word is whatever simpleos_raw_or_encoded_int made
 * of the constructor argument -- both ported verbatim, never re-decoded here,
 * matching the hosted twin (runtime_native.c:988-1000). The hosted contract
 * returns the cell word verbatim from load; a NULL handle reads as 0 and the
 * CAS reports failure, again as hosted. This image is single-hart, but the
 * seq_cst builtins are kept anyway -- they cost nothing and cannot silently
 * weaken if the lane ever grows a second hart. */
int64_t rt_atomic_int_load(int64_t handle)
{
    RuntimeAtomicInt *a = (RuntimeAtomicInt *)(intptr_t)handle;
    if (!a) return 0;
    return __atomic_load_n(&a->value, __ATOMIC_SEQ_CST);
}

int8_t rt_atomic_int_compare_exchange(int64_t handle, int64_t current, int64_t new_value)
{
    RuntimeAtomicInt *a = (RuntimeAtomicInt *)(intptr_t)handle;
    int64_t expected = current;
    if (!a) return 0;
    return __atomic_compare_exchange_n(&a->value, &expected, new_value, 0,
                                       __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST)
               ? 1
               : 0;
}

/* (I64)->(I8), runtime_sffi.rs:720. NOT truthiness: the hosted twin
 * (runtime_native.c:4238) decodes the tagged bool, i.e. answers 1 only for
 * the codegen `true` constant. In this lane's tag table (see
 * rt_value_unbox_int above) that constant is 11, `false` is 19. The x86_64
 * freestanding sibling's body is a truthiness test and contradicts the
 * hosted contract; the hosted twin is mirrored instead. */
int8_t rt_value_as_bool(int64_t value)
{
    return value == (int64_t)TRUE_VALUE ? 1 : 0;
}

/* (I64)->(I8), runtime_sffi.rs:742. Mirror of the hosted
 * rt_core_value_truthy (runtime_native.c:11914), with this lane's float
 * representations (heap cell from rt_value_float, legacy shifted TAG_FLOAT):
 * ints test their decoded value; the tagged bool constant tests equal to
 * `true`; heap words test a non-NULL payload; floats test != 0.0. Char
 * truthiness is a type error on the hosted twin and fails closed there, so
 * it fails closed here too -- loudly, through the named trap. */
int8_t rt_value_truthy(int64_t value)
{
    uintptr_t tag = (uintptr_t)value & TAG_MASK;
    if (tag == TAG_SPECIAL) {
        uint64_t payload = ((uint64_t)value) >> 3;
        if ((payload & ~0x1FFFFFULL) == (1ULL << 40)) {
            rv_runtime_trap_unimplemented("rt_value_truthy(char: type error, compare explicitly)");
        }
        return value == (int64_t)TRUE_VALUE ? 1 : 0;
    }
    if (tag == TAG_INT) return DECODE_INT((RuntimeValue)value) != 0 ? 1 : 0;
    if (tag == TAG_HEAP) return ((uint64_t)value & ~TAG_MASK) != 0 ? 1 : 0;
    if (tag == TAG_FLOAT) {
        uint64_t bits = (uint64_t)value >> 3;
        double f;
        __builtin_memcpy(&f, &bits, sizeof(f));
        return f != 0.0 ? 1 : 0;
    }
    return 0;
}

/* ---- Bucket 2: io / process / thread — no VFS, no processes, no threads
 * in the in-guest S-mode kernel. Every caller reaches for a host subsystem
 * this image does not have, so every one traps with a named message. This
 * mirrors the aarch64 freestanding sibling's SPL_P10_TRAP block; the x86_64
 * sibling's silent NIL no-ops for the same names are the silent-lie class
 * and were NOT copied. */
RV_RUNTIME_TRAP_3(rt_io_file_open)          /* (path_ptr, path_len, mode) -> fd */
RV_RUNTIME_TRAP_2(rt_io_file_open_read)     /* (path_ptr, path_len) -> fd       */
RV_RUNTIME_TRAP_2(rt_io_file_open_write)    /* (path_ptr, path_len) -> fd       */
RV_RUNTIME_TRAP_2(rt_io_file_open_append)   /* (path_ptr, path_len) -> fd       */
RV_RUNTIME_TRAP_2(rt_io_file_read)          /* (fd, size) -> array              */
RV_RUNTIME_TRAP_3(rt_io_file_seek)          /* (fd, offset, whence) -> pos      */
RV_RUNTIME_TRAP_1(rt_io_file_close_value)   /* (fd) -> 0/1                      */
RV_RUNTIME_TRAP_3(rt_process_run)           /* (cmd_ptr, cmd_len, args) -> ...  */
RV_RUNTIME_TRAP_5(rt_process_run_bounded)   /* + timeout_ms, max_output_bytes   */
RV_RUNTIME_TRAP_3(rt_process_run_tuple)     /* (cmd_ptr, cmd_len, args) -> i64  */
RV_RUNTIME_TRAP_5(rt_process_run_bounded_tuple)

void rt_thread_sleep(int64_t millis)
{
    (void)millis;
    rv_runtime_trap_unimplemented("rt_thread_sleep");
}

/* ---- Capability / identity queries. Truthful DEFINED answers where the
 * caller is written to recognise them, named traps elsewhere. */

/* Signal and atexit state, like the aarch64 freestanding sibling
 * (freestanding_runtime.c:2596-2615): SimpleOS in-guest has no POSIX signal
 * delivery and no process teardown, so "nothing pending" is the true answer,
 * and src/lib/nogc_sync_mut/io/signal_stubs.spl reads `<= 0` as
 * "not installed". Returning a nonzero fake pending flag would register a
 * handler that can never fire -- the silent lie -- so 0 it is. */
int64_t rt_signal_check(int64_t signal_num)
{
    (void)signal_num;
    return 0;
}

int64_t rt_atexit_check(void)
{
    return 0;
}

/* runtime_sffi.rs:2422-2423. There is no honest static answer: this image is
 * an AOT-compiled freestanding kernel that is neither the hosted tree-walk
 * interpreter runtime nor a JIT runtime, but its callers branch real
 * behaviour on the answer (flat_pool_packed_v1.spl:1051 chooses an mmap
 * fast path on "not interpreter"). Guessing `false` would route the guest
 * into a host-mapping path that does not exist here; the record's bucket
 * rule for capability queries is fail closed, so both trap with a named
 * message. */
RV_RUNTIME_TRAP_N(rt_is_interpreter_runtime)
RV_RUNTIME_TRAP_N(rt_is_jit_runtime)

/* ()->(I64), runtime_sffi.rs:1075. The x86_64 sibling answers a hardcoded 1
 * (its guest is uniprocessor); this lane's guest hart count is a boot
 * property, not a constant, so a fixed number could silently lie under a
 * multi-hart -smp. The aarch64 sibling traps; that is mirrored. */
RV_RUNTIME_TRAP_N(spl_thread_cpu_count)

/* ---- Bucket 3: adaptive-collection capture-note instrumentation
 * (runtime_sffi.rs:2467-2472, hosted twin runtime_collection_capture_impl.h).
 * The hosted contract for every note_* entry is: return 1 when no capture
 * session is active ("nothing to record"), 0 on a recording error. A
 * freestanding in-guest kernel can never begin a capture session (its
 * begin/finish/abort surface is not in this closure and would itself need
 * host I/O), so "capture inactive" is the TRUE state of this lane and 1 is
 * the honest no-op-with-note answer -- exactly what the hosted twin returns
 * before any session starts. */
int64_t spl_collection_capture_note_size(int64_t site, int64_t target, int64_t size)
{
    (void)site; (void)target; (void)size;
    return 1;
}

int64_t spl_collection_capture_note_lookup(int64_t site, int64_t target, int64_t found)
{
    (void)site; (void)target; (void)found;
    return 1;
}

int64_t spl_collection_capture_note_materialization(int64_t site, int64_t target)
{
    (void)site; (void)target;
    return 1;
}

int64_t spl_collection_capture_note_hash_probe(int64_t site, int64_t target, int64_t probes, int64_t collisions)
{
    (void)site; (void)target; (void)probes; (void)collisions;
    return 1;
}

int64_t spl_collection_capture_note_filter(int64_t site, int64_t target, int64_t evaluated, int64_t accepted)
{
    (void)site; (void)target; (void)evaluated; (void)accepted;
    return 1;
}

int64_t spl_collection_capture_note_loop(int64_t site, int64_t target, int64_t trips)
{
    (void)site; (void)target; (void)trips;
    return 1;
}

/* ---- Bucket 4: session / transient heap (runtime_sffi.rs:458-460; the
 * state query is the (I64)->() form declared in bootstrap_hir_store.spl:38).
 *
 * No freestanding sibling ANYWHERE in the tree implements this discipline
 * (checked: aarch64 and x86_64 freestanding runtimes, src/os/kernel/arch
 * freestanding runtimes). Porting it wrong -- refuse-everything or
 * accept-everything stubs -- would silently change what the in-guest BUILD
 * half produces, the exact silent-lie class the bug record names. So:
 *
 *   rt_session_alloc_begin/end -> 0, the hosted "no live session" answer
 *     (runtime_native.c:3539-3549 returns 0 when no session heap is live).
 *     A 0 keeps the bootstrap stores' session_on=false, which selects the
 *     pre-session LEGACY append+promote path -- the path this guest row
 *     actually booted with before the session discipline existed. That is a
 *     true, caller-recognised answer, not a stub.
 *   rt_transient_array_scope_state_v1 -> 0: no module scope is running on a
 *     runtime that has no scope machinery; bootstrap_hir_store.spl:68 reads
 *     == 1 as "scope running", so 0 keeps the same legacy path.
 *   rt_transient_heap_adopt -> NAMED TRAP. Adopt is reached only from the
 *     session publish path; if execution ever gets there on this lane, the
 *     session discipline the caller assumes does not exist and no return
 *     value is truthful -- failing loud beats failing plausible. This bucket
 *     is therefore PARTIALLY addressed: the image links and the legacy
 *     no-session path works; a real in-guest session heap needs the design
 *     session the bug record calls for. */
int8_t rt_session_alloc_begin(void)
{
    return 0;
}

int8_t rt_session_alloc_end(void)
{
    return 0;
}

int64_t rt_transient_array_scope_state_v1(void)
{
    return 0;
}

int8_t rt_transient_heap_adopt(int64_t value)
{
    (void)value;
    rv_runtime_trap_unimplemented("rt_transient_heap_adopt");
    return 0;
}


/* ---------------------------------------------------------------------------
 * Fifth tranche, part 2: the build-and-run row's own closure gap, measured on
 * the same link (the record above lists the interpreter row's set; the
 * buildrun row references nine further names, reported here per the same
 * buckets and the same honesty rule).
 * ------------------------------------------------------------------------- */

/* ---- Pure computation (6). Real semantics. -------------------------------- */

/* (I64)->(I64), runtime_sffi.rs:499. Hosted twin (runtime_native.c:11519):
 * the array length, -1 when the value is not an array. Tuples are HEAP_ARRAY
 * in this runtime (rt_tuple_new above), so the array rule covers them. */
int64_t rt_tuple_len(int64_t tuple)
{
    RuntimeArray *a = simpleos_array_from_handle((RuntimeValue)tuple);
    if (!a) return -1;
    return (int64_t)a->len;
}

/* ()->(I64), (I64)->(I8), (I64)->(I8): runtime_sffi.rs:716,721,722. The
 * hosted twins are one line each (runtime_native.c:4242-4258) and port
 * verbatim under this lane's tag table: nil is the TAG_SPECIAL word 3
 * (NIL_VALUE above), int is the TAG_INT low tag. The hosted is_int also
 * accepts heap-int/heap-uint boxes; this runtime has no such boxes (its
 * integers are always inline TAG_INT), so the tag test is the whole truth
 * here, not a weakening. */
int64_t rt_value_nil(void)
{
    return (int64_t)NIL_VALUE;
}

int8_t rt_value_is_nil(int64_t value)
{
    return value == (int64_t)NIL_VALUE ? 1 : 0;
}

int8_t rt_value_is_int(int64_t value)
{
    return ((uintptr_t)value & TAG_MASK) == TAG_INT ? 1 : 0;
}

/* Non-mutating `sorted`, hosted twin runtime_native.c:7239. Same contract:
 * a NEW array (the input and its order are preserved), nil when the receiver
 * is not an array. The comparator is the hosted rt_sorted_value_cmp rule:
 * two texts compare byte-lexicographically (shorter prefix first); tagged
 * ints compare numerically; floats compare numerically; ints sort before
 * floats; anything else mixed compares Equal. This lane's float forms are
 * the tranche-4 HEAP_FLOAT cell and the legacy shifted TAG_FLOAT, handled
 * exactly as rt_value_as_float above. The hosted twin sorts with a stable
 * O(n log n) merge; this port keeps this file's existing rt_sort insertion
 * sort so the comparator has exactly one local definition -- the row's
 * sorted arrays are small, and a stable sort answers identically either
 * way. */
static int rv_sorted_value_cmp(int64_t a, int64_t b)
{
    RuntimeString *sa = IS_HEAP(a) ? (RuntimeString *)DECODE_PTR(a) : (RuntimeString *)0;
    RuntimeString *sb = IS_HEAP(b) ? (RuntimeString *)DECODE_PTR(b) : (RuntimeString *)0;
    if (sa && sa->hdr.type != HEAP_STRING) sa = 0;
    if (sb && sb->hdr.type != HEAP_STRING) sb = 0;
    /* Both texts byte-lexicographically. rt_text_cmp_any treats a non-text
     * side as "", so it may only be used when BOTH sides are texts --
     * otherwise a text/int pair would order as "vs empty string" instead of
     * Equal, which is the hosted mixed-type answer. */
    if (sa && sb) {
        return (int)(int64_t)rt_text_cmp_any((RuntimeValue)a, (RuntimeValue)b);
    }
    {
        int a_is_int = ((uintptr_t)a & TAG_MASK) == TAG_INT;
        int b_is_int = ((uintptr_t)b & TAG_MASK) == TAG_INT;
        int a_is_float = (((uintptr_t)a & TAG_MASK) == TAG_FLOAT) ||
                         (IS_HEAP(a) && sa == 0 && ((HeapHeader *)DECODE_PTR(a))->type == HEAP_FLOAT);
        int b_is_float = (((uintptr_t)b & TAG_MASK) == TAG_FLOAT) ||
                         (IS_HEAP(b) && sb == 0 && ((HeapHeader *)DECODE_PTR(b))->type == HEAP_FLOAT);
        if (a_is_int && b_is_int) {
            int64_t x = DECODE_INT((RuntimeValue)a);
            int64_t y = DECODE_INT((RuntimeValue)b);
            return (x > y) - (x < y);
        }
        if (a_is_float && b_is_float) {
            double x = rt_value_as_float((RuntimeValue)a);
            double y = rt_value_as_float((RuntimeValue)b);
            return (x > y) - (x < y); /* NaN compares Equal, as hosted. */
        }
        if (a_is_int && b_is_float) return -1;
        if (a_is_float && b_is_int) return 1;
        return 0;
    }
}

int64_t rt_array_sorted(int64_t receiver)
{
    RuntimeArray *a = simpleos_array_from_handle((RuntimeValue)receiver);
    if (!a) return (int64_t)NIL_VALUE;
    {
        RuntimeValue copy = rt_array_copy((RuntimeValue)receiver);
        RuntimeArray *c;
        RuntimeValue *items;
        if (copy == NIL_VALUE) return (int64_t)NIL_VALUE;
        c = simpleos_array_from_handle(copy);
        if (!c) return (int64_t)NIL_VALUE;
        items = runtime_array_items(c);
        for (uint64_t i = 1; i < c->len; i++) {
            int64_t key = (int64_t)items[i];
            int64_t j = (int64_t)i - 1;
            while (j >= 0 && rv_sorted_value_cmp((int64_t)items[(uint64_t)j], key) > 0) {
                items[(uint64_t)j + 1] = items[(uint64_t)j];
                j--;
            }
            items[(uint64_t)j + 1] = (RuntimeValue)key;
        }
        return (int64_t)copy;
    }
}

/* ---- HIR codec node guard (1): defined, caller-recognised answer. --------- */

/* (I64)->(I8). Referenced by src/compiler/20.hir/generated/hir_codec.spl:17,68.
 * The hosted standalone-lane twin (runtime_native.c:11671, the
 * SIMPLE_CORE_C_STANDALONE form) is the wellformed probe, NOT the strict
 * registry-membership probe of mixed builds: AOT lowering allocates HIR node
 * structs as raw rt_alloc blocks that are never registered, so a
 * registry-only answer would refuse every HIR module and the codec would
 * cache nothing -- the documented Phase-3 failure. That is exactly this
 * lane's situation (bump-arena objects, no registry), so the standalone twin
 * is mirrored: reject nil and the zero page, accept everything else. False
 * rejects are safe (they only decline to cache), false accepts only mean a
 * garbage node is read later, which the codec's own guards name. */
int8_t rt_heap_ref_registered(int64_t value)
{
    return (((uint64_t)value) & ~TAG_MASK) >= 4096 ? 1 : 0;
}

/* ---- Evidence snapshot + VFS reads (2): fail closed. ---------------------- */

/* (I64,I64)->(I64), runtime_sffi.rs:2275, and the 19-word record form below.
 * Hosted twin (runtime.c:2353) opens a host evidence file O_EXCL|O_NOFOLLOW;
 * the in-guest kernel has no writable evidence sink and no host filesystem,
 * so setup truthfully fails closed with -1 -- the caller
 * (src/compiler/80.driver/driver_mem_snapshot.spl:48) reports -1 as
 * "fail-closed setup failure" and disables recording. rt_mem_snapshot_record
 * is only reached when a snapshot fd >= 0 exists, which this answer never
 * produces; if execution ever reaches it anyway, the named trap fires --
 * there is no truthful record to write. */
int64_t rt_mem_snapshot_open(int64_t path_ptr, int64_t path_len)
{
    (void)path_ptr; (void)path_len;
    return -1;
}

int64_t rt_mem_snapshot_record(int64_t fd, int64_t seq,
                               int64_t event_ptr, int64_t event_len,
                               int64_t phase_ptr, int64_t phase_len,
                               int64_t source_index,
                               int64_t source_path_ptr, int64_t source_path_len,
                               int64_t retained_modules, int64_t validation_keys,
                               int64_t validation_values, int64_t shared_traits,
                               int64_t hir_names, int64_t hir_symbols,
                               int64_t hir_functions, int64_t hir_constants,
                               int64_t hir_enums, int64_t hir_structs,
                               int64_t hir_classes)
{
    (void)fd; (void)seq;
    (void)event_ptr; (void)event_len;
    (void)phase_ptr; (void)phase_len;
    (void)source_index;
    (void)source_path_ptr; (void)source_path_len;
    (void)retained_modules; (void)validation_keys;
    (void)validation_values; (void)shared_traits;
    (void)hir_names; (void)hir_symbols;
    (void)hir_functions; (void)hir_constants;
    (void)hir_enums; (void)hir_structs;
    (void)hir_classes;
    rv_runtime_trap_unimplemented("rt_mem_snapshot_record");
    return 0;
}

/* (I64,I64,I64)->(I64) and ()->(I64), runtime_sffi.rs:2243-2244. The readers
 * go through the same host-filesystem bucket as rt_io_file_* above: trap with
 * a named message. The failure-code query is a different kind of entry point:
 * with the readers trapped it is never preceded by a read, so the hosted
 * "never called" sentinel 77 is its truthful value, spelled out so no caller
 * mistakes it for a real arm code. */
RV_RUNTIME_TRAP_3(rt_file_read_regular_no_follow_bounded_bytes)

int64_t rt_file_read_regular_no_follow_last_failure(void)
{
    return 77; /* hosted sentinel: never called */
}

#undef RV_RUNTIME_TRAP_N
#undef RV_RUNTIME_TRAP_1
#undef RV_RUNTIME_TRAP_2
#undef RV_RUNTIME_TRAP_3
#undef RV_RUNTIME_TRAP_5
