#include <stddef.h>
#include <stdint.h>

typedef intptr_t RuntimeValue;

#define TAG_MASK ((uintptr_t)0x7)
#define TAG_INT ((uintptr_t)0x0)
#define TAG_HEAP ((uintptr_t)0x1)
#define TAG_SPECIAL ((uintptr_t)0x3)
#define NIL_VALUE ((RuntimeValue)TAG_SPECIAL)

#define ENCODE_INT(v) ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3) | TAG_INT))
#define DECODE_INT(v) ((int64_t)((uint64_t)(v) >> 3))
#define ENCODE_PTR(p) ((RuntimeValue)((uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v) ((void *)((uintptr_t)(v) & ~TAG_MASK))
#define IS_INT(v) (((uintptr_t)(v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v) (((uintptr_t)(v) & TAG_MASK) == TAG_HEAP)

#define HEAP_STRING 1U
#define HEAP_ARRAY 2U
#define HEAP_DICT 11U
/* Not duplicated across the runtime TUs; resolve to the single owner. */
uint64_t     simpleos_dict_count(RuntimeValue dict);
RuntimeValue simpleos_dict_lookup(RuntimeValue dict, RuntimeValue key);
int8_t       simpleos_dict_store(RuntimeValue dict, RuntimeValue key, RuntimeValue item);

#define HEAP_ENUM 7U

typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

/* len MUST be uint64_t / data at offset 16 — codegen inlines .len() as an
 * i64 load at offset 8. See arch/common/baremetal_runtime.h. */
typedef struct {
    HeapHeader hdr;
    uint64_t len;
    char data[];
} RuntimeString;
_Static_assert(offsetof(RuntimeString, len) == 8, "RuntimeString.len must sit at offset 8");
_Static_assert(offsetof(RuntimeString, data) == 16, "RuntimeString.data must sit at offset 16");

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

/* This TU duplicates malloc/calloc/realloc/free/rt_alloc with the two main
 * riscv64 runtime TUs (baremetal_stubs.c, baremetal_runtime_core.inc.c), and
 * the link resolves the duplicates with --allow-multiple-definition: exactly
 * ONE copy serves the WHOLE image's allocations, and which copy that is is a
 * link-order lottery the caller does not control. Every duplicate must
 * therefore be sized for the whole image AND must not share storage with
 * module globals.
 *
 * The 2026-11-05 first attempt at that invariant -- a 32 MiB STATIC .bss
 * array -- is the measured root cause of the in-guest par_state corruption:
 * the array landed at the START of .bss (g_heap at 0x80665000, spanning
 * 32 MiB) and the parser module global par_state was placed INSIDE its span
 * (0x8266... family build: par_state at 0x80676fc0, g_heap+0x11fc0). Every
 * code-side allocation then bump-overlaid live module globals (watchpoint
 * lane, doc/08_tracking/bug/riscv64_in_guest_parse_recursion_par_state_uninit_2026-11-05.md):
 * .bss is for ZEROED GLOBALS, not for an allocator arena. This TU now does
 * what the other two do: own a private, linker-accounted slice of the
 * linker-reserved 64 MiB .heap (NOLOAD, outside .bss). The three cursors
 * own disjoint thirds so no lottery outcome can alias another TU's region. */
extern unsigned char __heap_start[];
extern unsigned char __heap_end[];
#define RV_HEAP_BASE (__heap_start + 2ULL * ((unsigned long long)(__heap_end - __heap_start) / 3ULL))
#define RV_HEAP_SIZE ((size_t)(__heap_end - __heap_start) / 3U)
static uintptr_t g_heap_off = 0;

extern RuntimeValue spl_start(void);
extern char _stack_top[];

#include "rv64_image_header.inc.h"
__attribute__((naked, section(".text.entry"))) void _start(void)
{
    __asm__ volatile(
        /* RISC-V Linux boot-image header v0.2 — see rv64_image_header.inc.h;
         * gated by check-simpleos-riscv64-image-header-contract.shs. */
        RV64_IMAGE_HEADER_ASM
        "la sp, _stack_top\n"
        "call spl_start\n"
        "1: wfi\n"
        "j 1b\n"
    );
}

#include "../../common/baremetal_bump_heap.h"

static RuntimeValue *runtime_array_inline_items(RuntimeArray *array)
{
    return (RuntimeValue *)((unsigned char *)array + sizeof(RuntimeArray));
}

static RuntimeValue *runtime_array_items(RuntimeArray *array)
{
    if (!array) return 0;
    return array->items ? array->items : runtime_array_inline_items(array);
}

static uint64_t simpleos_raw_or_encoded_int(RuntimeValue value)
{
    return IS_INT(value) ? (uint64_t)DECODE_INT(value) : (uint64_t)value;
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
    return rv_calloc(n, size);
}

void *realloc(void *ptr, size_t size)
{
    return rv_realloc(ptr, size);
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

RuntimeValue rt_alloc(RuntimeValue size)
{
    /* compile_struct_init passes RAW size (not tagged) -- the identical
     * contract the x86_64 sibling documents at its baremetal_stubs.c:763
     * and the other two riscv64 runtime TUs implement verbatim. Decoding
     * here (simpleos_raw_or_encoded_int) divided every multiple-of-8 byte
     * size by 8 (120 -> 15), under-allocating every struct literal and
     * producing the in-guest par_state overlay
     * (doc/08_tracking/bug/riscv64_in_guest_parse_recursion_par_state_uninit_2026-11-05.md). */
    size_t bytes = (size_t)size;
    void *ptr = calloc(1, bytes);
    return ptr ? (RuntimeValue)(uintptr_t)ptr : 0;
}

RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len_val)
{
    uintptr_t len = (uintptr_t)len_val;
    if (len > 4096U) return NIL_VALUE;
    RuntimeString *string = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + len + 1U);
    if (!string) return NIL_VALUE;
    string->hdr.type = HEAP_STRING;
    string->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1U);
    string->len = (uint32_t)len;
    const char *src = (const char *)(uintptr_t)data;
    for (uintptr_t i = 0; i < len; i++) string->data[i] = src ? src[i] : 0;
    string->data[len] = 0;
    return ENCODE_PTR(string);
}

RuntimeValue rt_array_new(RuntimeValue cap_val)
{
    uint64_t cap = simpleos_raw_or_encoded_int(cap_val);
    if (cap == 0) cap = 16;
    if (cap < 16) cap = 16;
    RuntimeArray *array = (RuntimeArray *)rv_alloc(sizeof(RuntimeArray) + cap * sizeof(RuntimeValue));
    if (!array) return NIL_VALUE;
    array->hdr.type = HEAP_ARRAY;
    array->hdr.size = (uint32_t)(sizeof(RuntimeArray) + cap * sizeof(RuntimeValue));
    array->len = 0;
    array->cap = cap;
    array->items = runtime_array_inline_items(array);
    for (uint64_t i = 0; i < cap; i++) array->items[i] = NIL_VALUE;
    return ENCODE_PTR(array);
}

RuntimeValue rt_array_new_with_cap(int64_t cap)
{
    return rt_array_new((RuntimeValue)cap);
}

/* The growth logic MUST live in this TU's copy, not only in the other
 * runtime TUs: which duplicate definition wins the
 * --allow-multiple-definition link is a per-closure lottery, and on the
 * 2026-11-06 interpreter closure THIS copy won rt_array_push with the
 * pre-fix body (len >= cap -> return 0, no growth). Every `[]` defaults
 * to cap 16 (rt_array_new above), so the lexer scan_string parts array
 * silently dropped every char past 16 and interpreted string literals
 * truncated to "HELLO_INTERP_SIM" (16 chars) — measured by RSP
 * write-watchpoint on the result object. Mirrors baremetal_stubs.c
 * rt_array_push_handle, whose growth this copy now shares verbatim. */
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

int8_t rt_array_push(RuntimeValue array_value, RuntimeValue item)
{
    return rt_array_push_handle(array_value, item) != NIL_VALUE;
}

static RuntimeValue rt_array_get(RuntimeValue array_value, RuntimeValue index)
{
    if (!IS_HEAP(array_value)) return NIL_VALUE;
    RuntimeArray *array = (RuntimeArray *)DECODE_PTR(array_value);
    int64_t i = (int64_t)index;
    if (!array || array->hdr.type != HEAP_ARRAY || i < 0 || (uint64_t)i >= array->len) return NIL_VALUE;
    return runtime_array_items(array)[i];
}

static int8_t rt_array_set(RuntimeValue array_value, RuntimeValue index, RuntimeValue item)
{
    if (!IS_HEAP(array_value)) return 0;
    RuntimeArray *array = (RuntimeArray *)DECODE_PTR(array_value);
    int64_t i = (int64_t)index;
    if (!array || array->hdr.type != HEAP_ARRAY || i < 0 || (uint64_t)i >= array->len) return 0;
    runtime_array_items(array)[i] = item;
    return 1;
}

RuntimeValue rt_tuple_new(RuntimeValue len_value)
{
    uint64_t len = simpleos_raw_or_encoded_int(len_value);
    RuntimeArray *array = (RuntimeArray *)rv_alloc(sizeof(RuntimeArray) + len * sizeof(RuntimeValue));
    if (!array) return NIL_VALUE;
    array->hdr.type = HEAP_ARRAY;
    array->hdr.size = (uint32_t)(sizeof(RuntimeArray) + len * sizeof(RuntimeValue));
    array->len = len;
    array->cap = len;
    array->items = runtime_array_inline_items(array);
    for (uint64_t i = 0; i < len; i++) array->items[i] = NIL_VALUE;
    return ENCODE_PTR(array);
}

RuntimeValue rt_tuple_get(RuntimeValue tuple, RuntimeValue index)
{
    return rt_array_get(tuple, index);
}

RuntimeValue rt_tuple_set(RuntimeValue tuple, RuntimeValue index, RuntimeValue item)
{
    return rt_array_set(tuple, index, item);
}

RuntimeValue rt_string_replace(RuntimeValue str, RuntimeValue old_val, RuntimeValue new_val)
{
    if (!IS_HEAP(str) || !IS_HEAP(old_val) || !IS_HEAP(new_val)) return NIL_VALUE;
    RuntimeString *s = (RuntimeString *)DECODE_PTR(str);
    RuntimeString *o = (RuntimeString *)DECODE_PTR(old_val);
    RuntimeString *n = (RuntimeString *)DECODE_PTR(new_val);
    if (!s || !o || !n || s->hdr.type != HEAP_STRING || o->hdr.type != HEAP_STRING || n->hdr.type != HEAP_STRING) {
        return NIL_VALUE;
    }
    if (o->len == 0 || o->len > s->len) return str;

    for (uint32_t i = 0; i <= s->len - o->len; i++) {
        uint32_t j = 0;
        while (j < o->len && s->data[i + j] == o->data[j]) j++;
        if (j != o->len) continue;

        uint32_t out_len = s->len - o->len + n->len;
        RuntimeString *out = (RuntimeString *)rv_alloc(sizeof(RuntimeString) + out_len + 1U);
        if (!out) return str;
        out->hdr.type = HEAP_STRING;
        out->hdr.size = (uint32_t)(sizeof(RuntimeString) + out_len + 1U);
        out->len = out_len;
        for (uint32_t k = 0; k < i; k++) out->data[k] = s->data[k];
        for (uint32_t k = 0; k < n->len; k++) out->data[i + k] = n->data[k];
        for (uint32_t k = i + o->len; k < s->len; k++) out->data[i + n->len + (k - i - o->len)] = s->data[k];
        out->data[out_len] = 0;
        return ENCODE_PTR(out);
    }
    return str;
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

uint32_t rt_mmio_read_u32(uint64_t addr)
{
    return *(volatile uint32_t *)(uintptr_t)addr;
}

uint64_t rt_mmio_read_u64(uint64_t addr)
{
    return *(volatile uint64_t *)(uintptr_t)addr;
}

__attribute__((naked)) void rt_mmio_write_u8(uint64_t addr, uint8_t value)
{
    __asm__ volatile(
        "sb a1, 0(a0)\n"
        "ret\n"
    );
}

__attribute__((naked)) void rt_mmio_write_u16(uint64_t addr, uint16_t value)
{
    __asm__ volatile(
        "sh a1, 0(a0)\n"
        "ret\n"
    );
}

__attribute__((naked)) void rt_mmio_write_u32(uint64_t addr, uint32_t value)
{
    __asm__ volatile(
        "sw a1, 0(a0)\n"
        "ret\n"
    );
}

__attribute__((naked)) void rt_mmio_write_u64(uint64_t addr, uint64_t value)
{
    __asm__ volatile(
        "sd a1, 0(a0)\n"
        "ret\n"
    );
}

__attribute__((naked)) void proof_store_u64(uint64_t slot, uint64_t value)
{
    __asm__ volatile(
        "slli a0, a0, 3\n"
        "lui t0, 0x80ff1\n"
        "slli t0, t0, 32\n"
        "srli t0, t0, 32\n"
        "add a0, a0, t0\n"
        "sd a1, 0(a0)\n"
        "ret\n"
    );
}

__attribute__((naked)) void proof_store_bool(uint64_t slot, uint64_t value)
{
    __asm__ volatile(
        "snez a1, a1\n"
        "slli a0, a0, 3\n"
        "lui t0, 0x80ff1\n"
        "slli t0, t0, 32\n"
        "srli t0, t0, 32\n"
        "add a0, a0, t0\n"
        "sd a1, 0(a0)\n"
        "ret\n"
    );
}

__attribute__((naked)) void proof_emit_boot_snapshot_defaults(uint64_t hart_id, uint64_t dtb_addr)
{
    __asm__ volatile(
        "lui t0, 0x80ff1\n"
        "slli t0, t0, 32\n"
        "srli t0, t0, 32\n"
        "slli a0, a0, 32\n"
        "srli a0, a0, 32\n"
        "slli a1, a1, 32\n"
        "srli a1, a1, 32\n"
        "sd a0, 16(t0)\n"
        "sd a1, 24(t0)\n"
        "li t1, 1\n"
        "sd t1, 32(t0)\n"
        "lui t1, 0x80000\n"
        "slli t1, t1, 32\n"
        "srli t1, t1, 32\n"
        "mv t2, t1\n"
        "sd t1, 40(t0)\n"
        "lui t1, 0x8000\n"
        "sd t1, 48(t0)\n"
        "lui t1, 0x10000\n"
        "sd t1, 56(t0)\n"
        "li t1, 1\n"
        "sd t1, 64(t0)\n"
        "li t1, 3\n"
        "sd t1, 72(t0)\n"
        "sd t2, 80(t0)\n"
        "lui t1, 0x200\n"
        "sd t1, 88(t0)\n"
        "li t1, 2\n"
        "sd t1, 96(t0)\n"
        "lui t1, 0x80200\n"
        "slli t1, t1, 32\n"
        "srli t1, t1, 32\n"
        "sd t1, 104(t0)\n"
        "lui t1, 0x200\n"
        "sd t1, 112(t0)\n"
        "li t1, 8\n"
        "sd t1, 120(t0)\n"
        "lui t1, 0x80400\n"
        "slli t1, t1, 32\n"
        "srli t1, t1, 32\n"
        "sd t1, 128(t0)\n"
        "lui t1, 0x7c00\n"
        "sd t1, 136(t0)\n"
        "li t1, 1\n"
        "sd t1, 144(t0)\n"
        "ret\n"
    );
}

RuntimeValue rt_len(RuntimeValue value)
{
    if (!IS_HEAP(value)) return 0;
    HeapHeader *hdr = (HeapHeader *)DECODE_PTR(value);
    if (!hdr) return 0;
    if (hdr->type == HEAP_STRING) return (RuntimeValue)((RuntimeString *)hdr)->len;
    if (hdr->type == HEAP_ARRAY) return (RuntimeValue)((RuntimeArray *)hdr)->len;
    if (hdr->type == HEAP_DICT) return (RuntimeValue)simpleos_dict_count(value);
    return 0;
}

RuntimeValue rt_string_char_at(RuntimeValue str, RuntimeValue idx);

RuntimeValue rt_index_get(RuntimeValue value, RuntimeValue index)
{
    if (!IS_HEAP(value)) return NIL_VALUE;
    HeapHeader *hdr0 = (HeapHeader *)DECODE_PTR(value);
    if (hdr0 && hdr0->type == HEAP_DICT) return simpleos_dict_lookup(value, index);
    if (!IS_INT(index)) return NIL_VALUE;
    HeapHeader *hdr = hdr0;
    if (!hdr) return NIL_VALUE;
    if (hdr->type == HEAP_ARRAY) return rt_array_get(value, (RuntimeValue)DECODE_INT(index));
    if (hdr->type == HEAP_STRING) return rt_string_char_at(value, (RuntimeValue)DECODE_INT(index));
    return NIL_VALUE;
}

/* The dict arms MUST live in this TU's copies of rt_index_set / rt_index_get
 * / rt_len, not only in the other runtime TUs: which duplicate definition
 * wins the --allow-multiple-definition link is a per-closure lottery, and on
 * the 2026-11-06 closure THIS copy won rt_index_set with the pre-fix body
 * (every dict write in-guest silently dropped; module.functions stayed
 * EMPTY; desugar_module then nil-faulted reading func.is_async). Mirrored
 * verbatim from baremetal_stubs.c, whose comment documents the same
 * incident class. simpleos_dict_* are not duplicated; declared with the
 * other HEAP_* defines below. */
RuntimeValue rt_index_set(RuntimeValue value, RuntimeValue index, RuntimeValue item)
{
    if (IS_HEAP(value)) {
        HeapHeader *hdr = (HeapHeader *)DECODE_PTR(value);
        if (hdr && hdr->type == HEAP_DICT)
            return (RuntimeValue)simpleos_dict_store(value, index, item);
    }
    if (!IS_INT(index)) return 0;
    return rt_array_set(value, (RuntimeValue)DECODE_INT(index), item);
}

RuntimeValue rt_enum_new(RuntimeValue enum_id, RuntimeValue discriminant, RuntimeValue payload)
{
    RuntimeEnum *enum_value = (RuntimeEnum *)rv_alloc(sizeof(RuntimeEnum));
    if (!enum_value) return NIL_VALUE;
    enum_value->hdr.type = HEAP_ENUM;
    enum_value->hdr.size = (uint32_t)sizeof(RuntimeEnum);
    enum_value->enum_id = (uint32_t)(int32_t)enum_id;
    enum_value->discriminant = (uint32_t)(int32_t)discriminant;
    enum_value->payload = payload;
    return ENCODE_PTR(enum_value);
}

RuntimeValue rt_enum_payload(RuntimeValue value)
{
    if (!IS_HEAP(value)) return value;
    RuntimeEnum *enum_value = (RuntimeEnum *)DECODE_PTR(value);
    return (!enum_value || enum_value->hdr.type != HEAP_ENUM) ? value : enum_value->payload;
}

RuntimeValue rt_enum_check_discriminant(RuntimeValue value, RuntimeValue expected)
{
    if (!IS_HEAP(value)) return 0;
    RuntimeEnum *enum_value = (RuntimeEnum *)DECODE_PTR(value);
    if (!enum_value || enum_value->hdr.type != HEAP_ENUM) return 0;
    return enum_value->discriminant == (uint32_t)(int32_t)expected ? 1 : 0;
}

RuntimeValue str_byte_at_impl(RuntimeValue string_value, RuntimeValue index) __asm__("str.byte_at");
RuntimeValue str_byte_at_impl(RuntimeValue string_value, RuntimeValue index)
{
    if (!IS_HEAP(string_value)) return 0;
    RuntimeString *string = (RuntimeString *)DECODE_PTR(string_value);
    int64_t i = (int64_t)index;
    if (!string || string->hdr.type != HEAP_STRING || i < 0 || (uint32_t)i >= string->len) return 0;
    return (RuntimeValue)(uint8_t)string->data[i];
}

RuntimeValue rt_native_eq(RuntimeValue a, RuntimeValue b)
{
    return a == b ? 1 : 0;
}

RuntimeValue rt_native_neq(RuntimeValue a, RuntimeValue b)
{
    return a == b ? 0 : 1;
}
