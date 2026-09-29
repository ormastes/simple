/* Minimal ring-3 user-side Simple runtime for SimpleOS x86_64.
 * Provides exactly the rt_* surface a hello-world .spl needs: a bump heap,
 * the string-literal ctor, tagged-value print, and exit(2).
 * Value ABI is copied verbatim from the kernel's baremetal_stubs.c so the
 * same codegen contract holds on both sides of the ring boundary. */
#include <stdint.h>
#include <stddef.h>

typedef int64_t RuntimeValue;
#define TAG_MASK    7
#define TAG_INT     0
#define TAG_HEAP    1
#define TAG_SPECIAL 3
#define IS_INT(v)   (((v) & TAG_MASK) == TAG_INT)
#define IS_HEAP(v)  (((v) & TAG_MASK) == TAG_HEAP)
#define DECODE_INT(v)  ((int64_t)(v) >> 3)
#define DECODE_PTR(v)  ((void *)((uintptr_t)(v) & ~(uintptr_t)TAG_MASK))
#define ENCODE_INT(v)  ((RuntimeValue)(((uint64_t)(int64_t)(v) << 3) | TAG_INT))
#define NIL_VALUE      ((RuntimeValue)TAG_SPECIAL)

typedef struct { uint8_t type; uint8_t gc_flags; uint16_t reserved; uint32_t size; } HeapHeader;
typedef struct { HeapHeader hdr; uint64_t len; char data[]; } RuntimeString;
#define HEAP_STRING 1

/* IOPL=3 is set in the ring-3 task rflags (0x3002), so CPL(3) <= IOPL(3) and
 * `out` to the 16550 at 0x3f8 is legal from userland. This is the same
 * mechanism the existing FDR ring-3 proof relies on. */
static void _putc(char c) { __asm__ __volatile__("outb %0,%1" :: "a"((uint8_t)c), "Nd"((uint16_t)0x3f8)); }
static void _puts(const char *s) { while (*s) _putc(*s++); }

static uint8_t  g_heap[1 << 20];
static uint64_t g_heap_off = 0;
static void *_alloc(uint64_t n) {
    n = (n + 15) & ~(uint64_t)15;
    if (g_heap_off + n > sizeof(g_heap)) return 0;
    void *p = &g_heap[g_heap_off];
    g_heap_off += n;
    return p;
}

RuntimeValue rt_string_new(RuntimeValue data, RuntimeValue len_val) {
    const char *src = (const char *)(uintptr_t)(IS_INT(data) ? (uint64_t)DECODE_INT(data) : (uint64_t)(uintptr_t)DECODE_PTR(data));
    uint64_t len = IS_INT(len_val) ? (uint64_t)DECODE_INT(len_val) : (uint64_t)len_val;
    RuntimeString *s = (RuntimeString *)_alloc(sizeof(RuntimeString) + len + 1);
    if (!s) return NIL_VALUE;
    s->hdr.type = HEAP_STRING; s->hdr.gc_flags = 0; s->hdr.reserved = 0;
    s->hdr.size = (uint32_t)(sizeof(RuntimeString) + len + 1);
    s->len = len;
    for (uint64_t i = 0; i < len; i++) s->data[i] = src[i];
    s->data[len] = 0;
    return (RuntimeValue)((uint64_t)(uintptr_t)s | TAG_HEAP);
}
RuntimeValue rt_string_new_literal(RuntimeValue d, RuntimeValue l) { return rt_string_new(d, l); }

RuntimeValue rt_print(RuntimeValue val) {
    if (IS_HEAP(val)) {
        HeapHeader *h = (HeapHeader *)DECODE_PTR(val);
        if (h && h->type == HEAP_STRING) {
            RuntimeString *s = (RuntimeString *)h;
            for (uint64_t i = 0; i < s->len; i++) _putc(s->data[i]);
        } else { _puts("<object>"); }
    } else if (IS_INT(val)) {
        int64_t n = DECODE_INT(val); char b[24]; int i = 0;
        if (n < 0) { _putc('-'); n = -n; }
        if (n == 0) b[i++] = '0';
        while (n > 0) { b[i++] = (char)('0' + (n % 10)); n /= 10; }
        while (i > 0) _putc(b[--i]);
    } else { _puts("nil"); }
    return NIL_VALUE;
}

RuntimeValue serial_println(RuntimeValue v) { rt_print(v); _putc('\r'); _putc('\n'); return NIL_VALUE; }

/* exit(2): SimpleOS's ring-3 exit longjmps the kernel back through its
 * enter-user savepoint. No isa-debug-exit, no port 0xf4. */
void rt_user_exit(RuntimeValue code) {
    int64_t c = IS_INT(code) ? DECODE_INT(code) : 0;
    __asm__ __volatile__("mov $0,%%rax\n\tsyscall" :: "D"(c) : "rax", "rcx", "r11");
    for (;;) __asm__ __volatile__("hlt");
}
