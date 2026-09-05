/* Selfcheck: freestanding/baremetal `text == ""` / `!= ""` against a RAW
 * string literal.
 *
 * Incident (2026-08-11, x86_64 OVMF real-firmware SimpleOS boot):
 *   doc/08_tracking/bug/native_text_equality_against_empty_literal_unreliable_after_trim_lower_2026-08-11.md
 *
 * The freestanding `rt_native_eq` (examples/09_embedded/simple_os/arch/<arch>/
 * boot/baremetal_stubs.c) content-compares two texts ONLY when BOTH operands
 * are IS_HEAP; anything else falls through to `return 0` (NOT EQUAL).
 *
 * On this lane a `.trim()` / `.lower()` result is ALWAYS a freshly malloc'd
 * HEAP string (rt_string_slice / rt_string_to_lower), while a bare `""`
 * literal is emitted as a RAW, untagged `[N x i8]` global pointer
 * (emit_bootstrap_str_const). So `x != ""` compared a heap handle against a
 * raw pointer, took the fall-through, and answered "not equal"
 * UNCONDITIONALLY -- even when x was genuinely empty. Interpolation `{x}`
 * meanwhile decoded the heap string honestly and printed nothing, producing
 * the tell-tale double space in
 *   [backend-resolve] override  rejected: Unknown backend:
 * and `.len() == 0` kept working (it reads the heap header directly, no
 * literal involved).
 *
 * This is bug #148 (hosted, fixed by introducing rt_text_eq_any's tagged-or-raw
 * normalization in runtime_native.c) never having been ported to the
 * freestanding lane: that lane has NO rt_text_eq_any at all. It did get the
 * ORDERING counterpart (rt_text_cmp_any), which is what makes the gap so easy
 * to miss.
 *
 * Build/run (hosted, no QEMU needed):
 *   cc -O1 -o /tmp/eqsc src/runtime/test/rt_native_eq_heap_vs_raw_empty_literal_selfcheck.c && /tmp/eqsc
 * Exit 0 = PASS.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef int64_t RuntimeValue;

#define TAG_MASK    0x7ULL
#define TAG_HEAP    0x1ULL
#define TAG_SPECIAL 0x3ULL
#define ENCODE_PTR(p)  ((RuntimeValue)((uint64_t)(uintptr_t)(p) | TAG_HEAP))
#define DECODE_PTR(v)  ((void*)((uint64_t)(v) & ~TAG_MASK))
#define IS_HEAP(v)     (((uint64_t)(v) & TAG_MASK) == TAG_HEAP)
#define NIL_VALUE      ((RuntimeValue)TAG_SPECIAL)
#define HEAP_STRING  1

typedef struct { uint32_t type; uint32_t size; } HeapHeader;
typedef struct { HeapHeader hdr; uint32_t len; char data[]; } RuntimeString;

static RuntimeValue mk_heap_str(const char *s) {
    uint32_t n = (uint32_t)strlen(s);
    RuntimeString *r = (RuntimeString *)malloc(sizeof(RuntimeString) + n + 1);
    r->hdr.type = HEAP_STRING;
    r->hdr.size = (uint32_t)(sizeof(RuntimeString) + n + 1);
    r->len = n;
    memcpy(r->data, s, n);
    r->data[n] = '\0';
    return ENCODE_PTR(r);
}

/* ---- BEFORE: the shipped freestanding predicate (both operands must be heap) */
static RuntimeValue rt_native_eq_before(RuntimeValue a, RuntimeValue b)
{
    if (a == b) return 1;
    if (IS_HEAP(a) && IS_HEAP(b)) {
        HeapHeader *ha = (HeapHeader *)DECODE_PTR(a);
        HeapHeader *hb = (HeapHeader *)DECODE_PTR(b);
        if (ha && hb && ha->type == HEAP_STRING && hb->type == HEAP_STRING) {
            RuntimeString *sa = (RuntimeString *)ha;
            RuntimeString *sb = (RuntimeString *)hb;
            if (sa->len != sb->len) return 0;
            for (uint32_t i = 0; i < sa->len; i++)
                if (sa->data[i] != sb->data[i]) return 0;
            return 1;
        }
    }
    return 0;
}

/* ---- AFTER: adds the heap-string vs RAW-char* content comparison.
 *
 * Deliberately conservative, because on this lane TAG_INT is 0x0 and a raw
 * pointer is therefore INDISTINGUISHABLE from a tagged small integer by tag
 * bits alone (that ambiguity already caused
 * doc/08_tracking/bug/native_text_eq_any_untagged_smallint_deref_2026-07-23.md,
 * an untagged-smallint dereference). Two guards keep this safe:
 *   1. the raw path is entered ONLY when the OTHER operand is already a proven
 *      HEAP_STRING -- so we only ever reinterpret a word as char* in a context
 *      that is known to be a TEXT comparison, and
 *   2. a plausibility floor rejects small words (nil, bools, small ints), the
 *      same 0x10000 heuristic the hosted rt_interp_cstr already uses.
 * The scan is bounded by the heap string's own length and demands a NUL
 * exactly at that offset, so it never runs past the literal.
 */
static int rt_text_eq_heap_vs_raw(RuntimeString *s, RuntimeValue raw)
{
    if ((uint64_t)raw < 0x10000ULL) return 0;      /* nil / bool / small int */
    if (((uint64_t)raw & TAG_MASK) == TAG_HEAP) return 0; /* not raw */
    const char *p = (const char *)(uintptr_t)raw;
    for (uint32_t i = 0; i < s->len; i++) {
        if (p[i] == '\0' || p[i] != s->data[i]) return 0;
    }
    return p[s->len] == '\0';
}

static RuntimeValue rt_native_eq_after(RuntimeValue a, RuntimeValue b)
{
    if (a == b) return 1;
    if (IS_HEAP(a) && IS_HEAP(b)) {
        HeapHeader *ha = (HeapHeader *)DECODE_PTR(a);
        HeapHeader *hb = (HeapHeader *)DECODE_PTR(b);
        if (ha && hb && ha->type == HEAP_STRING && hb->type == HEAP_STRING) {
            RuntimeString *sa = (RuntimeString *)ha;
            RuntimeString *sb = (RuntimeString *)hb;
            if (sa->len != sb->len) return 0;
            for (uint32_t i = 0; i < sa->len; i++)
                if (sa->data[i] != sb->data[i]) return 0;
            return 1;
        }
        return 0;
    }
    /* Mixed heap-string vs raw char* literal: compare by CONTENT. */
    if (IS_HEAP(a)) {
        HeapHeader *ha = (HeapHeader *)DECODE_PTR(a);
        if (ha && ha->type == HEAP_STRING)
            return rt_text_eq_heap_vs_raw((RuntimeString *)ha, b) ? 1 : 0;
    }
    if (IS_HEAP(b)) {
        HeapHeader *hb = (HeapHeader *)DECODE_PTR(b);
        if (hb && hb->type == HEAP_STRING)
            return rt_text_eq_heap_vs_raw((RuntimeString *)hb, a) ? 1 : 0;
    }
    return 0;
}

static int failures = 0;
static int checked = 0;
static void expect(const char *what, RuntimeValue got, RuntimeValue want)
{
    checked++;
    if (got != want) {
        failures++;
        printf("  FAIL %-52s got=%lld want=%lld\n", what, (long long)got, (long long)want);
    } else {
        printf("  ok   %-52s = %lld\n", what, (long long)got);
    }
}

int main(void)
{
    /* Raw, untagged string-literal pointers, as emit_bootstrap_str_const emits. */
    static const char raw_empty[] = "";
    static const char raw_vulkan[] = "vulkan";
    RuntimeValue L_empty  = (RuntimeValue)(uintptr_t)raw_empty;
    RuntimeValue L_vulkan = (RuntimeValue)(uintptr_t)raw_vulkan;

    /* Heap strings, as .trim()/.lower() produce on this lane. */
    RuntimeValue H_empty  = mk_heap_str("");
    RuntimeValue H_vulkan = mk_heap_str("vulkan");
    RuntimeValue H_other  = mk_heap_str("metal");

    printf("== BEFORE (shipped freestanding rt_native_eq) ==\n");
    int before_bug = 0;
    if (rt_native_eq_before(H_empty, L_empty) != 1) {
        printf("  REPRODUCED: heap \"\" == raw \"\" -> NOT EQUAL (so `x != \"\"` is TRUE)\n");
        before_bug = 1;
    }
    if (!before_bug) {
        printf("  ERROR - the defect did not reproduce; selfcheck is vacuous\n");
        return 2;
    }

    printf("== AFTER (heap-vs-raw content comparison) ==\n");
    /* The incident shape. */
    expect("heap \"\"     == raw \"\"      (empty trim/lower result)", rt_native_eq_after(H_empty, L_empty), 1);
    expect("raw  \"\"     == heap \"\"     (operands swapped)",        rt_native_eq_after(L_empty, H_empty), 1);

    /* Negative controls - non-empty text must still compare correctly. */
    expect("heap \"vulkan\" == raw \"vulkan\"",                       rt_native_eq_after(H_vulkan, L_vulkan), 1);
    expect("heap \"vulkan\" == raw \"\"          (must be NOT equal)", rt_native_eq_after(H_vulkan, L_empty), 0);
    expect("heap \"\"       == raw \"vulkan\"    (must be NOT equal)", rt_native_eq_after(H_empty, L_vulkan), 0);
    expect("heap \"metal\"  == raw \"vulkan\"    (must be NOT equal)", rt_native_eq_after(H_other, L_vulkan), 0);

    /* Heap/heap path must be untouched. */
    expect("heap \"vulkan\" == heap \"vulkan\"",                      rt_native_eq_after(H_vulkan, mk_heap_str("vulkan")), 1);
    expect("heap \"vulkan\" == heap \"metal\"   (must be NOT equal)", rt_native_eq_after(H_vulkan, H_other), 0);
    expect("heap \"\"       == heap \"\"",                            rt_native_eq_after(H_empty, mk_heap_str("")), 1);

    /* Small non-pointer words must never be dereferenced (bug 2026-07-23). */
    expect("heap \"\"       == nil            (must be NOT equal)",   rt_native_eq_after(H_empty, NIL_VALUE), 0);
    expect("heap \"vulkan\" == small int 7    (must be NOT equal)",   rt_native_eq_after(H_vulkan, (RuntimeValue)7), 0);
    expect("heap \"\"       == small int 0    (must be NOT equal)",   rt_native_eq_after(H_empty, (RuntimeValue)0), 0);

    printf("\n");
    if (failures) {
        printf("FAIL - %d of %d assertion(s) failed\n", failures, checked);
        return 1;
    }
    if (checked == 0) {
        printf("ERROR - nothing was checked\n");
        return 2;
    }
    printf("PASS - %d assertion(s) checked, defect reproduced before / fixed after\n", checked);
    return 0;
}
