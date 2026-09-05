/* Selfcheck: freestanding/baremetal text ORDERING (`<`/`>`/sort) against a
 * RAW string literal -- the sibling gap of
 * rt_native_eq_heap_vs_raw_empty_literal_selfcheck.c, for `rt_text_cmp_any` /
 * `rt_native_cmp` instead of `rt_native_eq`.
 *
 * Follow-up flagged by commit 43aed2b9df8 (see its bug doc), which fixed
 * freestanding text EQUALITY against raw literals but explicitly left this
 * ORDERING counterpart open: `rt_text_cmp_any` (x86_64/aarch64) and the
 * inlined string-ordering branch of `rt_native_cmp` (arm64) have the
 * identical both-sides-heap requirement -- a heap string compared against a
 * raw untagged char* literal (e.g. `""` / `.trim()` results vs a bare
 * literal) fell through to a raw pointer/word compare, so ordering against a
 * literal reflected malloc address, not content.
 *
 * Bug doc: doc/08_tracking/bug/freestanding_text_ordering_raw_literal_2026-08-11.md
 *
 * Build/run (hosted, no QEMU needed):
 *   cc -O1 -o /tmp/cmpsc src/runtime/test/rt_text_cmp_any_heap_vs_raw_selfcheck.c && /tmp/cmpsc
 * Exit 0 = PASS, exit 2 = the defect did not reproduce (vacuous selfcheck).
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

/* ---- BEFORE: the shipped freestanding rt_text_cmp_any (both operands must
 * be heap; otherwise falls through to a raw pointer/word compare). */
static RuntimeValue rt_text_cmp_any_before(RuntimeValue left, RuntimeValue right)
{
    if (!IS_HEAP(left) || !IS_HEAP(right))
        return (RuntimeValue)(left == right ? 0 : (left < right ? -1 : 1));
    RuntimeString *a = (RuntimeString *)DECODE_PTR(left);
    RuntimeString *b = (RuntimeString *)DECODE_PTR(right);
    if (!a || !b) return (RuntimeValue)(a == b ? 0 : (a ? 1 : -1));
    uint32_t n = a->len < b->len ? a->len : b->len;
    for (uint32_t i = 0; i < n; i++) {
        unsigned char ca = (unsigned char)a->data[i];
        unsigned char cb = (unsigned char)b->data[i];
        if (ca != cb) return (RuntimeValue)(ca < cb ? -1 : 1);
    }
    if (a->len == b->len) return (RuntimeValue)0;
    return (RuntimeValue)(a->len < b->len ? -1 : 1);
}

/* ---- AFTER: adds the heap-string vs RAW-char* ordering comparison, with the
 * same safety rules as rt_text_eq_heap_vs_raw (floor + non-heap-tag check +
 * scan bounded by the heap string's own length, NUL required at that
 * offset). */
static int rt_text_cmp_heap_vs_raw(RuntimeString *s, RuntimeValue raw, int *ok)
{
    *ok = 0;
    if ((uint64_t)raw < 0x10000ULL) return 0;               /* nil / bool / small int */
    if (((uint64_t)raw & TAG_MASK) == TAG_HEAP) return 0;   /* not a raw pointer */
    const char *p = (const char *)(uintptr_t)raw;
    for (uint32_t i = 0; i < s->len; i++) {
        unsigned char sc = (unsigned char)s->data[i];
        unsigned char pc = (unsigned char)p[i];
        if (pc == '\0') { *ok = 1; return 1; }               /* raw ends first -> s greater */
        if (sc != pc) { *ok = 1; return sc < pc ? -1 : 1; }
    }
    *ok = 1;
    return p[s->len] == '\0' ? 0 : -1;                       /* equal length, or raw has more */
}

static RuntimeValue rt_text_cmp_any_after(RuntimeValue left, RuntimeValue right)
{
    if (IS_HEAP(left) && IS_HEAP(right)) {
        RuntimeString *a = (RuntimeString *)DECODE_PTR(left);
        RuntimeString *b = (RuntimeString *)DECODE_PTR(right);
        if (!a || !b) return (RuntimeValue)(a == b ? 0 : (a ? 1 : -1));
        uint32_t n = a->len < b->len ? a->len : b->len;
        for (uint32_t i = 0; i < n; i++) {
            unsigned char ca = (unsigned char)a->data[i];
            unsigned char cb = (unsigned char)b->data[i];
            if (ca != cb) return (RuntimeValue)(ca < cb ? -1 : 1);
        }
        if (a->len == b->len) return (RuntimeValue)0;
        return (RuntimeValue)(a->len < b->len ? -1 : 1);
    }
    if (IS_HEAP(left)) {
        HeapHeader *hl = (HeapHeader *)DECODE_PTR(left);
        if (hl && hl->type == HEAP_STRING) {
            int ok;
            int r = rt_text_cmp_heap_vs_raw((RuntimeString *)hl, right, &ok);
            if (ok) return (RuntimeValue)r;
        }
    }
    if (IS_HEAP(right)) {
        HeapHeader *hr = (HeapHeader *)DECODE_PTR(right);
        if (hr && hr->type == HEAP_STRING) {
            int ok;
            int r = rt_text_cmp_heap_vs_raw((RuntimeString *)hr, left, &ok);
            if (ok) return (RuntimeValue)(-r);
        }
    }
    return (RuntimeValue)(left == right ? 0 : (left < right ? -1 : 1));
}

static int failures = 0;
static int checked = 0;
static void expect(const char *what, RuntimeValue got, RuntimeValue want)
{
    checked++;
    if (got != want) {
        failures++;
        printf("  FAIL %-56s got=%lld want=%lld\n", what, (long long)got, (long long)want);
    } else {
        printf("  ok   %-56s = %lld\n", what, (long long)got);
    }
}

int main(void)
{
    /* Raw, untagged string-literal pointers, as emit_bootstrap_str_const
     * emits (word-aligned globals in the real compiler, so align these test
     * fixtures the same way -- an unaligned char[] can otherwise coincide
     * with TAG_HEAP's low bits purely by linker luck and make the AFTER
     * assertions flaky, independent of the fix's own correctness). */
    static const char raw_bar[] __attribute__((aligned(8))) = "bar";
    static const char raw_foo[] __attribute__((aligned(8))) = "foo";
    static const char raw_empty[] __attribute__((aligned(8))) = "";
    RuntimeValue L_bar   = (RuntimeValue)(uintptr_t)raw_bar;
    RuntimeValue L_foo   = (RuntimeValue)(uintptr_t)raw_foo;
    RuntimeValue L_empty = (RuntimeValue)(uintptr_t)raw_empty;

    /* Heap strings, as .trim()/.substring() produce on this lane. Force the
     * heap allocation ABOVE the literals' addresses (typical: .rodata is
     * lower than the heap on these lanes) so the BEFORE pointer-compare
     * reliably mis-orders rather than accidentally agreeing. */
    RuntimeValue H_foo = mk_heap_str("foo");
    RuntimeValue H_bar = mk_heap_str("bar");
    RuntimeValue H_empty = mk_heap_str("");

    printf("== BEFORE (shipped freestanding rt_text_cmp_any) ==\n");
    int before_bug = 0;
    /* "bar" vs "bar": content-equal, but a pointer compare between a heap
     * copy and the raw literal is virtually never 0 (different addresses),
     * so BEFORE almost always reports non-equal for equal content. */
    if (rt_text_cmp_any_before(H_bar, L_bar) == 0
        && rt_text_cmp_any_before(H_foo, L_foo) == 0
        && rt_text_cmp_any_before(H_empty, L_empty) == 0) {
        /* Extremely unlikely (would require malloc to return the exact
         * literal address); treat as non-reproduction rather than silently
         * passing. */
    } else {
        printf("  REPRODUCED: heap \"bar\"/\"foo\"/\"\" vs raw same-content literal -> nonzero (pointer compare, not content)\n");
        before_bug = 1;
    }
    if (!before_bug) {
        printf("  ERROR - the defect did not reproduce; selfcheck is vacuous\n");
        return 2;
    }

    printf("== AFTER (heap-vs-raw content ordering) ==\n");
    /* The incident shape: equal content across heap/raw must compare equal. */
    expect("cmp(heap \"bar\", raw \"bar\")   == 0", rt_text_cmp_any_after(H_bar, L_bar), 0);
    expect("cmp(raw \"bar\",  heap \"bar\")  == 0", rt_text_cmp_any_after(L_bar, H_bar), 0);
    expect("cmp(heap \"\",    raw \"\")      == 0", rt_text_cmp_any_after(H_empty, L_empty), 0);

    /* Negative controls - non-equal ordering must still be correct. */
    expect("cmp(heap \"bar\", raw \"foo\")   <  0", rt_text_cmp_any_after(H_bar, L_foo) < 0 ? -1 : 1, -1);
    expect("cmp(heap \"foo\", raw \"bar\")   >  0", rt_text_cmp_any_after(H_foo, L_bar) > 0 ? 1 : -1, 1);
    expect("cmp(heap \"foo\", raw \"\")      >  0", rt_text_cmp_any_after(H_foo, L_empty) > 0 ? 1 : -1, 1);
    expect("cmp(heap \"\",    raw \"foo\")   <  0", rt_text_cmp_any_after(H_empty, L_foo) < 0 ? -1 : 1, -1);

    /* Heap/heap path must be untouched. */
    expect("cmp(heap \"bar\", heap \"foo\")  <  0", rt_text_cmp_any_after(H_bar, mk_heap_str("foo")) < 0 ? -1 : 1, -1);
    expect("cmp(heap \"foo\", heap \"foo\")  == 0", rt_text_cmp_any_after(H_foo, mk_heap_str("foo")), 0);

    /* Small non-pointer words must never be dereferenced (bug 2026-07-23). */
    expect("cmp(heap \"foo\", nil) does not crash, != 0", rt_text_cmp_any_after(H_foo, NIL_VALUE) != 0 ? 1 : 0, 1);
    expect("cmp(heap \"\",    small int 7) does not crash", rt_text_cmp_any_after(H_empty, (RuntimeValue)7) != 0 ? 1 : 0, 1);
    expect("cmp(heap \"foo\", small int 0) does not crash", rt_text_cmp_any_after(H_foo, (RuntimeValue)0) != 0 ? 1 : 0, 1);

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
