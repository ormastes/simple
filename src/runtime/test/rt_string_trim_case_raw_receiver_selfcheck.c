/* Selfcheck: hosted rt_string_trim / rt_string_trim_start / rt_string_trim_end
 * / rt_string_to_lower / rt_string_to_upper DEGRADE on a raw, untagged char*
 * receiver -- trim* silently passed the raw pointer straight through
 * unchanged (not trimmed), and to_lower/to_upper silently returned nil.
 *
 * Follow-up flagged by commit 43aed2b9df8 (see its bug doc). Reachable
 * wherever MIR's ensure_tagged_str normalization is skipped (gated on
 * `resolution_is_unresolved` in
 * src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl around the
 * "trim"/"strip"/"lower"/"to_lower"/"to_upper" dispatch) -- a statically
 * resolved call can hand these functions a raw string-literal pointer
 * instead of a tagged heap string.
 *
 * Mirrors src/runtime/runtime_native.c's real rt_core_as_string /
 * rt_string_trim / rt_string_ascii_case shape (BEFORE = shipped defect,
 * AFTER = the rt_string_promote_raw_receiver fix), same as the
 * rt_native_eq_heap_vs_raw_empty_literal_selfcheck.c precedent, so this
 * selfcheck always demonstrates the defect regardless of the current state
 * of the production file (it does not link against it).
 *
 * Bug doc: doc/08_tracking/bug/hosted_string_trim_case_raw_receiver_degrades_2026-08-11.md
 *
 * Build/run (hosted, no QEMU needed):
 *   cc -O1 -o /tmp/trimsc src/runtime/test/rt_string_trim_case_raw_receiver_selfcheck.c && /tmp/trimsc
 * Exit 0 = PASS, exit 2 = the defect did not reproduce (vacuous selfcheck).
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef int64_t RtValue;

#define TAG_MASK    0x7ULL
#define TAG_HEAP    0x1ULL
#define TAG_SPECIAL 0x3ULL
#define NIL_VALUE   ((RtValue)TAG_SPECIAL)
#define HEAP_STRING 1

typedef struct { uint32_t kind; uint32_t len; char data[]; } RtString;

static RtValue mk_heap_str(const char *s) {
    uint32_t n = (uint32_t)strlen(s);
    RtString *r = (RtString *)malloc(sizeof(RtString) + n + 1);
    r->kind = HEAP_STRING;
    r->len = n;
    memcpy(r->data, s, n);
    r->data[n] = '\0';
    return (RtValue)(((uint64_t)(uintptr_t)r) | TAG_HEAP);
}

/* rt_core_as_string() equivalent: only a tagged, registered heap string
 * decodes; a raw untagged char* (or nil/small int) returns NULL. */
static RtString *as_string(RtValue v) {
    uintptr_t raw = (uintptr_t)v;
    if (raw < 4096) return NULL;
    if ((raw & TAG_MASK) != TAG_HEAP) return NULL;
    return (RtString *)(raw & ~TAG_MASK);
}

static RtValue rt_string_new_v(const char *bytes, uint64_t len) {
    RtString *r = (RtString *)malloc(sizeof(RtString) + len + 1);
    r->kind = HEAP_STRING;
    r->len = (uint32_t)len;
    memcpy(r->data, bytes, len);
    r->data[len] = '\0';
    return (RtValue)(((uint64_t)(uintptr_t)r) | TAG_HEAP);
}

/* ---- BEFORE: the shipped predicate shape (rt_core_as_string() == NULL on a
 * raw receiver => passthrough / nil). */
static RtValue rt_string_trim_before(RtValue value) {
    RtString *s = as_string(value);
    if (!s) return value;                      /* BUG: raw literal passed through unchanged */
    uint64_t begin = 0, end = s->len;
    while (begin < end && s->data[begin] == ' ') begin++;
    while (end > begin && s->data[end - 1] == ' ') end--;
    return rt_string_new_v(s->data + begin, end - begin);
}
static RtValue rt_string_to_lower_before(RtValue value) {
    RtString *s = as_string(value);
    if (!s) return NIL_VALUE;                   /* BUG: raw literal degrades to nil */
    char *out = (char *)malloc(s->len + 1);
    for (uint32_t i = 0; i < s->len; i++) {
        char c = s->data[i];
        out[i] = (c >= 'A' && c <= 'Z') ? (char)(c + 32) : c;
    }
    out[s->len] = '\0';
    RtValue r = rt_string_new_v(out, s->len);
    free(out);
    return r;
}

/* ---- AFTER: promote a plausible raw pointer to a real heap string first,
 * matching the runtime_native.c fix (rt_string_promote_raw_receiver): a
 * word below the 0x10000 floor is left alone (genuinely "not text"). */
static int promote_raw(RtValue value, RtValue *out) {
    if (value < 0x10000) return 0;
    const char *p = (const char *)(uintptr_t)value;
    *out = rt_string_new_v(p, (uint64_t)strlen(p));
    return 1;
}
static RtValue rt_string_trim_after(RtValue value) {
    RtString *s = as_string(value);
    if (!s) {
        RtValue promoted;
        if (promote_raw(value, &promoted)) return rt_string_trim_after(promoted);
        return value;
    }
    uint64_t begin = 0, end = s->len;
    while (begin < end && s->data[begin] == ' ') begin++;
    while (end > begin && s->data[end - 1] == ' ') end--;
    return rt_string_new_v(s->data + begin, end - begin);
}
static RtValue rt_string_to_lower_after(RtValue value) {
    RtString *s = as_string(value);
    if (!s) {
        RtValue promoted;
        if (promote_raw(value, &promoted)) return rt_string_to_lower_after(promoted);
        return NIL_VALUE;
    }
    char *out = (char *)malloc(s->len + 1);
    for (uint32_t i = 0; i < s->len; i++) {
        char c = s->data[i];
        out[i] = (c >= 'A' && c <= 'Z') ? (char)(c + 32) : c;
    }
    out[s->len] = '\0';
    RtValue r = rt_string_new_v(out, s->len);
    free(out);
    return r;
}

static const char *text_of(RtValue v) {
    RtString *s = as_string(v);
    return s ? s->data : NULL;
}

static int failures = 0;
static int checked = 0;
static void expect_text(const char *what, RtValue got, const char *want)
{
    checked++;
    const char *g = text_of(got);
    if (!g || strcmp(g, want) != 0) {
        failures++;
        printf("  FAIL %-40s got=%s want=%s\n", what, g ? g : "(nil/raw)", want);
    } else {
        printf("  ok   %-40s = \"%s\"\n", what, g);
    }
}

int main(void)
{
    /* Raw, untagged string-literal pointer, as emit_bootstrap_str_const /
     * codegen emits for a bare literal that skipped ensure_tagged_str.
     * Word-aligned, matching a real compiler-emitted global. */
    static const char raw_padded[] __attribute__((aligned(8))) = "  padded  ";
    static const char raw_mixed[]  __attribute__((aligned(8))) = "MiXeD";
    RtValue RAW_PADDED = (RtValue)(uintptr_t)raw_padded;
    RtValue RAW_MIXED  = (RtValue)(uintptr_t)raw_mixed;

    printf("== BEFORE (shipped rt_string_trim / rt_string_to_lower) ==\n");
    int before_bug = 0;
    if (rt_string_trim_before(RAW_PADDED) == RAW_PADDED) {
        printf("  REPRODUCED: trim(raw \"  padded  \") returned the raw pointer unchanged\n");
        before_bug = 1;
    }
    if (rt_string_to_lower_before(RAW_MIXED) == NIL_VALUE) {
        printf("  REPRODUCED: to_lower(raw \"MiXeD\") returned nil\n");
        before_bug = 1;
    }
    if (!before_bug) {
        printf("  ERROR - the defect did not reproduce; selfcheck is vacuous\n");
        return 2;
    }

    printf("== AFTER (raw receiver promoted to a real heap string) ==\n");
    expect_text("trim(raw \"  padded  \")", rt_string_trim_after(RAW_PADDED), "padded");
    expect_text("to_lower(raw \"MiXeD\")",  rt_string_to_lower_after(RAW_MIXED), "mixed");

    /* Negative controls: heap-string receivers (already-working path)
     * must behave identically. */
    RtValue heap_padded = mk_heap_str("  padded  ");
    RtValue heap_mixed  = mk_heap_str("MiXeD");
    expect_text("trim(heap \"  padded  \")", rt_string_trim_after(heap_padded), "padded");
    expect_text("to_lower(heap \"MiXeD\")",  rt_string_to_lower_after(heap_mixed), "mixed");

    /* Small non-pointer words must never be dereferenced (bug 2026-07-23),
     * and must keep the documented "not text" contract. */
    checked++;
    if (rt_string_trim_after(NIL_VALUE) != NIL_VALUE) {
        failures++;
        printf("  FAIL trim(nil) must be a no-op\n");
    } else {
        printf("  ok   trim(nil) is a no-op\n");
    }
    checked++;
    if (rt_string_to_lower_after(NIL_VALUE) != NIL_VALUE) {
        failures++;
        printf("  FAIL to_lower(nil) must stay nil\n");
    } else {
        printf("  ok   to_lower(nil) stays nil\n");
    }
    checked++;
    RtValue small_int = (RtValue)7;
    if (rt_string_trim_after(small_int) != small_int) {
        failures++;
        printf("  FAIL trim(small int 7) must be a no-op\n");
    } else {
        printf("  ok   trim(small int 7) is a no-op\n");
    }

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
