/* rt_freestanding_string_len_abi_selfcheck.c
 *
 * Pins the string-object ABI that LLVM codegen bakes into every `text.len()`.
 *
 * `.len()` is NOT a call to rt_len on the native lanes: compile_inline_len
 * (src/compiler_rust/compiler/src/codegen/llvm/functions/calls.rs) expands it
 * inline to "load i64 from object+8", and the compiler emits string objects
 * whose data payload starts at object+16. The hosted runtime agrees --
 * RtCoreString is { u32 kind; u32 reserved; u64 len; char data[]; }
 * (src/runtime/runtime_native.c).
 *
 * Several freestanding/baremetal runtimes declared their RuntimeString with a
 * uint32_t len, putting data at offset 12. The C side then stayed
 * self-consistent (substring, equality, trim, starts_with and chars all read
 * the u32 and all agreed), but the codegen-inlined i64 load at offset 8 picked
 * up the length in its low half and the FIRST FOUR BYTES OF THE PAYLOAD in its
 * high half -- an astronomically large length. Every `while i < s.len()` loop
 * over such a string became unbounded, which is why product modules printed
 * correct output and then stalled with no trap.
 *
 * Incidents:
 *   doc/08_tracking/bug/x64_rt_extras_runtime_string_layout_mismatch.md
 *     (x86_64, fixed 2026-07-12, silently reverted by the tree wipe 6f86ff32a7d)
 *   doc/08_tracking/bug/riscv64_freestanding_runtime_text_len_and_loop_concat_2026-08-31.md
 *     (riscv64 in-guest components lane)
 *
 * Runs on the host; no OS boot, no cross toolchain.
 * Exit 0 = pass, 1 = fail, 2 = vacuous (the defect could not be reproduced,
 * so a subsequent pass would prove nothing).
 */

#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include <string.h>

/* Header shared by both layouts under test. */
typedef struct {
    uint32_t type;
    uint32_t size;
} HeapHeader;

/* The layout the defect shipped: len is 32-bit, so data lands at offset 12. */
typedef struct {
    HeapHeader hdr;
    uint32_t len;
    char data[];
} BuggyString;

/* The layout codegen and the hosted runtime require. */
typedef struct {
    HeapHeader hdr;
    uint64_t len;
    char data[];
} FixedString;

/* Exactly what compile_inline_len emits: an i64 load at byte offset 8. */
static int64_t codegen_inline_len(const void *object)
{
    int64_t v;
    memcpy(&v, (const unsigned char *)object + 8, sizeof(v));
    return v;
}

/* Exactly where the compiler places the payload of a string object. */
static const char *codegen_data(const void *object)
{
    return (const char *)((const unsigned char *)object + 16);
}

/* The subject from the riscv64 probe transcript: 15 bytes, pure ASCII, and its
 * first four payload bytes are non-zero, which is what corrupts the high half
 * of a 32-bit-len object read as an i64. */
static const char SUBJECT[] = "{\"role\":\"user\"}";
#define SUBJECT_LEN 15u

static unsigned char buggy_storage[64];
static unsigned char fixed_storage[64];

int main(void)
{
    int failures = 0;

    /* Layout contract of the object codegen expects. */
    if (offsetof(FixedString, len) != 8) {
        printf("FAIL: FixedString.len at offset %zu, codegen loads at 8\n",
               offsetof(FixedString, len));
        failures++;
    }
    if (offsetof(FixedString, data) != 16) {
        printf("FAIL: FixedString.data at offset %zu, codegen reads payload at 16\n",
               offsetof(FixedString, data));
        failures++;
    }

    /* ---- reproduce the defect on the old layout -------------------------- */
    memset(buggy_storage, 0, sizeof(buggy_storage));
    {
        BuggyString *b = (BuggyString *)buggy_storage;
        b->hdr.type = 1u;
        b->hdr.size = (uint32_t)(sizeof(BuggyString) + SUBJECT_LEN + 1u);
        b->len = SUBJECT_LEN;
        memcpy(b->data, SUBJECT, SUBJECT_LEN + 1u);

        /* The C side of the old runtime is self-consistent: this is why every
         * other probed primitive answered EXPECTED in-guest. */
        if (b->len != SUBJECT_LEN) {
            printf("FAIL: buggy layout's own C read is %u, expected %u\n",
                   (unsigned)b->len, SUBJECT_LEN);
            failures++;
        }

        int64_t seen = codegen_inline_len(b);
        if (seen == (int64_t)SUBJECT_LEN) {
            printf("VACUOUS: the 32-bit-len layout produced the correct length "
                   "%lld under a codegen i64 load; this selfcheck would prove "
                   "nothing.\n", (long long)seen);
            return 2;
        }
        printf("reproduced: codegen .len() over the 32-bit-len layout = %lld "
               "(expected %u) -- an unbounded `while i < s.len()`\n",
               (long long)seen, SUBJECT_LEN);
    }

    /* ---- the fixed layout satisfies the codegen contract ------------------ */
    memset(fixed_storage, 0, sizeof(fixed_storage));
    {
        FixedString *f = (FixedString *)fixed_storage;
        f->hdr.type = 1u;
        f->hdr.size = (uint32_t)(sizeof(FixedString) + SUBJECT_LEN + 1u);
        f->len = SUBJECT_LEN;
        memcpy(f->data, SUBJECT, SUBJECT_LEN + 1u);

        int64_t seen = codegen_inline_len(f);
        if (seen != (int64_t)SUBJECT_LEN) {
            printf("FAIL: codegen .len() over the 64-bit-len layout = %lld, "
                   "expected %u\n", (long long)seen, SUBJECT_LEN);
            failures++;
        }
        if (f->len != SUBJECT_LEN) {
            printf("FAIL: C-side len over the fixed layout = %llu, expected %u\n",
                   (unsigned long long)f->len, SUBJECT_LEN);
            failures++;
        }
        if (memcmp(codegen_data(f), SUBJECT, SUBJECT_LEN) != 0) {
            printf("FAIL: payload at codegen offset 16 does not match the subject\n");
            failures++;
        }
        if (codegen_data(f) != f->data) {
            printf("FAIL: C-side data pointer disagrees with codegen offset 16\n");
            failures++;
        }

        /* `.len()` stays BYTES. A multi-byte character must widen the byte
         * count, never the character count -- the fix must not be mistaken for
         * a bytes-vs-chars change. */
        const char utf8[] = "a\xE2\x80\x94" "b"; /* "a", em dash, "b" = 5 bytes */
        memset(fixed_storage, 0, sizeof(fixed_storage));
        f = (FixedString *)fixed_storage;
        f->hdr.type = 1u;
        f->len = (uint64_t)(sizeof(utf8) - 1u);
        memcpy(f->data, utf8, sizeof(utf8));
        if (codegen_inline_len(f) != 5) {
            printf("FAIL: .len() must stay BYTES; got %lld for a 5-byte / "
                   "3-character string\n", (long long)codegen_inline_len(f));
            failures++;
        }
    }

    /* A bounded scan over the fixed layout terminates. */
    {
        FixedString *f = (FixedString *)fixed_storage;
        f->len = SUBJECT_LEN;
        memcpy(f->data, SUBJECT, SUBJECT_LEN + 1u);
        int64_t n = codegen_inline_len(f);
        int64_t i = 0;
        int64_t guard = 0;
        while (i < n) {
            i++;
            if (++guard > 1000) {
                printf("FAIL: a `while i < s.len()` scan did not terminate\n");
                failures++;
                break;
            }
        }
        if (guard <= 1000 && i != (int64_t)SUBJECT_LEN) {
            printf("FAIL: scan ended at %lld, expected %u\n",
                   (long long)i, SUBJECT_LEN);
            failures++;
        }
    }

    if (failures) {
        printf("rt_freestanding_string_len_abi_selfcheck: %d failure(s)\n", failures);
        return 1;
    }
    printf("rt_freestanding_string_len_abi_selfcheck: OK\n");
    return 0;
}
