/* Self-check for the RtCoreDict registry and the rt_core_as_dict safety gate.
 *
 * rt_core_as_dict used to trust the RT_VALUE_TAG_HEAP tag bits alone and read
 * (masked_value)->kind straight away. Every other heap type -- string, array,
 * enum, mutex, heap-boxed f64 -- proves registry membership by pure pointer
 * comparison BEFORE any dereference, precisely because the low-3-bit tag is
 * ambiguous: a flat i64 payload congruent to 1 mod 8 aliases TAG_HEAP without
 * being a heap object at all. Dict was the one hole, and it is the same shape
 * as the enum SIGSEGV already documented at rt_core_register_enum.
 *
 * Case 4 is the one that catches it: it hands a dict accessor an address that
 * is validly tagged, >= 4096, and NOT MAPPED. With the membership gate the
 * accessor refuses it. Without the gate the ->kind read faults.
 *
 * NEGATIVE CONTROL: delete the rt_core_is_registered_dict(d) line from
 * rt_core_as_dict and case 4 must fail (the probe child dies on SIGSEGV) and
 * cases 1/5 must fail (unregistered dicts would still be accepted, so nothing
 * would be gated). A check that cannot fail proves nothing.
 *
 * Build + run:
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/rtdict \
 *     src/runtime/test/rt_dict_registry_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3 && /tmp/rtdict
 */
#include <stdio.h>
#include <string.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

#define TAG_MASK 0x7ULL
#define TAG_HEAP 0x1ULL

extern int64_t rt_dict_new(int64_t cap_hint);
extern int64_t rt_dict_get(int64_t dict, int64_t key);
extern int8_t  rt_dict_set(int64_t dict, int64_t key, int64_t value);
extern int8_t  rt_dict_contains(int64_t dict, int64_t key);
extern int8_t  rt_dict_remove(int64_t dict, int64_t key);
extern int64_t rt_dict_len(int64_t dict);
extern int64_t rt_dict_keys(int64_t dict);
extern int64_t rt_heap_registry_count(void);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

static int failures = 0;

static void check(int cond, const char* what) {
    if (cond) {
        printf("  ok   %s\n", what);
    } else {
        printf("  FAIL %s\n", what);
        failures++;
    }
}

static int64_t mkstr(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

/* Run `probe` in a forked child so a dereference of a bad pointer is reported
 * as a signal rather than taking the whole self-check down. Returns 1 if the
 * child exited normally, 0 if it died on a signal. */
static int survives(void (*probe)(int64_t), int64_t arg) {
    fflush(stdout);
    pid_t pid = fork();
    if (pid == 0) {
        probe(arg);
        _exit(0);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    return WIFEXITED(status) && WEXITSTATUS(status) == 0;
}

static void probe_all_accessors(int64_t handle) {
    /* every entry point that funnels through rt_core_as_dict */
    (void)rt_dict_len(handle);
    (void)rt_dict_contains(handle, 1);
    (void)rt_dict_get(handle, 1);
    (void)rt_dict_set(handle, 1, 2);
    (void)rt_dict_remove(handle, 1);
    (void)rt_dict_keys(handle);
}

int main(void) {
    /* Line-buffer stdout: without the gate this process dies on SIGSEGV, and a
     * block-buffered stdout would discard the FAIL line that names the cause. */
    setvbuf(stdout, NULL, _IOLBF, 0);

    /* 1. a real dict is accepted, and registration is accounted for */
    int64_t before = rt_heap_registry_count();
    int64_t d = rt_dict_new(0);
    check(d != 0, "rt_dict_new returns a handle");
    check((((uint64_t)d) & TAG_MASK) == TAG_HEAP, "handle carries the HEAP tag");
    check(rt_heap_registry_count() == before + 1, "new dict registers (+1)");
    check(rt_dict_len(d) == 0, "a real dict is accepted by rt_dict_len");
    check(rt_dict_set(d, 5, 42) == 1, "a real dict is accepted by rt_dict_set");

    /* 2. no regression: ordinary get/put/remove over int keys */
    check(rt_dict_get(d, 5) == 42, "int key round-trips");
    check(rt_dict_len(d) == 1, "len reflects one live entry");
    check(rt_dict_contains(d, 5) == 1, "contains finds the live int key");
    check(rt_dict_contains(d, 6) == 0, "contains rejects an absent int key");
    check(rt_dict_set(d, 5, 43) == 1, "overwrite of an existing key accepted");
    check(rt_dict_get(d, 5) == 43, "overwrite is visible");
    check(rt_dict_len(d) == 1, "overwrite does not grow len");
    check(rt_dict_remove(d, 5) == 1, "remove of a live key succeeds");
    check(rt_dict_len(d) == 0, "len drops after remove");
    check(rt_dict_contains(d, 5) == 0, "removed key is gone");
    check(rt_dict_remove(d, 5) == 0, "second remove refused");

    /* 3. no regression: string keys, and growth past the initial capacity */
    int64_t k = mkstr("alpha");
    check(rt_dict_set(d, k, 7) == 1, "string key accepted");
    check(rt_dict_contains(d, k) == 1, "string key found");
    check(rt_dict_contains(d, mkstr("alpha")) == 1, "string key matches by content, not identity");
    check(rt_dict_contains(d, mkstr("beta")) == 0, "a different string key does not match");
    char buf[64];
    for (int i = 0; i < 200; i++) {
        snprintf(buf, sizeof buf, "grow-key-%d", i);
        rt_dict_set(d, mkstr(buf), i);
    }
    check(rt_dict_len(d) == 201, "all 200 inserts plus the string key are live (resize ok)");
    int all_found = 1;
    for (int i = 0; i < 200; i++) {
        snprintf(buf, sizeof buf, "grow-key-%d", i);
        if (rt_dict_get(d, mkstr(buf)) != i) { all_found = 0; break; }
    }
    check(all_found, "every key survives resize with its value");

    /* 4. THE GATE. A validly-tagged, >=4096, UNMAPPED address must be refused
     *    rather than dereferenced. This is the flat-i64-aliasing-TAG_HEAP case.
     *    Without the membership gate the ->kind read faults here. */
    void* page = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
                      MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    check(page != MAP_FAILED, "probe page mapped");
    munmap(page, 4096); /* address is now valid-looking but unmapped */
    int64_t wild = (int64_t)((((uint64_t)(uintptr_t)page) & ~TAG_MASK) | TAG_HEAP);
    check((uintptr_t)wild >= 4096, "wild handle clears the low-address guard");
    check(survives(probe_all_accessors, wild),
          "unmapped HEAP-tagged handle is REFUSED, not dereferenced");
    check(rt_dict_len(wild) == 0, "wild handle reads as an empty non-dict");
    check(rt_dict_set(wild, 1, 2) == 0, "wild handle refuses a put");

    /* 5. a NON-DICT heap value handed to a dict accessor is refused. The
     *    registry is checked before ->kind, so this never dereferences the
     *    foreign object as a dict. */
    int64_t s = mkstr("this is a heap string, not a dict");
    check((((uint64_t)s) & TAG_MASK) == TAG_HEAP, "string handle carries the HEAP tag too");
    check(rt_dict_len(s) == 0, "string passed to rt_dict_len is refused");
    check(rt_dict_contains(s, 1) == 0, "string passed to rt_dict_contains is refused");
    check(rt_dict_set(s, 1, 2) == 0, "string passed to rt_dict_set is refused");
    check(rt_dict_remove(s, 1) == 0, "string passed to rt_dict_remove is refused");
    check(survives(probe_all_accessors, s), "no accessor faults on the string handle");

    /* the string must be undamaged -- a refused call must not have written */
    check(rt_dict_len(d) == 201, "the real dict is untouched by the refusals");

    /* 6. an INTERIOR pointer to a real dict is not a member and is refused.
     *    Only the exact registered base address counts. */
    int64_t interior = (int64_t)((((uint64_t)d & ~TAG_MASK) + 8) | TAG_HEAP);
    check(rt_dict_len(interior) == 0, "interior pointer into a live dict is refused");

    /* 7. accounting stays consistent across many allocations */
    int64_t base = rt_heap_registry_count();
    enum { N = 512 };
    for (int i = 0; i < N; i++) {
        int64_t t = rt_dict_new(0);
        if (t == 0) { check(0, "bulk allocation failed"); break; }
    }
    check(rt_heap_registry_count() == base + N, "each dict increments the registry by exactly 1");

    /* 8. registered dicts stay usable after the registry has grown/rehashed */
    check(rt_dict_len(d) == 201, "the original dict is still registered after churn");
    check(rt_dict_get(d, k) == 7, "the original dict still reads correctly after churn");

    printf("%s (%d failure%s)\n", failures ? "SELFCHECK FAILED" : "SELFCHECK PASSED",
           failures, failures == 1 ? "" : "s");
    return failures ? 1 : 0;
}
