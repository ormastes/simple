/* Probe: can the driver's eviction targets actually be reclaimed by the
 * rt_*_free_deep family?  The driver's three eviction targets are
 *   modules:     Dict<text, ParserModule>
 *   hir_modules: Dict<text, HirModule>
 *   mir_modules: Dict<text, MirModule>
 * i.e. Dict<text, CLASS INSTANCE> in all three cases.
 *
 * P0 is the RED: it measures what eviction reclaims TODAY (0).
 * P1 is the control: the same primitive on a string-valued dict (2001).
 * P2 is the driver's real shape, and the finding: the call ACCEPTS but frees
 *    only keys+header, stranding every module object.
 * P3 measures hazard 4: an externally-aliased key is freed under its holder.
 * P4 checks rt_free_deep still refuses a class-instance ROOT.
 *
 * Full analysis:
 *   doc/08_tracking/bug/bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md
 *   (UPDATE 2026-08-06, third session)
 *
 * Build + run (same line the existing selfchecks document; the runtime dir
 * holds mutually-exclusive alternative TUs, hence the filter and -z muldefs):
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/evict_probe \
 *     src/runtime/test/rt_driver_eviction_reclaim_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time') \
 *     -lm -lpthread -ldl -lsqlite3
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);
extern int64_t rt_string_len(int64_t value);
extern int64_t rt_heap_registry_count(void);
extern int64_t rt_dict_new(int64_t cap_hint);
extern int8_t  rt_dict_set(int64_t dict, int64_t key, int64_t value);
extern int64_t rt_dict_free_deep(int64_t value);
extern int64_t rt_free_deep(int64_t value);

static int64_t mkstr(const char* s) {
    return rt_string_new((const uint8_t*)s, (uint64_t)strlen(s));
}

#define N 1000

/* Build a dict shaped like the driver's `modules` / `hir_modules` /
 * `mir_modules`: text keys, values of the given maker. */
static int64_t build(int64_t (*mkval)(int i), int64_t* keys_out) {
    int64_t d = rt_dict_new(N * 2);
    for (int i = 0; i < N; i++) {
        char buf[64];
        snprintf(buf, sizeof buf, "module_name_%d", i);
        int64_t k = mkstr(buf);
        if (keys_out) keys_out[i] = k;
        rt_dict_set(d, k, mkval(i));
    }
    return d;
}

static int64_t mk_string_val(int i) {
    char buf[128];
    snprintf(buf, sizeof buf, "payload contents for module %d", i);
    return mkstr(buf);
}

/* A class/struct instance on this lane: an UNTAGGED, UNREGISTERED,
 * header-less rt_alloc block (see the rt_free_deep contract in runtime.h). */
static int64_t mk_class_instance_val(int i) {
    void* p = calloc(1, 256);
    return (int64_t)(uintptr_t)p;
}

int main(void) {
    int failures = 0;

    /* ---- P0 (RED): what evict_ast()/evict_hir() do TODAY ----------------
     * `self.modules = {}` drops the reference. With no GC and no refcount
     * that must reclaim nothing. */
    {
        int64_t before = rt_heap_registry_count();
        int64_t d = build(mk_string_val, NULL);
        int64_t after_build = rt_heap_registry_count();
        int64_t pre_replacement = rt_heap_registry_count();
        d = rt_dict_new(4);              /* <- exactly `self.modules = {}` */
        int64_t after_drop = rt_heap_registry_count();
        /* the replacement `{}` registers itself; discount it so `reclaimed`
         * counts ONLY what the drop gave back */
        int64_t replacement_cost = after_drop - pre_replacement;
        int64_t built = after_build - before;
        int64_t reclaimed = (after_build - after_drop) + replacement_cost;
        printf("P0 RED   evict-by-reassign: built=%lld reclaimed=%lld "
               "(replacement dict cost %lld new registration)\n",
               (long long)built, (long long)reclaimed, (long long)replacement_cost);
        if (reclaimed != 0) { printf("  UNEXPECTED: drop reclaimed memory\n"); failures++; }
        else printf("  CONFIRMED: eviction is a NO-OP, 0 of %lld allocations freed\n",
                    (long long)built);
    }

    /* ---- P1: the primitive itself works on a string-valued dict -------- */
    {
        int64_t before = rt_heap_registry_count();
        int64_t d = build(mk_string_val, NULL);
        int64_t after_build = rt_heap_registry_count();
        int64_t verdict = rt_dict_free_deep(d);
        int64_t after_free = rt_heap_registry_count();
        printf("P1 GREEN string-valued dict: verdict=%lld built=%lld delta_free=%lld\n",
               (long long)verdict, (long long)(after_build - before),
               (long long)(after_build - after_free));
        if (verdict != 1) { printf("  UNEXPECTED: refused\n"); failures++; }
    }

    /* ---- P2: the DRIVER'S ACTUAL SHAPE: Dict<text, class instance> -----
     * This is `modules` / `hir_modules` / `mir_modules`. The class instances
     * hold essentially all the memory. */
    {
        int64_t before = rt_heap_registry_count();
        int64_t d = build(mk_class_instance_val, NULL);
        int64_t after_build = rt_heap_registry_count();
        int64_t verdict = rt_dict_free_deep(d);
        int64_t after_free = rt_heap_registry_count();
        int64_t delta = after_build - after_free;
        printf("P2 DRIVER Dict<text,class-instance>: verdict=%lld "
               "registered_built=%lld delta_free=%lld class_instances=%d\n",
               (long long)verdict, (long long)(after_build - before),
               (long long)delta, N);
        if (verdict == 1)
            printf("  ACCEPTED -- but the %d class instances are UNTAGGED/UNREGISTERED,\n"
                   "  so they were classified as LEAVES and STRANDED. Only keys+header freed.\n", N);
        else
            printf("  REFUSED -- reclaims NOTHING.\n");
    }

    /* ---- P3: HAZARD 4 -- a key aliased from OUTSIDE the structure -------
     * MirFunction.name / export_name are the SAME heap strings as the
     * HIR/AST/SymbolTable copies, which live outside mir_modules. The
     * planner's `seen` set only spans nodes it TRAVERSES, so an external
     * alias is undetectable. */
    {
        int64_t* keys = calloc(N, sizeof(int64_t));
        int64_t d = build(mk_string_val, keys);
        /* an outside holder of the very same key strings (the SymbolTable) */
        int64_t witness = keys[0];
        int64_t len_before = rt_string_len(witness);
        int64_t verdict = rt_dict_free_deep(d);
        printf("P3 HAZARD4 externally-aliased keys: verdict=%lld key_len_before=%lld\n",
               (long long)verdict, (long long)len_before);
        if (verdict == 1)
            printf("  ACCEPTED -- the external holder now points at FREED storage.\n"
                   "  An external alias is NOT detectable; this would CORRUPT the compiler.\n");
        else
            printf("  refused\n");
        free(keys);
    }

    /* ---- P4: rt_free_deep on a class-instance root --------------------- */
    {
        int64_t inst = mk_class_instance_val(0);
        int64_t verdict = rt_free_deep(inst);
        printf("P4 rt_free_deep(class instance root): verdict=%lld (expect 0/refuse)\n",
               (long long)verdict);
        if (verdict != 0) { printf("  UNEXPECTED: accepted an unidentifiable root\n"); failures++; }
    }

    printf("\nfailures=%d\n", failures);
    return failures ? 1 : 0;
}
