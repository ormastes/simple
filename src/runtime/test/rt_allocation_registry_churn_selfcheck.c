/* Exercise the actual registry owners with a bounded live set and distinct
 * retired addresses. Including the owner gives the check its table-byte oracle
 * without adding a production ABI solely for testing. Unused runtime sections
 * are discarded by the test linker. */
#if defined(RT_REGISTRY_MEMORY_PROVIDER)
#include "../runtime_memory.c"
#define raw_register rt_transient_raw_register
#define raw_erase rt_transient_raw_erase
#define raw_lookup rt_transient_raw_lookup
#define raw_active rt_transient_raw_active
#define raw_capacity rt_transient_raw_cap
#define raw_length rt_transient_raw_len
#define raw_owned_bit RT_TRANSIENT_RAW_OWNED_BIT
#define PROVIDER "memory"
#else
#include "../runtime_native.c"
#define raw_register rt_core_transient_raw_register
#define raw_erase rt_core_transient_raw_erase
#define raw_lookup rt_core_transient_raw_lookup
#define raw_active rt_core_transient_array_scope_active
#define raw_capacity rt_core_transient_raw_alloc_cap
#define raw_length rt_core_transient_raw_alloc_len
#define raw_owned_bit RT_CORE_TRANSIENT_RAW_OWNED_BIT
#define PROVIDER "native"
#endif
#include <stdio.h>

enum { MODULES = 512, MODULE_LIVE = 48, GROWTH_LIVE = 512 };
static int failures;

static void require(int ok, const char *message) {
    if (!ok) {
        fprintf(stderr, "FAIL %s: %s\n", PROVIDER, message);
        failures++;
    }
}

int main(void) {
    /* Keep storage valid while retiring registry membership. Fresh addresses
     * prevent malloc's address reuse from hiding tombstone accumulation. */
    uint64_t *pool = calloc(1 + MODULES * MODULE_LIVE + GROWTH_LIVE,
                            sizeof(uint64_t));
    if (!pool) return 2;
    raw_active = 1;
    require(rt_struct_alloc_register(pool, 8) && raw_register(pool, 8),
            "retained cross-module root registers");
    for (size_t module = 0; module < MODULES && !failures; module++) {
        for (size_t i = 0; i < MODULE_LIVE; i++) {
            void *ptr = pool + 1 + module * MODULE_LIVE + i;
            require(rt_struct_alloc_register(ptr, 8) && raw_register(ptr, 8),
                    "module allocation registers");
        }
        for (size_t i = 0; i < MODULE_LIVE; i++) {
            void *ptr = pool + 1 + module * MODULE_LIVE + i;
            rt_struct_alloc_unregister(ptr);
            raw_erase(ptr);
            size_t bytes = 0;
            require(!rt_struct_alloc_lookup_size(ptr, &bytes) && !raw_lookup((uintptr_t)ptr),
                    "retired module address is absent");
        }
        size_t bytes = 0;
        require(rt_struct_alloc_lookup_size(pool, &bytes) && bytes == 8 &&
                    raw_lookup((uintptr_t)pool) &&
                    raw_lookup((uintptr_t)pool)->bytes == (8 | raw_owned_bit),
                "retained root survives registry compaction");
        require(rt_struct_alloc_len == 1 && raw_length == 1,
                "live set returns to one root after each module");
    }
    printf("%s churn: modules=%d live=%zu struct_bytes=%zu raw_bytes=%zu\n",
           PROVIDER, MODULES, rt_struct_alloc_len,
           rt_struct_alloc_cap * sizeof(RtStructAllocation),
           raw_capacity * sizeof(*raw_lookup((uintptr_t)pool)));
    require(rt_struct_alloc_cap <= 256, "struct registry stays within initial byte budget");
    require(raw_capacity <= 256, "raw registry stays within initial byte budget");

    /* Compaction must still grow for genuine live demand and preserve sizes. */
    for (size_t i = 0; i < GROWTH_LIVE; i++) {
        void *ptr = pool + 1 + MODULES * MODULE_LIVE + i;
        require(rt_struct_alloc_register(ptr, 8) && raw_register(ptr, 8),
                "larger live set registers");
    }
    for (size_t i = 0; i < GROWTH_LIVE; i++) {
        void *ptr = pool + 1 + MODULES * MODULE_LIVE + i;
        size_t bytes = 0;
        require(rt_struct_alloc_lookup_size(ptr, &bytes) && bytes == 8 &&
                    raw_lookup((uintptr_t)ptr) &&
                    raw_lookup((uintptr_t)ptr)->bytes == (8 | raw_owned_bit),
                "live allocation size and ownership survive growth");
        rt_struct_alloc_unregister(ptr);
        raw_erase(ptr);
    }
    rt_struct_alloc_unregister(pool);
    raw_erase(pool);
    raw_active = 0;
    require(rt_struct_alloc_len == 0 && raw_length == 0, "all fixture owners release");
    free(pool);
    printf("SELFCHECK %s (%d failures)\n", failures ? "FAILED" : "PASSED", failures);
    return failures ? 1 : 0;
}
