/*
 * Regression: rt_process_run_tuple (the LLVM/Cranelift tuple facade) must free
 * the owner result array it copies its three slots out of. Before the fix each
 * spawn leaked that array (header + data), i.e. 3 live malloc blocks per call;
 * after it, only the rt_alloc'd 3-word tuple block the pure-Simple destructure
 * reads remains (1 per call, owned by the transient raw registry).
 *
 * Measured with malloc_zone_statistics (macOS). Not a portable test: it is a
 * no-op "skip" elsewhere.
 *
 * Build and run (macOS, from the repo root; the runtime's unrelated SFFI
 * symbols stay unresolved and are never reached by this test, and
 * runtime_legacy_core.c supplies spl_str_concat for the popen path):
 *   clang -O0 -Isrc/runtime -w test/runtime/process_result_tuple_owner_free_test.c \
 *     src/runtime/runtime_native.c src/runtime/runtime_legacy_core.c \
 *     -Wl,-undefined,dynamic_lookup -o "$TMPDIR/pr_tuple_test" && "$TMPDIR/pr_tuple_test"
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#ifdef __APPLE__
#include <malloc/malloc.h>

int64_t *rt_process_run_tuple(const char *cmd, uint64_t cmd_len, void *args);
void *rt_array_new(int64_t cap);
void rt_array_free(void *value);

int main(void) {
    enum { ITERS = 200, MAX_BLOCKS_PER_CALL_X100 = 150 };
    malloc_statistics_t before, after;
    malloc_zone_statistics(NULL, &before);
    for (int i = 0; i < ITERS; i++) {
        void *args = rt_array_new(0);
        int64_t *tuple = rt_process_run_tuple("true", 4, args);
        rt_array_free(args);
        if (!tuple || tuple[2] != 0) {
            fprintf(stderr, "FAIL: spawn of `true` did not report status 0\n");
            return 1;
        }
    }
    malloc_zone_statistics(NULL, &after);
    long blocks = (long)(after.blocks_in_use - before.blocks_in_use);
    /* Allow 1.5 live blocks per call: the tuple block itself (1) plus slack. */
    if (blocks * 100 > (long)ITERS * MAX_BLOCKS_PER_CALL_X100) {
        fprintf(stderr,
                "FAIL: %ld live malloc blocks over %d spawns (%.2f/call); owner result arrays leaked\n",
                blocks, ITERS, (double)blocks / ITERS);
        return 1;
    }
    printf("ok: %ld live malloc blocks over %d spawns (%.2f/call)\n", blocks, ITERS,
           (double)blocks / ITERS);
    return 0;
}
#else
int main(void) {
    printf("skip: process tuple owner-free check is macOS-only\n");
    return 0;
}
#endif
