/* Core-C standalone lane must define BOTH runtime-kind probes.
 *
 * runtime.h declares rt_is_interpreter_runtime and rt_is_jit_runtime, and
 * simple_common::CORE_REQUIRED_RUNTIME_SYMBOLS requires both from the core-C
 * archive. Until 2026-08-22 only the interpreter probe lived in the
 * SIMPLE_CORE_C_STANDALONE block of runtime_native.c; the JIT probe was
 * defined only in runtime.c, which is NOT a core-C archive member, so
 * test_core_lane_runtime_archives_expose_required_abi_symbols failed with
 * `missing: ["rt_is_jit_runtime"]`.
 *
 * Build (links against the standalone-compiled runtime_native.o, i.e. the
 * exact TU the core-C archive is made from):
 *   cc -c -std=gnu11 -ffunction-sections -DSIMPLE_CORE_C_STANDALONE=1 \
 *      -Isrc/runtime -Isrc/runtime/platform src/runtime/runtime_native.c -o rn.o
 *   cc -std=gnu11 -Wl,--gc-sections \
 *      src/runtime/test/rt_runtime_kind_probes_core_c_selfcheck.c rn.o \
 *      -lpthread -lm -ldl -o probes && ./probes
 * (--gc-sections drops the unreferenced TUs whose Simple-side providers, e.g.
 * spl_eprintln, are only present at a real native link.)
 * An AOT-native binary linked against the C runtime is neither the seed
 * interpreter nor seed-JIT, so both must answer false.
 */
#include <stdbool.h>
#include <stdio.h>

extern bool rt_is_interpreter_runtime(void);
extern bool rt_is_jit_runtime(void);

int main(void) {
    int failures = 0;
    if (rt_is_interpreter_runtime()) {
        fprintf(stderr, "FAIL: rt_is_interpreter_runtime() returned true in core-C lane\n");
        failures++;
    }
    if (rt_is_jit_runtime()) {
        fprintf(stderr, "FAIL: rt_is_jit_runtime() returned true in core-C lane\n");
        failures++;
    }
    if (failures == 0) {
        printf("PASS: core-C lane defines both runtime-kind probes, both false\n");
    }
    return failures == 0 ? 0 : 1;
}
