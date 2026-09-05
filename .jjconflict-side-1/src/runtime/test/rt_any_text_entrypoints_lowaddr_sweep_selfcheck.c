/* SIMILAR-PROBLEM DETECTION sweep for the defect CLASS behind
 * native_text_eq_any_untagged_smallint_deref_2026-07-23.
 *
 * The reproducing selfcheck (rt_text_eq_any_untagged_smallint_selfcheck.c)
 * pins ONE entry point at ONE value (0x148). That is not the shape of the
 * defect. The class is:
 *
 *   Every runtime entry point that accepts an `any`-typed operand and
 *   normalizes it to a raw `char*` via rt_interp_cstr will dereference a
 *   BOXED SMALL INTEGER as a pointer, because a boxed int `v << 3` is
 *   arithmetically indistinguishable from an aligned low heap pointer.
 *
 * There are five such entry points in runtime_native.c today, and the class
 * grows every time someone adds a sixth. std.common.json takes `any`
 * everywhere, so any of them can receive garbage on a legal-but-wrong program
 * -- and the interpreter answers gracefully for all of them, so a native-only
 * SIGSEGV is a pure interp/native divergence.
 *
 * This sweep drives all five over the whole low-address value class rather
 * than one value:
 *   - boxed positives  v << 3 for v in a spread from 0 to 8191
 *   - boxed negatives  v << 3 for negative v (the sign-extended arm the
 *     original fix note called out explicitly)
 *   - the raw sentinels 0, 1, 2, 3 (nil/bool/special tags)
 *   - values straddling the 0x10000 floor rt_interp_cstr uses
 *
 * Each probe runs in a FORKED CHILD, so a segfault is REPORTED with the exact
 * function and value that caused it instead of taking the harness down. That
 * is the whole point: a crash-class sweep that itself dies on the first crash
 * can only ever find one defect.
 *
 * Note what this does NOT assert: it makes no claim about the RESULT of these
 * calls on garbage input (that is per-function and covered by the focused
 * selfchecks). It asserts only that no `any`-accepting text entry point
 * dereferences a low integer -- the invariant whose violation is always a
 * silent-crash channel.
 *
 * Values at or above the 0x10000 floor are deliberately NOT dereferenced by
 * this sweep: above that floor rt_interp_cstr is contractually allowed to
 * treat the word as a real pointer, so feeding it a fake one would test the
 * harness, not the runtime.
 *
 * Build + run:
 *   gcc -std=gnu11 -O1 -w -Wl,-z,muldefs -o /tmp/any_text_lowaddr_sweep \
 *     src/runtime/test/rt_any_text_entrypoints_lowaddr_sweep_selfcheck.c \
 *     $(ls src/runtime/*.c | grep -vE \
 *       'hosted_cocoa|hosted_win32|directx|openssl|wasm|audio|font|image|sdl2|runtime_time|counterpart') \
 *     -lm -lpthread -ldl -lsqlite3
 */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <unistd.h>

extern int64_t rt_text_eq_any(int64_t left, int64_t right);
extern int64_t rt_text_cmp_any(int64_t left, int64_t right);
extern int64_t rt_string_to_int_any(int64_t value);
extern int64_t rt_strcat_tagged(int64_t a, int64_t b);
extern int64_t rt_to_string(int64_t value);
extern int64_t rt_string_new(const uint8_t* bytes, uint64_t len);

/* rt_interp_cstr's non-pointer floor (runtime_native.c). Anything below this
 * must never be dereferenced by any entry point in the table. */
#define RT_INTERP_CSTR_FLOOR 0x10000

static int crashes = 0;
static int probes = 0;

/* Run one call in a child. Returns 0 if the child exited normally (any exit
 * status), 1 if it died on a signal (SIGSEGV/SIGBUS being the defect). */
static int run_isolated(int which, int64_t value, int64_t text) {
    fflush(stdout);
    pid_t pid = fork();
    if (pid < 0) {
        printf("ERROR fork failed\n");
        exit(2);
    }
    if (pid == 0) {
        volatile int64_t sink = 0;
        switch (which) {
            case 0: sink = rt_text_eq_any(value, text); break;
            case 1: sink = rt_text_eq_any(text, value); break;
            case 2: sink = rt_text_cmp_any(value, text); break;
            case 3: sink = rt_string_to_int_any(value); break;
            case 4: sink = rt_strcat_tagged(value, text); break;
            case 5: sink = rt_to_string(value); break;
        }
        (void)sink;
        _exit(0);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    return WIFSIGNALED(status) ? WTERMSIG(status) : 0;
}

static const char* fn_name(int which) {
    switch (which) {
        case 0: return "rt_text_eq_any(garbage, text)";
        case 1: return "rt_text_eq_any(text, garbage)";
        case 2: return "rt_text_cmp_any(garbage, text)";
        case 3: return "rt_string_to_int_any(garbage)";
        case 4: return "rt_strcat_tagged(garbage, text)";
        default: return "rt_to_string(garbage)";
    }
}

static void probe(int which, int64_t value, const char* label, int64_t text) {
    probes++;
    int sig = run_isolated(which, value, text);
    if (sig != 0) {
        printf("FAIL %s on %s (0x%llx) died with signal %d\n",
               fn_name(which), label, (unsigned long long)value, sig);
        crashes++;
    }
}

int main(void) {
    int64_t text = rt_string_new((const uint8_t*)"array", 5);

    /* Boxed small integers, positive: the exact encoding of the original
     * defect (41 << 3 == 0x148), swept across magnitudes. */
    static const int64_t positives[] = {0, 1, 2, 3, 7, 41, 42, 255, 256, 1000,
                                        2026, 4095, 8191};
    /* Boxed small integers, negative: sign-extended `v << 3`. */
    static const int64_t negatives[] = {-1, -2, -3, -41, -255, -2026, -8191};
    /* Raw untagged sentinels and near-floor values. */
    static const int64_t raws[] = {0, 1, 2, 3, 8, 0x100, 0xfff8,
                                   RT_INTERP_CSTR_FLOOR - 8};

    for (int which = 0; which <= 5; which++) {
        for (size_t i = 0; i < sizeof(positives) / sizeof(positives[0]); i++) {
            probe(which, positives[i] << 3, "boxed positive", text);
        }
        for (size_t i = 0; i < sizeof(negatives) / sizeof(negatives[0]); i++) {
            probe(which, negatives[i] << 3, "boxed negative", text);
        }
        for (size_t i = 0; i < sizeof(raws) / sizeof(raws[0]); i++) {
            probe(which, raws[i], "raw low word", text);
        }
    }

    /* Control: the sweep must be capable of observing a crash at all. If this
     * deliberate null dereference is reported as clean, the harness is broken
     * and every "clean" verdict above is vacuous. */
    fflush(stdout);
    pid_t pid = fork();
    if (pid == 0) {
        volatile int* p = (int*)0;
        *p = 1;
        _exit(0);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    if (!WIFSIGNALED(status)) {
        printf("FAIL control: deliberate null deref was not observed as a signal"
               " -- this harness cannot detect crashes, verdict is vacuous\n");
        printf("RT_ANY_TEXT_LOWADDR_SWEEP_SELFCHECK: FAIL\n");
        return 1;
    }
    printf("PASS control: deliberate null deref observed as signal %d\n",
           WTERMSIG(status));

    if (crashes == 0) {
        printf("RT_ANY_TEXT_LOWADDR_SWEEP_SELFCHECK: PASS\n");
        printf("VERDICT: %d probes across 6 any-text entry points, 0 crashes\n",
               probes);
        return 0;
    }
    printf("RT_ANY_TEXT_LOWADDR_SWEEP_SELFCHECK: FAIL\n");
    printf("VERDICT: %d probes, %d crash(es)\n", probes, crashes);
    return 1;
}
