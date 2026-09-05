/* rt_clear receiver-dispatch harness.
 *
 * Purpose: observe, WITHOUT a bootstrap, what the Dict arm added to rt_clear by
 * 8510a8368ca2 does when handed a receiver that is NOT a dict. The suspected
 * mechanism (see doc/08_tracking/bug/) is misclassification: a registered
 * non-dict heap object admitted by rt_core_as_dict, after which rt_dict_clear
 * walks d->cap entries at DICT field offsets over a smaller object -- a wild
 * write, not a use-after-free.
 *
 * The product source is #included so the file-static predicates
 * (rt_core_as_dict, rt_core_is_registered_dict, rt_core_registered_object_kind)
 * are directly observable. Every case that is EXPECTED to be loud runs in a
 * forked child, because rt_refuse_non_text_receiver terminates the process.
 *
 * Verdict is the LAST line on stdout. 0 cases checked is ERROR.
 */
#include "../../src/runtime/runtime_native.c"

#include <sys/wait.h>

static int g_checked = 0;
static int g_failed = 0;

static void report(const char* name, int ok, const char* detail) {
    g_checked++;
    if (!ok) g_failed++;
    printf("[%s] %-52s %s\n", ok ? " ok " : "FAIL", name, detail ? detail : "");
    fflush(stdout);
}

/* Run `body` in a child; return the child's wait status encoded as:
 *   0..255   -> normal exit code
 *   -SIGNUM  -> killed by signal (so -11 is SIGSEGV) */
static int run_isolated(void (*body)(void)) {
    fflush(stdout);
    pid_t pid = fork();
    if (pid == 0) {
        body();
        _exit(0);
    }
    int status = 0;
    waitpid(pid, &status, 0);
    if (WIFSIGNALED(status)) return -WTERMSIG(status);
    return WEXITSTATUS(status);
}

/* ---------- case bodies ---------- */

/* A registered ARRAY whose kind byte has been stomped to RT_VALUE_HEAP_DICT.
 * This is the exact shape the misclassification hypothesis predicts. The array
 * struct is 32 bytes; RtCoreDict reads ->entries at offset 32, i.e. one word
 * PAST the end of the allocation. */
static void body_stomped_array(void) {
    SplArray* a = rt_array_new(0);
    for (int i = 0; i < 4; i++) rt_array_push(a, (int64_t)(((uint64_t)i << 3) | RT_VALUE_TAG_INT));
    RtCoreArray* base = rt_core_array_ptr(a);
    int64_t recv = (int64_t)(((uint64_t)(uintptr_t)base) | RT_VALUE_TAG_HEAP);
    base->kind = (uint8_t)RT_VALUE_HEAP_DICT;
    RtCoreDict* seen = rt_core_as_dict(recv);
    fprintf(stderr, "stomped_array: as_dict=%p cap=%lld entries=%p\n",
            (void*)seen,
            seen ? (long long)seen->cap : -1LL,
            seen ? (void*)seen->entries : NULL);
    rt_clear(recv);
}

int main(void) {
    printf("== rt_clear receiver-dispatch harness ==\n");

    /* sizeof evidence: the two layouts that the hypothesis says overlap. */
    printf("sizeof(RtCoreArray)=%zu sizeof(RtCoreDict)=%zu "
           "offsetof(dict.entries)=%zu offsetof(dict.cap)=%zu\n",
           sizeof(RtCoreArray), sizeof(RtCoreDict),
           offsetof(RtCoreDict, entries), offsetof(RtCoreDict, cap));

    /* ---- C1: positive control. A real dict must actually clear. ---- */
    {
        int64_t d = rt_dict_new(0);
        for (int i = 0; i < 5; i++) {
            rt_dict_set(d, rt_value_int(i), rt_value_int(i * 7));
        }
        int64_t before = rt_dict_len(d);
        rt_clear(d);
        int64_t after = rt_dict_len(d);
        char buf[128];
        snprintf(buf, sizeof(buf), "len %lld -> %lld (want 5 -> 0)",
                 (long long)before, (long long)after);
        report("C1 dict receiver clears", before == 5 && after == 0, buf);
    }

    /* ---- C2: an ARRAY receiver must take the ARRAY arm, never the dict arm. */
    {
        SplArray* a = rt_array_new(0);
        for (int i = 0; i < 6; i++) rt_array_push(a, rt_value_int(i));
        RtCoreArray* base = rt_core_array_ptr(a);
        int64_t recv = (int64_t)(((uint64_t)(uintptr_t)base) | RT_VALUE_TAG_HEAP);
        int dict_admits = rt_core_as_dict(recv) != NULL;
        int64_t len_before = base->len;
        rt_clear(recv);
        int64_t len = base->len;
        char buf[192];
        snprintf(buf, sizeof(buf),
                 "handle=%p base=%p as_dict admits=%d len %lld -> %lld (want 6 -> 0)",
                 (void*)a, (void*)base, dict_admits,
                 (long long)len_before, (long long)len);
        report("C2 array receiver: dict arm NOT taken", !dict_admits && len_before == 6 && len == 0, buf);
    }

    /* ---- C3..C5: registered NON-dict heap objects must not be admitted as
     * dicts. This is the census the brief asks for: every kind that shares the
     * one immortal-pointer registry. Each records the OBSERVED kind byte. ---- */
    {
        struct { const char* name; int64_t recv; uint32_t want_kind; } cases[3];
        int n = 0;
        cases[n].name = "C3 wide-int (RT_VALUE_HEAP_INT)";
        cases[n].recv = rt_value_int_wide((int64_t)1 << 62);
        cases[n].want_kind = RT_VALUE_HEAP_INT; n++;
        cases[n].name = "C4 boxed u64 (RT_VALUE_HEAP_UINT)";
        cases[n].recv = rt_value_u64(-1);
        cases[n].want_kind = RT_VALUE_HEAP_UINT; n++;
        cases[n].name = "C5 heap float (RT_VALUE_HEAP_FLOAT)";
        cases[n].recv = rt_value_float(1.5);
        cases[n].want_kind = RT_VALUE_HEAP_FLOAT; n++;

        for (int i = 0; i < n; i++) {
            int64_t recv = cases[i].recv;
            char buf[192];
            if ((((uintptr_t)recv) & RT_VALUE_TAG_MASK) != RT_VALUE_TAG_HEAP) {
                snprintf(buf, sizeof(buf), "not heap-tagged (degraded to tagged int) - vacuous");
                report(cases[i].name, 0, buf);
                continue;
            }
            void* p = (void*)(((uintptr_t)recv) & ~RT_VALUE_TAG_MASK);
            uint32_t kind = rt_core_registered_object_kind(p);
            int registered = rt_core_is_registered_immortal_ptr(p);
            int dict_pred = rt_core_is_registered_dict((RtCoreDict*)p);
            int admits = rt_core_as_dict(recv) != NULL;
            snprintf(buf, sizeof(buf),
                     "kind=0x%08x byte0=0x%02x registered=%d is_registered_dict=%d as_dict=%d",
                     kind, *(uint8_t*)p, registered, dict_pred, admits);
            /* The load-bearing assertion is as_dict==0. is_registered_dict is
             * ALLOWED to say 1 today (it is registry-only); what must never
             * happen is the dict ARM being entered. */
            report(cases[i].name, !admits, buf);
        }
    }

    /* ---- C6: a non-collection receiver must stay LOUD (fail-closed).
     * Before 8510a8368ca2 this exited 70 via rt_refuse_non_text_receiver; the
     * dict arm must not have converted it into a silent no-op. ---- */
    {
        extern void body_loud_receiver(void);
        int rc = run_isolated(body_loud_receiver);
        char buf[128];
        snprintf(buf, sizeof(buf), "child rc=%d (want 70 = loud refusal; 0 = SILENT NO-OP defect)", rc);
        report("C6 non-collection receiver stays loud", rc == 70, buf);
    }

    /* ---- C7: the stomped-kind array. Documents the residual mechanism. A
     * stomped kind byte is memory corruption that has ALREADY happened, so this
     * case is descriptive: it records whether the dict arm is entered and what
     * happens next. It is NOT asserted as a pass/fail of the fix. ---- */
    {
        int rc = run_isolated(body_stomped_array);
        char buf[192];
        snprintf(buf, sizeof(buf),
                 "child rc=%d (%s) [descriptive: pre-corrupted kind byte]",
                 rc, rc == 0 ? "survived" : (rc < 0 ? "killed by signal" : "exited"));
        /* Always counted as checked; never counted as a failure, because no
         * predicate fix can distinguish a stomped kind byte from a real dict. */
        report("C7 stomped-kind array (descriptive)", 1, buf);
    }

    if (g_checked == 0) {
        printf("ERROR — nothing was checked\n");
        return 2;
    }
    if (g_failed != 0) {
        printf("FAIL — %d of %d rt_clear receiver-dispatch case(s) failed\n", g_failed, g_checked);
        return 1;
    }
    printf("PASS — %d rt_clear receiver-dispatch case(s) checked\n", g_checked);
    return 0;
}

void body_loud_receiver(void) {
    /* A plain tagged integer: not an array, not a dict, not a string. */
    int64_t recv = (int64_t)((7ULL << 3) | RT_VALUE_TAG_INT);
    rt_clear(recv);
}
