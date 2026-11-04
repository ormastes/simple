/* Owner-attribution report self-check for the native-C guard-page allocator
 * (bug mem_guard_owner_attribution_trap_report_missing_2026-08-05).
 *
 * Part 1 (all hosts): drives rt_mem_guard_record_slot + rt_mem_guard_fault_report
 * directly, asserting classification (underflow/overflow/use-after-free), size
 * and the alloc-time owner tag, and that a non-guard address yields no report.
 * Part 2 (POSIX only): forks a child that really overflows a sampled slot with
 * stderr piped to the parent, and asserts the PRINTED report names the owner
 * and size and that the child still dies by SIGSEGV (signal not swallowed).
 */
#include <stdio.h>
#include <string.h>
#include "../runtime_memory_guard.h"
#if !defined(_WIN32)
#include <sys/wait.h>
#endif

static int failures = 0;
static void check(int c, const char* m) {
    printf("  %s %s\n", c ? "ok  " : "FAIL", m);
    if (!c) failures++;
}

int main(void) {
    char buf[RT_MEM_GUARD_REPORT_MAX];
    /* Fake slot layout: 4 pages, [guard][data][data][guard]. */
    static uint8_t fake[4 * 4096];
    uint8_t* page_base = fake;
    uint8_t* user = fake + 3 * 4096 - 100; /* right-aligned, size 100 */

    rt_mem_guard_set_owner("parser.lexer", 12);
    size_t idx = rt_mem_guard_record_slot(user, page_base, 4, 100);
    check(idx != RT_MEM_GUARD_MAX_SLOTS, "slot recorded");

    size_t n = rt_mem_guard_fault_report((uintptr_t)(fake + 3 * 4096 + 5), buf, sizeof(buf));
    check(n > 0 && strstr(buf, "overflow") != NULL, "trailing guard page -> overflow");
    check(strstr(buf, "owner=parser.lexer") != NULL, "report names the owner");
    check(strstr(buf, "size=100") != NULL, "report names the size");

    n = rt_mem_guard_fault_report((uintptr_t)(fake + 10), buf, sizeof(buf));
    check(n > 0 && strstr(buf, "underflow") != NULL, "leading guard page -> underflow");

    rt_mem_guard_slots[idx].freed = 1;
    n = rt_mem_guard_fault_report((uintptr_t)(fake + 4096 + 3), buf, sizeof(buf));
    check(n > 0 && strstr(buf, "use-after-free") != NULL, "freed slot -> use-after-free");

    n = rt_mem_guard_fault_report((uintptr_t)0x10, buf, sizeof(buf));
    check(n == 0, "non-guard address produces no report");

    rt_mem_guard_slots[idx].user_ptr = NULL;
    rt_mem_guard_set_owner(NULL, 0);
    idx = rt_mem_guard_record_slot(user, page_base, 4, 7);
    n = rt_mem_guard_fault_report((uintptr_t)(fake + 3 * 4096), buf, sizeof(buf));
    check(n > 0 && strstr(buf, "owner=<none>") != NULL, "unset owner reports <none>");
    rt_mem_guard_slots[idx].user_ptr = NULL;

#if !defined(_WIN32)
    setenv("SIMPLE_MEM_GUARD_RATE", "1", 1);
    int fds[2];
    if (pipe(fds) == 0) {
        pid_t pid = fork();
        if (pid == 0) {
            dup2(fds[1], 2);
            close(fds[0]);
            rt_mem_guard_set_owner("e2e.owner", 9);
            uint8_t* p = rt_mem_guard_alloc_sampled(37);
            if (p == NULL) _exit(3);
            ((volatile uint8_t*)p)[37] = 1; /* overflow onto trailing guard */
            _exit(0);
        }
        close(fds[1]);
        char out[512];
        ssize_t got = read(fds[0], out, sizeof(out) - 1);
        out[got > 0 ? got : 0] = '\0';
        int status = 0;
        waitpid(pid, &status, 0);
        check(WIFSIGNALED(status) && WTERMSIG(status) == SIGSEGV, "child still dies by SIGSEGV");
        check(strstr(out, "overflow") && strstr(out, "owner=e2e.owner") && strstr(out, "size=37"),
              "printed trap report has class, owner and size");
    }
#endif
    if (failures) { printf("SELFCHECK FAILED (%d)\n", failures); return 1; }
    printf("SELFCHECK PASSED\n");
    return 0;
}
