#include "runtime_fork.h"
#include "runtime_memtrack.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Standalone adapter link: production defines these in the embedding runtime. */
int g_memtrack_enabled = 0;
void spl_memtrack_record(void* ptr, int64_t size, const char* tag) {
    (void)ptr; (void)size; (void)tag;
}
void spl_memtrack_unrecord(void* ptr) { (void)ptr; }

int main(void) {
#ifdef _WIN32
    puts("runtime_fork_resource_selfcheck: SKIP (fork unavailable)");
    return 0;
#else
    int64_t pid = rt_fork_child_setup();
    if (pid == 0) {
        const size_t size = 8U * 1024U * 1024U;
        volatile unsigned char* bytes = (volatile unsigned char*)malloc(size);
        if (!bytes) rt_fork_child_exit(2);
        for (size_t offset = 0; offset < size; offset += 4096U) bytes[offset] = 1U;
        rt_fork_child_exit(0);
    }
    if (pid <= 0) {
        fputs("fork setup failed\n", stderr);
        return 1;
    }
    int64_t code = rt_fork_parent_wait(pid, 5000);
    int64_t peak = rt_fork_parent_peak_rss_bytes();
    if (code != 0 || rt_fork_parent_timed_out() || rt_fork_parent_signaled()) {
        fprintf(stderr, "unexpected receipt: code=%lld timeout=%d signal=%d\n",
                (long long)code, rt_fork_parent_timed_out(), rt_fork_parent_signaled());
        return 1;
    }
    if (peak < 4LL * 1024LL * 1024LL) {
        fprintf(stderr, "peak direct-child RSS too small: %lld\n", (long long)peak);
        return 1;
    }
    if (rt_fork_parent_user_cpu_micros() < 0 || rt_fork_parent_system_cpu_micros() < 0) {
        fputs("negative CPU receipt\n", stderr);
        return 1;
    }
    puts("runtime_fork_resource_selfcheck: PASS");
    return 0;
#endif
}
