#include "../../src/runtime/platform/windows_system_processor_count.h"
#include <stdio.h>

int main(void) {
    SYSTEM_INFO old;
    GROUP_AFFINITY original, single;
    GetSystemInfo(&old);
    int64_t count = spl_windows_active_processor_count();
    if (count <= 0 || count != GetActiveProcessorCount(ALL_PROCESSOR_GROUPS)) return 1;
    if (!GetThreadGroupAffinity(GetCurrentThread(), &original)) return 2;
    single = original;
    single.Mask &= (KAFFINITY)(0 - single.Mask);
    if (!SetThreadGroupAffinity(GetCurrentThread(), &single, NULL)) return 3;
    if (spl_windows_active_processor_count() != count) return 4;
    if (!SetThreadGroupAffinity(GetCurrentThread(), &original, NULL)) return 5;
    printf("PASS old_group=%lu active_system=%lld affinity_independent=1\n",
           old.dwNumberOfProcessors, (long long)count);
    return 0;
}
