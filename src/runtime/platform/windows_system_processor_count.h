#ifndef SIMPLE_WINDOWS_SYSTEM_PROCESSOR_COUNT_H
#define SIMPLE_WINDOWS_SYSTEM_PROCESSOR_COUNT_H

#include <windows.h>
#include <stdint.h>

/* System population, not caller affinity or a process admission allowance. */
static int64_t spl_windows_active_processor_count(void) {
    DWORD count = GetActiveProcessorCount(ALL_PROCESSOR_GROUPS);
    return count != 0 ? (int64_t)count : -1;
}

#endif
