#define _WIN32_WINNT 0x0A00
#define PSAPI_VERSION 1
#include <windows.h>
#include <pdh.h>
#include <powrprof.h>
#include <psapi.h>
#include <lmcons.h>
#include <lmaccess.h>
#include <lmapibuf.h>
#include <stdio.h>

static FARPROC volatile imported_functions[] = {
    (FARPROC)PdhAddEnglishCounterA,
    (FARPROC)PdhAddEnglishCounterW,
    (FARPROC)PdhCloseQuery,
    (FARPROC)PdhCollectQueryData,
    (FARPROC)PdhCollectQueryDataEx,
    (FARPROC)PdhGetFormattedCounterValue,
    (FARPROC)PdhOpenQueryA,
    (FARPROC)PdhRemoveCounter,
    (FARPROC)CallNtPowerInformation,
    (FARPROC)GetModuleFileNameExW,
    (FARPROC)NetApiBufferFree,
    (FARPROC)NetGroupEnum,
    (FARPROC)NetGroupGetInfo,
    (FARPROC)NetUserEnum,
    (FARPROC)NetUserGetInfo,
    (FARPROC)NetUserGetLocalGroups
};

int main(void) {
    unsigned count = (unsigned)(sizeof(imported_functions) / sizeof(imported_functions[0]));
    if (count != 16) return 40;
    for (unsigned i = 0; i < count; ++i) if (!imported_functions[i]) return 41;
    printf("sdk-imports=%u\n", count);
    return 0;
}
