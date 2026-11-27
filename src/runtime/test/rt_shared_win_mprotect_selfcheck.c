/* Selfcheck for the shared Windows page-protection helpers in
 * platform/windows_raw_mapping.h (prot -> PAGE_* ladder and mprotect body used
 * by platform_win.h and runtime_legacy_core.c). Windows-only; no runtime link.
 * clang -std=gnu11 -O1 -o rt_shared_win_mprotect.exe src/runtime/test/rt_shared_win_mprotect_selfcheck.c */
#include "../platform/windows_raw_mapping.h"
#include <stdio.h>

static int fails;
#define CHECK(c) do { if (!(c)) { printf("FAIL line %d: %s\n", __LINE__, #c); fails++; } } while (0)

int main(void) {
    DWORD p = 0;
    CHECK(rt__shared_win_prot_to_page(0x0, &p) && p == PAGE_NOACCESS);
    CHECK(rt__shared_win_prot_to_page(0x1, &p) && p == PAGE_READONLY);
    CHECK(rt__shared_win_prot_to_page(0x2, &p) && p == PAGE_READWRITE);
    CHECK(rt__shared_win_prot_to_page(0x3, &p) && p == PAGE_READWRITE);
    CHECK(rt__shared_win_prot_to_page(0x4, &p) && p == PAGE_EXECUTE);
    CHECK(rt__shared_win_prot_to_page(0x5, &p) && p == PAGE_EXECUTE_READ);
    CHECK(!rt__shared_win_prot_to_page(0x6, &p) && !rt__shared_win_prot_to_page(0x7, &p));
    CHECK(!rt__shared_win_prot_to_page(0x8, &p) && !rt__shared_win_prot_to_page(-1, &p));

    int64_t region = spl_windows_mmap_raw(0, 4096, 0x3, 0x22, -1, 0);
    CHECK(region != -1);
    CHECK(spl_windows_mprotect_raw(0, 4096, 0x1) == -1);       /* null addr */
    CHECK(spl_windows_mprotect_raw(region, 0, 0x1) == -1);     /* empty length */
    CHECK(spl_windows_mprotect_raw(region, 4096, 0x6) == -1);  /* W+X refused */
    CHECK(spl_windows_mprotect_raw(region, 4096, 0x8) == -1);  /* unknown bit */
    CHECK(spl_windows_mprotect_raw(region, 4096, 0x1) == 0);
    MEMORY_BASIC_INFORMATION info;
    CHECK(VirtualQuery((void*)(uintptr_t)region, &info, sizeof(info)) != 0 && info.Protect == PAGE_READONLY);
    CHECK(spl_windows_mprotect_raw(region, 4096, 0x5) == 0);
    CHECK(VirtualQuery((void*)(uintptr_t)region, &info, sizeof(info)) != 0 && info.Protect == PAGE_EXECUTE_READ);
    CHECK(spl_windows_mprotect_raw(region, 4096, 0x3) == 0);
    CHECK(VirtualQuery((void*)(uintptr_t)region, &info, sizeof(info)) != 0 && info.Protect == PAGE_READWRITE);

    printf(fails ? "rt_shared_win_mprotect_selfcheck FAIL\n" : "rt_shared_win_mprotect_selfcheck PASS\n");
    return fails != 0;
}
