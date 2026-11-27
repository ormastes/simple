#include "src/runtime/platform/runtime_windows_private_atomic.h"
#if defined(_WIN32)
#include <aclapi.h>
#include <sddl.h>
#include <assert.h>

#define CHECK(test) do { if (!(test)) { fprintf(stderr, "private atomic check failed at line %d: %s (winerr=%lu)\n", __LINE__, #test, (unsigned long)GetLastError()); return 1; } } while (0)
static int private_acl(const wchar_t *path) {
    PSECURITY_DESCRIPTOR descriptor = NULL;
    PACL dacl = NULL;
    DWORD result = GetNamedSecurityInfoW((LPWSTR)path, SE_FILE_OBJECT,
        DACL_SECURITY_INFORMATION, NULL, NULL, &dacl, NULL, &descriptor);
    if (result != ERROR_SUCCESS || !descriptor || !dacl) return 0;
    SECURITY_DESCRIPTOR_CONTROL control = 0;
    DWORD revision = 0;
    int ok = GetSecurityDescriptorControl(descriptor, &control, &revision) &&
        (control & SE_DACL_PROTECTED) != 0 && dacl->AceCount > 0;
    for (DWORD i = 0; ok && i < dacl->AceCount; i++) {
        ACCESS_ALLOWED_ACE *ace = NULL;
        LPWSTR sid = NULL;
        ok = GetAce(dacl, i, (LPVOID *)&ace) && ace->Header.AceType == ACCESS_ALLOWED_ACE_TYPE &&
            !(ace->Header.AceFlags & INHERITED_ACE) &&
            ConvertSidToStringSidW((PSID)&ace->SidStart, &sid);
        if (ok) ok = wcscmp(sid, L"S-1-3-4") == 0 || wcscmp(sid, L"S-1-5-18") == 0;
        if (sid) LocalFree(sid);
    }
    LocalFree(descriptor);
    return ok;
}
int main(void) {
    char parent[MAX_PATH], directory[MAX_PATH], path[MAX_PATH];
    CHECK(GetTempPathA(sizeof(parent), parent) != 0);
    CHECK(snprintf(directory, sizeof(directory), "%sdevhub-atomic-acl-%lu", parent,
        (unsigned long)GetCurrentProcessId()) > 0);
    CHECK(CreateDirectoryA(directory, NULL));
    CHECK(snprintf(path, sizeof(path), "%s\\token.txt", directory) > 0);
    /* Replace a pre-existing inherited-ACL file, not just a fresh target. */
    FILE *inherited = fopen(path, "wb");
    CHECK(inherited != NULL && fputs("old public value", inherited) >= 0 && fclose(inherited) == 0);
    CHECK(rt_win_private_atomic_write(path, (const unsigned char *)"first synthetic token", strlen("first synthetic token"), 0600) == 1);
    wchar_t *wide = rt_widen_long_path_rc(path);
    CHECK(wide != NULL);
    CHECK(private_acl(wide));
    CHECK(rt_win_private_atomic_write(path, (const unsigned char *)"second synthetic token", strlen("second synthetic token"), 0600) == 1);
    CHECK(private_acl(wide));
    FILE *file = fopen(path, "rb");
    CHECK(file != NULL);
    char bytes[64] = {0};
    CHECK(fread(bytes, 1, sizeof(bytes), file) == strlen("second synthetic token"));
    CHECK(fclose(file) == 0 && strcmp(bytes, "second synthetic token") == 0);
    CHECK(rt_win_private_atomic_write(path, (const unsigned char *)"refused", 7, 0644) == 0);
    CHECK(rt_win_private_atomic_write("", (const unsigned char *)"refused", 7, 0600) == 0);
    CHECK(rt_win_private_atomic_write(directory, (const unsigned char *)"refused", 7, 0600) == 0);
    char pattern[MAX_PATH];
    snprintf(pattern, sizeof(pattern), "%s.tmp.*", path);
    WIN32_FIND_DATAA found;
    HANDLE search = FindFirstFileA(pattern, &found);
    CHECK(search == INVALID_HANDLE_VALUE);
    snprintf(pattern, sizeof(pattern), "%s.tmp.*", directory);
    search = FindFirstFileA(pattern, &found);
    CHECK(search == INVALID_HANDLE_VALUE);
    CHECK(DeleteFileW(wide));
    free(wide);
    CHECK(RemoveDirectoryA(directory));
    puts("PASS actual C atomic mode0600 protected ACL, replacement, content, refusal, cleanup");
    return 0;
}
#else
int main(void) { return 77; }
#endif
