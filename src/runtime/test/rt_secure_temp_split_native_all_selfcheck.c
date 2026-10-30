/* Link this fixture against the NEW real libsimple_native_all.a, not fake
 * rt_string_* functions. It tests actual Rust boxed text and Windows OS state.
 * UNRUN. No passing result is implied by this source. */
#include "../runtime.h"
#include <windows.h>
#include <aclapi.h>
#include <sddl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define WORKERS 24
#define PATH_BYTES 4096
static char created[128][PATH_BYTES];
static int created_count;
static LONG assertions;

static void require(int condition, const char* message) {
    if (!condition) { fprintf(stderr, "FAIL: %s\n", message); exit(1); }
    assertions++;
}
static int64_t boxed(const char* value) {
    return rt_string_new((const uint8_t*)value, (uint64_t)strlen(value));
}
static void unbox(int64_t value, char* out) {
    int64_t length = rt_string_len(value);
    require(length > 0 && length < PATH_BYTES, "OS creation must return real boxed path");
    const uint8_t* bytes = rt_string_data(value);
    require(bytes != NULL && memchr(bytes, 0, (size_t)length) == NULL, "boxed path bytes");
    memcpy(out, bytes, (size_t)length); out[length] = 0;
}
static void wide_path(const char* path, wchar_t* out) {
    wchar_t plain[32768];
    require(MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, path, -1,
                              plain, 32768) > 0, "UTF-8 path conversion");
    require(plain[0] != 0 && plain[1] == L':', "fixture requires absolute local drive path");
    require(wcslen(plain) + 5 < 32768, "extended path bound");
    wcscpy(out, L"\\\\?\\"); wcscat(out, plain);
}
static void remember(const char* path) {
    require(created_count < 128, "fixture cleanup inventory bound");
    strcpy(created[created_count++], path);
}
static void real_private_directory(const char* path) {
    wchar_t wide[32768]; wide_path(path, wide);
    DWORD attributes = GetFileAttributesW(wide);
    require(attributes != INVALID_FILE_ATTRIBUTES &&
            (attributes & FILE_ATTRIBUTE_DIRECTORY) &&
            !(attributes & FILE_ATTRIBUTE_REPARSE_POINT), "real non-reparse directory");
    PACL dacl = NULL; PSECURITY_DESCRIPTOR descriptor = NULL;
    require(GetNamedSecurityInfoW(wide, SE_FILE_OBJECT, DACL_SECURITY_INFORMATION,
            NULL, NULL, &dacl, NULL, &descriptor) == ERROR_SUCCESS, "read real directory ACL");
    SECURITY_DESCRIPTOR_CONTROL control; DWORD revision;
    require(GetSecurityDescriptorControl(descriptor, &control, &revision) &&
            (control & SE_DACL_PROTECTED), "directory ACL must be protected");
    require(dacl != NULL && dacl->AceCount == 2, "only SYSTEM and owner-rights grants");
    int system = 0, owner = 0;
    for (DWORD i = 0; i < dacl->AceCount; i++) {
        ACCESS_ALLOWED_ACE* ace = NULL;
        require(GetAce(dacl, i, (void**)&ace) &&
                ace->Header.AceType == ACCESS_ALLOWED_ACE_TYPE, "allowed ACL entry");
        require((ace->Mask & FILE_ALL_ACCESS) == FILE_ALL_ACCESS, "full owner/SYSTEM directory grant");
        LPSTR sid = NULL;
        require(ConvertSidToStringSidA(&ace->SidStart, &sid), "ACL SID conversion");
        if (strcmp(sid, "S-1-5-18") == 0) system++;
        else if (strcmp(sid, "S-1-3-4") == 0) owner++;
        else require(0, "unexpected directory ACL principal");
        LocalFree(sid);
    }
    require(system == 1 && owner == 1, "SYSTEM and owner-rights ACL identities");
    LocalFree(descriptor);
}
static void make_pair(const char* parent, const char* prefix, char* output) {
    require(rt_secure_temp_dir_set_parent(boxed(parent)) == 1, "boxed parent accepted");
    require(rt_secure_temp_dir_set_prefix(boxed(prefix)) == 1, "boxed prefix accepted");
    unbox(rt_secure_temp_dir_make(), output);
    require(strncmp(output, parent, strlen(parent)) == 0 &&
            output[strlen(parent)] == '\\', "child stays under supplied parent spelling");
    require(strncmp(output + strlen(parent) + 1, prefix, strlen(prefix)) == 0 &&
            output[strlen(parent) + 1 + strlen(prefix)] == '-', "child uses this exact prefix");
    real_private_directory(output); remember(output);
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "successful make consumed both slots");
}

typedef struct ThreadCase {
    const char* parent;
    HANDLE ready, release;
    char prefix[32], output[PATH_BYTES];
    int ok;
} ThreadCase;
static DWORD WINAPI tls_case(void* parameter) {
    ThreadCase* value = (ThreadCase*)parameter;
    int parent_ok = rt_secure_temp_dir_set_parent(boxed(value->parent)) == 1;
    int prefix_ok = rt_secure_temp_dir_set_prefix(boxed(value->prefix)) == 1;
    ReleaseSemaphore(value->ready, 1, NULL);
    if (WaitForSingleObject(value->release, 30000) != WAIT_OBJECT_0) return 1;
    if (!parent_ok || !prefix_ok) return 1;
    int64_t made = rt_secure_temp_dir_make();
    int64_t length = rt_string_len(made);
    if (length <= 0 || length >= PATH_BYTES) return 1;
    const uint8_t* bytes = rt_string_data(made);
    if (!bytes) return 1;
    memcpy(value->output, bytes, (size_t)length); value->output[length] = 0;
    const char* leaf = strrchr(value->output, '\\');
    value->ok = strncmp(value->output, value->parent, strlen(value->parent)) == 0 &&
        value->output[strlen(value->parent)] == '\\' &&
        leaf && strncmp(leaf + 1, value->prefix, strlen(value->prefix)) == 0 &&
        leaf[1 + strlen(value->prefix)] == '-' && rt_string_len(rt_secure_temp_dir_make()) == 0;
    return value->ok ? 0 : 1;
}

int main(void) {
    wchar_t temporary[32768]; char temporary_utf8[PATH_BYTES], root[PATH_BYTES];
    DWORD count = GetTempPathW(32768, temporary);
    require(count > 0 && count < 32768, "existing Windows temporary parent");
    require(WideCharToMultiByte(CP_UTF8, 0, temporary, -1, temporary_utf8,
                               PATH_BYTES, NULL, NULL) > 0, "temporary parent UTF-8");
    size_t temporary_length = strlen(temporary_utf8);
    while (temporary_length > 3 && temporary_utf8[temporary_length - 1] == '\\')
        temporary_utf8[--temporary_length] = 0;
    const char* fixture_prefix = "simple-split-native-all";
    unbox(rt_secure_temp_dir((const uint8_t*)temporary_utf8, temporary_length,
            (const uint8_t*)fixture_prefix, strlen(fixture_prefix)), root);
    real_private_directory(root); remember(root);

    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "empty pair refused");
    require(rt_secure_temp_dir_set_parent(boxed(root)) == 1, "parent-only setup");
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "missing prefix refused and consumed");
    require(rt_secure_temp_dir_set_prefix(boxed("orphan")) == 1, "prefix-only setup");
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "previous parent was consumed");
    require(rt_secure_temp_dir_set_parent(boxed("")) == 0, "empty parent refused");
    require(rt_secure_temp_dir_set_prefix(boxed("")) == 0, "empty prefix refused");
    require(rt_secure_temp_dir_set_prefix(boxed("bad/name")) == 0, "slash prefix refused");
    require(rt_secure_temp_dir_set_prefix(boxed("bad\\name")) == 0, "backslash prefix refused");
    const uint8_t nul_path[] = {'x', 0, 'y'};
    require(rt_secure_temp_dir_set_parent(rt_string_new(nul_path, 3)) == 0, "embedded NUL parent refused");
    require(rt_secure_temp_dir_set_prefix(rt_string_new(nul_path, 3)) == 0, "embedded NUL prefix refused");
    char oversized[4096]; memset(oversized, 'x', sizeof(oversized));
    require(rt_secure_temp_dir_set_parent(rt_string_new((uint8_t*)oversized, sizeof(oversized))) == 0,
            "parent slot bound enforced");
    require(rt_secure_temp_dir_set_prefix(rt_string_new((uint8_t*)oversized, 128)) == 0,
            "prefix slot bound enforced");
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "invalid sequence has no complete pair");
    require(rt_secure_temp_dir_set_parent(boxed(root)) == 1 &&
            rt_secure_temp_dir_set_prefix(boxed("stale-parent")) == 1, "valid pair before rejected parent");
    require(rt_secure_temp_dir_set_parent(boxed("")) == 0, "replacement parent refused");
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "rejected replacement clears prior parent");
    require(rt_secure_temp_dir_set_parent(boxed(root)) == 1 &&
            rt_secure_temp_dir_set_prefix(boxed("stale-prefix")) == 1, "valid pair before rejected prefix");
    require(rt_secure_temp_dir_set_prefix(boxed("bad/name")) == 0, "replacement prefix refused");
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "rejected replacement clears prior prefix");

    char first[PATH_BYTES], second[PATH_BYTES];
    make_pair(root, "same", first); make_pair(root, "same", second);
    require(strcmp(first, second) != 0, "exclusive random child names differ");
    char missing[PATH_BYTES]; snprintf(missing, sizeof(missing), "%s\\absent-parent", root);
    require(rt_secure_temp_dir_set_parent(boxed(missing)) == 1 &&
            rt_secure_temp_dir_set_prefix(boxed("no-child")) == 1, "OS refusal setup");
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "missing OS parent refused");
    require(rt_string_len(rt_secure_temp_dir_make()) == 0, "OS failure consumed both slots");

    char parent[PATH_BYTES], child[PATH_BYTES]; strcpy(parent, root);
    for (int i = 0; i < 5; i++) {
        make_pair(parent, "unicode_\xce\xb4_long_component", child);
        strcpy(parent, child);
    }
    require(strlen(parent) > 260, "real Unicode directory created beyond MAX_PATH");

    HANDLE ready = CreateSemaphoreW(NULL, 0, WORKERS, NULL);
    HANDLE release = CreateEventW(NULL, TRUE, FALSE, NULL);
    require(ready != NULL && release != NULL, "TLS test synchronization");
    ThreadCase cases[WORKERS]; HANDLE threads[WORKERS];
    char tls_parents[WORKERS][PATH_BYTES];
    for (int i = 0; i < WORKERS; i++) {
        char parent_prefix[32];
        snprintf(parent_prefix, sizeof(parent_prefix), "tls-parent-%02d", i);
        make_pair(root, parent_prefix, tls_parents[i]);
        memset(&cases[i], 0, sizeof(cases[i]));
        cases[i].parent = tls_parents[i]; cases[i].ready = ready; cases[i].release = release;
        snprintf(cases[i].prefix, sizeof(cases[i].prefix), "thread-%02d", i);
        threads[i] = CreateThread(NULL, 0, tls_case, &cases[i], 0, NULL);
        require(threads[i] != NULL, "start actual TLS worker");
    }
    for (int i = 0; i < WORKERS; i++)
        require(WaitForSingleObject(ready, 30000) == WAIT_OBJECT_0, "all 24 TLS pairs ready");
    require(SetEvent(release), "release actual concurrent makes");
    require(WaitForMultipleObjects(WORKERS, threads, TRUE, 30000) == WAIT_OBJECT_0,
            "all 24 TLS workers terminate");
    for (int i = 0; i < WORKERS; i++) {
        DWORD status; require(GetExitCodeThread(threads[i], &status) && status == 0 && cases[i].ok,
                              "thread-local pair preserved during interleaving");
        real_private_directory(cases[i].output); remember(cases[i].output);
        CloseHandle(threads[i]);
    }
    CloseHandle(ready); CloseHandle(release);
    for (int i = created_count - 1; i >= 0; i--) {
        wchar_t path[32768]; wide_path(created[i], path);
        require(RemoveDirectoryW(path), "remove actual fixture directory");
    }
    printf("secure-temp-split: assertions=%ld tls_workers=24\n", assertions);
    return 0;
}
