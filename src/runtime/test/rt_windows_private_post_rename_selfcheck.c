/* Actual Windows fixture, NOT_RUN without an installed empty private root.
 * Test-only wrappers inject a failed security query after a REAL successful
 * kernel rename. The production provider has no fault flag or bypass. */
#if !defined(_WIN32)
int main(void) { return 77; }
#else
#if !defined(_WIN32_WINNT) || _WIN32_WINNT < 0x0602
#undef _WIN32_WINNT
#define _WIN32_WINNT 0x0602
#endif
#include <windows.h>
#include <aclapi.h>
#include <stdio.h>
#include <string.h>
#include <wchar.h>
static int inject_after_rename;
static int observed_real_rename;
static BOOL WINAPI private_test_rename(HANDLE file,FILE_INFO_BY_HANDLE_CLASS kind,LPVOID data,DWORD size) {
    BOOL ok=SetFileInformationByHandle(file,kind,data,size);
    if (ok && kind==FileRenameInfo) {observed_real_rename=1;inject_after_rename=1;}
    return ok;
}
static DWORD WINAPI private_test_security(HANDLE handle,SE_OBJECT_TYPE type,SECURITY_INFORMATION info,
        PSID *owner,PSID *group,PACL *dacl,PACL *sacl,PSECURITY_DESCRIPTOR *descriptor) {
    if (inject_after_rename) {
        inject_after_rename=0;
        if (descriptor) *descriptor=NULL;
        return ERROR_ACCESS_DENIED;
    }
    return GetSecurityInfo(handle,type,info,owner,group,dacl,sacl,descriptor);
}
#define SetFileInformationByHandle private_test_rename
#define GetSecurityInfo private_test_security
#include "../platform/runtime_windows_private_root.h"
#undef SetFileInformationByHandle
#undef GetSecurityInfo

int main(void) {
    wchar_t path[32768],final[32768],retry[32768];
    DWORD length=GetEnvironmentVariableW(L"SIMPLE_WINDOWS_PRIVATE_EMPTY_ROOT",path,32768);
    if (!length || length>=32700) {fputs("NOT_RUN: installed private root required\n",stderr);return 77;}
    int64_t root=rt_windows_private_root_open_v1((int64_t)(intptr_t)path);
    if (root==-1 || !rt_windows_private_root_ready_v1(root)) {
        if (root!=-1 && !rt_windows_private_root_close_v1(root))
            fputs("FAIL: root cleanup still required\n",stderr);
        fputs("FAIL: root admission\n",stderr);return 1;
    }
    int64_t file=rt_windows_private_file_v1(root,(int64_t)(intptr_t)L"fault-stage.sdn",1,64);
    const char bytes[]="receipt\n";int failed=0;
    if (file==-1 || !rt_windows_private_check_v1(file,64) ||
        rt_windows_private_file_write_v1(file,(int64_t)(intptr_t)bytes,sizeof(bytes)-1)!=(int64_t)sizeof(bytes)-1 ||
        !rt_windows_private_file_seal_v1(file)) failed=1;
    if (!failed) {
        int64_t first=rt_windows_private_publish_v1(root,file,(int64_t)(intptr_t)L"fault-final.sdn");
        int64_t second=rt_windows_private_publish_v1(root,file,(int64_t)(intptr_t)L"fault-republish.sdn");
        swprintf(final,32768,L"%ls\\fault-final.sdn",path);
        swprintf(retry,32768,L"%ls\\fault-republish.sdn",path);
        failed=first!=-1 || !observed_real_rename || second!=-1 ||
            GetFileAttributesW(final)==INVALID_FILE_ATTRIBUTES ||
            GetFileAttributesW(retry)!=INVALID_FILE_ATTRIBUTES;
    }
    if (file!=-1 && !rt_windows_private_file_close_v1(file)) failed=1;
    if (!rt_windows_private_root_close_v1(root)) failed=1;
    if (failed) fputs("FAIL: post-rename error must consume publication\n",stderr);
    return failed;
}
#endif
