/* NEW shared-read capability fixture, source only: NOT_RUN.
 * Uses real Windows opens/sharing/rename/ACL checks. Test-only CloseHandle
 * wrapping injects a genuine unclosed RW handle or a real final-name swap.
 * No production fault switch and no previous private-file campaign rerun. */
#if !defined(_WIN32)
int main(void) {return 77;}
#else
#if !defined(_WIN32_WINNT) || _WIN32_WINNT < 0x0602
#undef _WIN32_WINNT
#define _WIN32_WINNT 0x0602
#endif
#include <windows.h>
#include <aclapi.h>
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <wchar.h>
static HANDLE targeted_stage;
static int close_fault;
static wchar_t swap_final[32768],swap_backup[32768];
static PSECURITY_DESCRIPTOR replacement_security;
static BOOL WINAPI shared_read_test_close(HANDLE handle) {
    if (handle==targeted_stage && close_fault==1) {
        close_fault=0;SetLastError(ERROR_ACCESS_DENIED);return FALSE;
    }
    BOOL ok=CloseHandle(handle);
    if (ok && handle==targeted_stage && close_fault==2) {
        close_fault=0;
        assert(MoveFileExW(swap_final,swap_backup,0));
        SECURITY_ATTRIBUTES attributes={sizeof(attributes),replacement_security,FALSE};
        HANDLE replacement=CreateFileW(swap_final,GENERIC_WRITE,0,&attributes,CREATE_NEW,
            FILE_ATTRIBUTE_NORMAL|FILE_FLAG_OPEN_REPARSE_POINT,NULL);
        DWORD written=0;const char changed[]="changed\n";
        assert(replacement!=INVALID_HANDLE_VALUE && WriteFile(replacement,changed,sizeof(changed)-1,&written,NULL));
        assert(written==sizeof(changed)-1 && FlushFileBuffers(replacement) && CloseHandle(replacement));
    }
    return ok;
}
#define CloseHandle shared_read_test_close
#include "../platform/runtime_windows_private_root.h"
#undef CloseHandle

static int64_t create_stage(int64_t root,const wchar_t* name,const char* bytes) {
    int64_t stage=rt_windows_private_file_v1(root,(int64_t)(intptr_t)name,1,128);
    assert(stage>0 && rt_windows_private_check_v1(stage,128));
    assert(rt_windows_private_file_write_v1(stage,(int64_t)(intptr_t)bytes,(int64_t)strlen(bytes))==(int64_t)strlen(bytes));
    assert(rt_windows_private_file_seal_v1(stage));return stage;
}
static void exact_read(int64_t reader,const char* expected) {
    char bytes[128];int64_t size=rt_windows_private_read_file_size_v2(reader);
    assert(size==(int64_t)strlen(expected));
    assert(rt_windows_private_read_file_read_v2(reader,0,(int64_t)(intptr_t)bytes,size)==size);
    assert(!memcmp(bytes,expected,(size_t)size) && rt_windows_private_read_file_check_v2(reader,128));
}
int main(void) {
    wchar_t root_path[32768];
    DWORD length=GetEnvironmentVariableW(L"SIMPLE_WINDOWS_PRIVATE_READ_EMPTY_ROOT",root_path,32768);
    if (!length || length>=32000) {fputs("NOT_RUN: fresh installed private root required\n",stderr);return 77;}
    int64_t writer=rt_windows_private_root_open_v1((int64_t)(intptr_t)root_path);
    int64_t first_root=rt_windows_private_read_root_open_v2((int64_t)(intptr_t)root_path);
    int64_t second_root=rt_windows_private_read_root_open_v2((int64_t)(intptr_t)root_path);
    assert(writer>0 && first_root>0 && second_root>0);
    assert(rt_windows_private_read_root_ready_v2(first_root) && rt_windows_private_read_root_ready_v2(second_root));
    assert(rt_windows_private_file_v1(first_root,(int64_t)(intptr_t)L"cast-must-not-create",1,128)==-1);
    int64_t retained[9],reopened[9];wchar_t final[64];
    for (int index=0;index<9;index++) {
        wchar_t stage_name[64];char bytes[64];
        swprintf(stage_name,64,L"shared-stage-%d.sdn",index);swprintf(final,64,L"shared-final-%d.sdn",index);
        snprintf(bytes,sizeof(bytes),"artifact-%d\n",index);
        int64_t stage=create_stage(writer,stage_name,bytes),out[3]={0};
        assert(rt_windows_private_publish_shared_read_v2(writer,stage,(int64_t)(intptr_t)final,(int64_t)(intptr_t)out)==0);
        assert(out[0]>0 && out[1]==0 && out[2]==1);retained[index]=out[0];
        /* Old copied stage and forged V1 views cannot regain mutation or close
         * the new readonly generation, even though its numeric token is equal. */
        assert(rt_windows_private_file_write_v1(stage,(int64_t)(intptr_t)"x",1)==-1);
        assert(!rt_windows_private_file_seal_v1(stage) && !rt_windows_private_file_close_v1(stage));
        assert(rt_windows_private_publish_v1(writer,retained[index],(int64_t)(intptr_t)L"must-not-move")==-1);
        DWORD written=0;
        assert(!WriteFile((HANDLE)wp_find_v1(retained[index],4)->owner,"x",1,&written,NULL));
        reopened[index]=rt_windows_private_read_file_open_v2(second_root,(int64_t)(intptr_t)final,128);
        assert(reopened[index]>0);exact_read(retained[index],bytes);exact_read(reopened[index],bytes);
    }
    int64_t collision=create_stage(writer,L"collision-stage.sdn","other\n"),out[3]={0};
    assert(rt_windows_private_publish_shared_read_v2(writer,collision,(int64_t)(intptr_t)L"shared-final-0.sdn",(int64_t)(intptr_t)out)==1);
    assert(out[0]==0 && out[1]==collision && out[2]==0);
    assert(rt_windows_private_file_close_v1(collision));exact_read(retained[0],"artifact-0\n");

    int64_t failed=create_stage(writer,L"failed-close-stage.sdn","close\n");
    targeted_stage=(HANDLE)wp_find_v1(failed,2)->owner;close_fault=1;
    assert(rt_windows_private_publish_shared_read_v2(writer,failed,(int64_t)(intptr_t)L"failed-close-final.sdn",(int64_t)(intptr_t)out)==-1);
    assert(out[0]==0 && out[1]==failed && out[2]==1);
    assert(rt_windows_private_file_write_v1(failed,(int64_t)(intptr_t)"x",1)==-1);
    assert(rt_windows_private_file_close_v1(failed));targeted_stage=NULL;
    int64_t after_close=rt_windows_private_read_file_open_v2(first_root,(int64_t)(intptr_t)L"failed-close-final.sdn",128);
    assert(after_close>0);exact_read(after_close,"close\n");assert(rt_windows_private_read_file_close_v2(after_close));

    int64_t swapped=create_stage(writer,L"swap-stage.sdn","original\n");
    targeted_stage=(HANDLE)wp_find_v1(swapped,2)->owner;
    assert(GetSecurityInfo(targeted_stage,SE_FILE_OBJECT,OWNER_SECURITY_INFORMATION|DACL_SECURITY_INFORMATION,
        NULL,NULL,NULL,NULL,&replacement_security)==ERROR_SUCCESS && replacement_security);
    swprintf(swap_final,32768,L"%ls\\swap-final.sdn",root_path);
    swprintf(swap_backup,32768,L"%ls\\swap-original.sdn",root_path);close_fault=2;
    assert(rt_windows_private_publish_shared_read_v2(writer,swapped,(int64_t)(intptr_t)L"swap-final.sdn",(int64_t)(intptr_t)out)==-1);
    assert(out[0]>0 && out[1]==0 && out[2]==1);
    assert(!rt_windows_private_read_file_check_v2(out[0],128));
    assert(rt_windows_private_read_file_close_v2(out[0]));
    assert(LocalFree(replacement_security)==NULL);targeted_stage=NULL;
    for (int index=0;index<9;index++) {
        assert(rt_windows_private_read_file_close_v2(reopened[index]));
        assert(rt_windows_private_read_file_close_v2(retained[index]));
    }
    assert(rt_windows_private_read_root_close_v2(second_root));
    assert(rt_windows_private_read_root_close_v2(first_root));
    assert(rt_windows_private_root_close_v1(writer));return 0;
}
#endif
