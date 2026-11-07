/* Handle-relative private journal leaf. No pathname-based publication, chmod
 * admission, ACL repair, or replacement of a colliding journal entry. */
#ifndef SIMPLE_WINDOWS_PRIVATE_ROOT_V1_H
#define SIMPLE_WINDOWS_PRIVATE_ROOT_V1_H
#include <stdint.h>
#if defined(_WIN32)
#include <windows.h>
#include <winternl.h>
#include <aclapi.h>
#include <stdlib.h>
#include <wchar.h>
#include <stddef.h>

typedef NTSTATUS (NTAPI *WpCreateV1)(PHANDLE,ACCESS_MASK,POBJECT_ATTRIBUTES,
    PIO_STATUS_BLOCK,PLARGE_INTEGER,ULONG,ULONG,ULONG,ULONG,PVOID,ULONG);
typedef struct WpRootV1 {
    HANDLE directory;
    struct WpRootV1 *parent;
    int ready, closing;
} WpRootV1;

static int wp_trusted_v1(PSID sid, PSID user) {
    return sid && IsValidSid(sid) && (EqualSid(sid,user) ||
        IsWellKnownSid(sid,WinLocalSystemSid) ||
        IsWellKnownSid(sid,WinBuiltinAdministratorsSid));
}
static TOKEN_USER *wp_user_v1(void) {
    HANDLE token=NULL; DWORD size=0; TOKEN_USER *user=NULL;
    /* Reject impersonation rather than admitting a descriptor against the
     * process identity while operations execute as a different principal. */
    if (OpenThreadToken(GetCurrentThread(),TOKEN_QUERY,TRUE,&token)) {
        CloseHandle(token); return NULL;
    }
    if (GetLastError()!=ERROR_NO_TOKEN ||
        !OpenProcessToken(GetCurrentProcess(),TOKEN_QUERY,&token)) return NULL;
    GetTokenInformation(token,TokenUser,NULL,0,&size);
    if (size && size<=65536) {
        user=(TOKEN_USER*)malloc(size);
        if (user && !GetTokenInformation(token,TokenUser,user,size,&size)) {
            free(user); user=NULL;
        }
    }
    CloseHandle(token); return user;
}
/* Ancestors may be readable; only the journal directory and its children
 * require privacy. All must reject untrusted mutation, including generic
 * rights and owner implicit WRITE_DAC. Unknown ACE forms fail closed. */
static int wp_security_v1(HANDLE handle,int private_required) {
    TOKEN_USER *user=wp_user_v1(); PSECURITY_DESCRIPTOR security=NULL;
    PSID owner=NULL; PACL dacl=NULL; BOOL present=FALSE,defaulted=FALSE;
    SECURITY_DESCRIPTOR_CONTROL control=0; DWORD revision=0; int ok=0;
    if (!user) return 0;
    if (GetSecurityInfo(handle,SE_FILE_OBJECT,
        OWNER_SECURITY_INFORMATION|DACL_SECURITY_INFORMATION,
        NULL,NULL,NULL,NULL,&security)!=ERROR_SUCCESS || !security) goto done;
    if (!GetSecurityDescriptorOwner(security,&owner,&defaulted) ||
        !wp_trusted_v1(owner,user->User.Sid) ||
        !GetSecurityDescriptorDacl(security,&present,&dacl,&defaulted) ||
        !present || !dacl || !IsValidAcl(dacl) ||
        !GetSecurityDescriptorControl(security,&control,&revision) ||
        (private_required && !(control&SE_DACL_PROTECTED))) goto done;
    for (DWORD index=0; index<dacl->AceCount; index++) {
        void *raw=NULL; if (!GetAce(dacl,index,&raw)) goto done;
        ACE_HEADER *header=(ACE_HEADER*)raw;
        if (header->AceType==ACCESS_DENIED_ACE_TYPE) continue;
        if (header->AceType!=ACCESS_ALLOWED_ACE_TYPE) goto done;
        if (header->AceSize<sizeof(ACCESS_ALLOWED_ACE)) goto done;
        ACCESS_ALLOWED_ACE *ace=(ACCESS_ALLOWED_ACE*)raw;
        if (!IsValidSid((PSID)&ace->SidStart)) goto done;
        if (header->AceFlags&INHERIT_ONLY_ACE) continue;
        DWORD forbidden=FILE_WRITE_DATA|FILE_APPEND_DATA|FILE_WRITE_EA|
            FILE_WRITE_ATTRIBUTES|FILE_DELETE_CHILD|DELETE|WRITE_DAC|
            WRITE_OWNER|GENERIC_WRITE|GENERIC_ALL;
        if (private_required) forbidden |= FILE_READ_DATA|FILE_READ_EA|
            FILE_READ_ATTRIBUTES|READ_CONTROL|GENERIC_READ|GENERIC_EXECUTE|FILE_EXECUTE;
        if ((ace->Mask&forbidden) && !wp_trusted_v1((PSID)&ace->SidStart,user->User.Sid)) goto done;
    }
    ok=1;
done:
    if (security) LocalFree(security); free(user); return ok;
}
static int wp_kind_v1(HANDLE handle,int directory,int64_t maximum) {
    BY_HANDLE_FILE_INFORMATION info; LARGE_INTEGER size;
    if (!GetFileInformationByHandle(handle,&info) ||
        (info.dwFileAttributes&FILE_ATTRIBUTE_REPARSE_POINT) ||
        !!(info.dwFileAttributes&FILE_ATTRIBUTE_DIRECTORY)!=directory) return 0;
    if (!directory && (info.nNumberOfLinks!=1 || maximum<0 ||
        !GetFileSizeEx(handle,&size) || size.QuadPart<0 || size.QuadPart>maximum)) return 0;
    return 1;
}
static int wp_name_v1(const wchar_t *name) {
    if (!name || !*name || !wcscmp(name,L".") || !wcscmp(name,L"..")) return 0;
    size_t length=wcslen(name); if (length>255) return 0;
    for (size_t index=0; index<length; index++)
        if (name[index]<32 || wcschr(L"\\/:*?\"<>|",name[index])) return 0;
    return name[length-1]!=L'.' && name[length-1]!=L' ';
}
static HANDLE wp_relative_v1(HANDLE root,const wchar_t *name,int directory,int create) {
    if (!wp_name_v1(name)) return INVALID_HANDLE_VALUE;
    HMODULE library=GetModuleHandleW(L"ntdll.dll");
    WpCreateV1 open=library?(WpCreateV1)GetProcAddress(library,"NtCreateFile"):NULL;
    if (!open) return INVALID_HANDLE_VALUE;
    TOKEN_USER *user=wp_user_v1(); if (!user) return INVALID_HANDLE_VALUE;
    DWORD acl_size=sizeof(ACL)+sizeof(ACCESS_ALLOWED_ACE)+GetLengthSid(user->User.Sid);
    PACL acl=(PACL)malloc(acl_size); SECURITY_DESCRIPTOR security;
    int ready=acl && InitializeAcl(acl,acl_size,ACL_REVISION) &&
        AddAccessAllowedAce(acl,ACL_REVISION,FILE_ALL_ACCESS,user->User.Sid) &&
        InitializeSecurityDescriptor(&security,SECURITY_DESCRIPTOR_REVISION) &&
        SetSecurityDescriptorOwner(&security,user->User.Sid,FALSE) &&
        SetSecurityDescriptorDacl(&security,TRUE,acl,FALSE) &&
        SetSecurityDescriptorControl(&security,SE_DACL_PROTECTED,SE_DACL_PROTECTED);
    HANDLE handle=INVALID_HANDLE_VALUE;
    if (ready) {
        UNICODE_STRING string; string.Buffer=(PWSTR)name;
        string.Length=(USHORT)(wcslen(name)*sizeof(wchar_t)); string.MaximumLength=string.Length;
        OBJECT_ATTRIBUTES attributes; memset(&attributes,0,sizeof(attributes));
        attributes.Length=sizeof(attributes); attributes.RootDirectory=root;
        attributes.ObjectName=&string; attributes.Attributes=OBJ_CASE_INSENSITIVE;
        attributes.SecurityDescriptor=create?&security:NULL;
        IO_STATUS_BLOCK result;
        /* FILE_OPEN_REPARSE_POINT|FILE_SYNCHRONOUS_IO_NONALERT and exact kind.
         * A live file is exclusive; ancestry permits readers only. */
        NTSTATUS status=open(&handle,READ_CONTROL|FILE_READ_ATTRIBUTES|SYNCHRONIZE|
            (directory?FILE_LIST_DIRECTORY|FILE_ADD_FILE|FILE_ADD_SUBDIRECTORY:
                GENERIC_READ|GENERIC_WRITE|DELETE),&attributes,&result,NULL,
            FILE_ATTRIBUTE_NORMAL,directory?FILE_SHARE_READ:0,
            create?2:1,0x00200000|0x20|(directory?1:0x40),NULL,0);
        if (status<0) handle=INVALID_HANDLE_VALUE;
    }
    free(acl); free(user); return handle;
}
static int wp_close_v1(WpRootV1 **link) {
    WpRootV1 *lease=*link; if (!lease) return 1;
    lease->closing=1;
    if (!wp_close_v1(&lease->parent)) return 0;
    if (lease->directory!=INVALID_HANDLE_VALUE && !CloseHandle(lease->directory)) return 0;
    free(lease); *link=NULL; return 1;
}
int64_t rt_windows_private_root_close_v1(int64_t raw) {
    WpRootV1 *lease=(WpRootV1*)(intptr_t)raw;
    return lease && wp_close_v1(&lease);
}
int64_t rt_windows_private_root_ready_v1(int64_t raw) {
    WpRootV1 *lease=(WpRootV1*)(intptr_t)raw;
    if (!lease || !lease->ready || lease->closing) return 0;
    for (WpRootV1 *item=lease;item;item=item->parent)
        if (!wp_kind_v1(item->directory,1,0) || !wp_security_v1(item->directory,item==lease)) return 0;
    return 1;
}
/* Failed admission returns a cleanup lease whenever close did not complete.
 * Its ready query is false; the caller must retain it and retry close. */
static int64_t wp_reject_v1(WpRootV1 *lease) {
    lease->ready=0;lease->closing=1;
    if (wp_close_v1(&lease)) return -1;
    return (int64_t)(intptr_t)lease;
}
int64_t rt_windows_private_root_open_v1(int64_t raw_path) {
    const wchar_t *path=(const wchar_t*)(intptr_t)raw_path;
    if (!path || wcslen(path)<4 || wcslen(path)>32760 ||
        !((path[0]>=L'A'&&path[0]<=L'Z')||(path[0]>=L'a'&&path[0]<=L'z')) ||
        path[1]!=L':' || path[2]!=L'\\') return -1;
    wchar_t volume[4]={path[0],L':',L'\\',0};
    if (GetDriveTypeW(volume)!=DRIVE_FIXED) return -1;
    WpRootV1 *lease=(WpRootV1*)calloc(1,sizeof(*lease)); if (!lease) return -1;
    lease->directory=CreateFileW(volume,READ_CONTROL|FILE_READ_ATTRIBUTES|FILE_LIST_DIRECTORY,
        FILE_SHARE_READ,NULL,OPEN_EXISTING,FILE_FLAG_BACKUP_SEMANTICS|FILE_FLAG_OPEN_REPARSE_POINT,NULL);
    if (lease->directory==INVALID_HANDLE_VALUE) {free(lease);return -1;}
    if (!wp_kind_v1(lease->directory,1,0) || !wp_security_v1(lease->directory,0)) return wp_reject_v1(lease);
    /* A substituted drive could hide unvalidated ancestors. Require the DOS
     * drive to resolve to a volume root, not a directory below a volume. */
    wchar_t final[128];
    DWORD count=GetFinalPathNameByHandleW(lease->directory,final,128,FILE_NAME_NORMALIZED|VOLUME_NAME_GUID);
    wchar_t *end=count && count<128?wcsrchr(final,L'}'):NULL;
    if (!end || end[1]!=L'\\' || end[2]!=0) return wp_reject_v1(lease);
    const wchar_t *cursor=path+3;
    while (*cursor) {
        const wchar_t *end=wcschr(cursor,L'\\'); size_t count=end?(size_t)(end-cursor):wcslen(cursor);
        if (!count || count>255) return wp_reject_v1(lease);
        wchar_t name[256]; memcpy(name,cursor,count*sizeof(wchar_t)); name[count]=0;
        WpRootV1 *next=(WpRootV1*)calloc(1,sizeof(*next));
        if (!next) return wp_reject_v1(lease);
        next->directory=wp_relative_v1(lease->directory,name,1,0);
        if (next->directory==INVALID_HANDLE_VALUE) {free(next);return wp_reject_v1(lease);}
        next->parent=lease;lease=next;
        if (!wp_kind_v1(lease->directory,1,0) || !wp_security_v1(lease->directory,!end)) return wp_reject_v1(lease);
        if (!end) {lease->ready=1;return (int64_t)(intptr_t)lease;}
        cursor=end+1;
    }
    return wp_reject_v1(lease);
}
int64_t rt_windows_private_directory_v1(int64_t raw,int64_t raw_name,int64_t create) {
    WpRootV1 *root=(WpRootV1*)(intptr_t)raw;
    if (!rt_windows_private_root_ready_v1(raw)) return -1;
    WpRootV1 *child=(WpRootV1*)calloc(1,sizeof(*child)); if (!child) return -1;
    child->directory=INVALID_HANDLE_VALUE;
    WpRootV1 **tail=&child->parent;
    for (WpRootV1 *item=root;item;item=item->parent) {
        WpRootV1 *copy=(WpRootV1*)calloc(1,sizeof(*copy));
        if (!copy) return wp_reject_v1(child);
        copy->directory=INVALID_HANDLE_VALUE;*tail=copy;tail=&copy->parent;
        HANDLE duplicate=NULL;
        if (!DuplicateHandle(GetCurrentProcess(),item->directory,GetCurrentProcess(),&duplicate,0,FALSE,DUPLICATE_SAME_ACCESS)) return wp_reject_v1(child);
        copy->directory=duplicate;
    }
    child->directory=wp_relative_v1(root->directory,(const wchar_t*)(intptr_t)raw_name,1,create!=0);
    if (child->directory==INVALID_HANDLE_VALUE || !wp_kind_v1(child->directory,1,0) ||
        !wp_security_v1(child->directory,1)) return wp_reject_v1(child);
    child->ready=1;return (int64_t)(intptr_t)child;
}
int64_t rt_windows_private_check_v1(int64_t handle,int64_t maximum) {
    return wp_kind_v1((HANDLE)(intptr_t)handle,0,maximum) && wp_security_v1((HANDLE)(intptr_t)handle,1);
}
int64_t rt_windows_private_file_v1(int64_t raw,int64_t name,int64_t create,int64_t maximum) {
    WpRootV1 *root=(WpRootV1*)(intptr_t)raw;
    if (maximum<0 || !rt_windows_private_root_ready_v1(raw)) return -1;
    HANDLE handle=wp_relative_v1(root->directory,(const wchar_t*)(intptr_t)name,0,create!=0);
    if (handle==INVALID_HANDLE_VALUE) return -1;
    /* The typed owner checks admission; even a rejected handle is returned
     * so failed cleanup can never lose ownership. */
    return (int64_t)(intptr_t)handle;
}
int64_t rt_windows_private_publish_v1(int64_t raw,int64_t file,int64_t raw_name) {
    WpRootV1 *root=(WpRootV1*)(intptr_t)raw;
    HANDLE handle=(HANDLE)(intptr_t)file; const wchar_t *name=(const wchar_t*)(intptr_t)raw_name;
    if (!rt_windows_private_root_ready_v1(raw) || !wp_name_v1(name) ||
        !rt_windows_private_check_v1(file,INT64_MAX) || !FlushFileBuffers(handle)) return -1;
    size_t bytes=wcslen(name)*sizeof(wchar_t), size=sizeof(FILE_RENAME_INFO)+bytes;
    FILE_RENAME_INFO *rename=(FILE_RENAME_INFO*)calloc(1,size); if (!rename) return -1;
    rename->ReplaceIfExists=FALSE;rename->RootDirectory=root->directory;
    rename->FileNameLength=(DWORD)bytes;memcpy(rename->FileName,name,bytes);
    int ok=SetFileInformationByHandle(handle,FileRenameInfo,rename,(DWORD)size);
    DWORD error=GetLastError();free(rename);
    if (!ok) return error==ERROR_ALREADY_EXISTS || error==ERROR_FILE_EXISTS?1:-1;
    return rt_windows_private_check_v1(file,INT64_MAX)?0:-1;
}
#else
int64_t rt_windows_private_root_open_v1(int64_t path) {(void)path;return -1;}
int64_t rt_windows_private_directory_v1(int64_t root,int64_t name,int64_t create) {(void)root;(void)name;(void)create;return -1;}
int64_t rt_windows_private_file_v1(int64_t root,int64_t name,int64_t create,int64_t maximum) {(void)root;(void)name;(void)create;(void)maximum;return -1;}
int64_t rt_windows_private_publish_v1(int64_t root,int64_t file,int64_t name) {(void)root;(void)file;(void)name;return -1;}
int64_t rt_windows_private_check_v1(int64_t file,int64_t maximum) {(void)file;(void)maximum;return 0;}
int64_t rt_windows_private_root_close_v1(int64_t root) {(void)root;return 0;}
int64_t rt_windows_private_root_ready_v1(int64_t root) {(void)root;return 0;}
#endif
#endif
