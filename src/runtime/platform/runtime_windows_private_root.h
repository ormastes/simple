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

#define WP_CAPACITY_V1 256
#define WP_PENDING_V1 4
#define WP_DEPTH_V1 64
typedef struct {
    uint64_t generation;
    int kind, phase, created_stage;
    void *owner;
    int64_t root_token, maximum, position;
    FILE_ID_INFO identity;
    FILE_BASIC_INFO basic;
    LARGE_INTEGER size;
    HANDLE pending_handles[WP_PENDING_V1];
    HLOCAL pending_memory[WP_PENDING_V1];
} WpEntryV1;
static WpEntryV1 wp_entries_v1[WP_CAPACITY_V1];
static SRWLOCK wp_lock_v1=SRWLOCK_INIT;
static uint64_t wp_generation_v1=0;
/* Set only while the exclusive IO owner lock is held. Temporary OS resources
 * remain attached to this exact generation if a release operation fails. */
static WpEntryV1 *wp_active_v1;
static int wp_pending_v1(WpEntryV1 *entry) {
    if (!entry) return 1;
    for (int i=0;i<WP_PENDING_V1;i++)
        if (entry->pending_handles[i] || entry->pending_memory[i]) return 1;
    return 0;
}
static int wp_token_release_v1(HANDLE handle) {
    if (CloseHandle(handle)) return 1;
    for (int i=0;i<WP_PENDING_V1;i++) if (!wp_active_v1->pending_handles[i]) {
        wp_active_v1->pending_handles[i]=handle;return 0;
    }
    abort(); /* Opening another temporary without a reserved slot is a bug. */
}
static int wp_memory_release_v1(HLOCAL memory) {
    if (!LocalFree(memory)) return 1;
    for (int i=0;i<WP_PENDING_V1;i++) if (!wp_active_v1->pending_memory[i]) {
        wp_active_v1->pending_memory[i]=memory;return 0;
    }
    abort();
}
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
    if (!wp_active_v1 || wp_pending_v1(wp_active_v1)) return NULL;
    HANDLE token=NULL; DWORD size=0; TOKEN_USER *user=NULL;
    /* Reject impersonation rather than admitting a descriptor against the
     * process identity while operations execute as a different principal. */
    if (OpenThreadToken(GetCurrentThread(),TOKEN_QUERY,TRUE,&token)) {
        wp_token_release_v1(token); return NULL;
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
    if (!wp_token_release_v1(token)) {free(user);return NULL;} return user;
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
        if (header->AceSize<offsetof(ACCESS_ALLOWED_ACE,SidStart)+8) goto done;
        ACCESS_ALLOWED_ACE *ace=(ACCESS_ALLOWED_ACE*)raw;
        SID *sid=(SID*)&ace->SidStart;
        if (sid->SubAuthorityCount>15 || GetSidLengthRequired(sid->SubAuthorityCount)>
            header->AceSize-offsetof(ACCESS_ALLOWED_ACE,SidStart)) goto done;
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
    if (security && !wp_memory_release_v1(security)) ok=0; free(user); return ok;
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
static HANDLE wp_relative_profile_v2(HANDLE root,const wchar_t *name,int directory,int create,int read_only) {
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
            (read_only?(directory?FILE_LIST_DIRECTORY|FILE_TRAVERSE:GENERIC_READ):
                (directory?FILE_LIST_DIRECTORY|FILE_ADD_FILE|FILE_ADD_SUBDIRECTORY:
                    GENERIC_READ|GENERIC_WRITE|DELETE)),&attributes,&result,NULL,
            FILE_ATTRIBUTE_NORMAL,read_only?(directory?FILE_SHARE_READ|FILE_SHARE_WRITE:FILE_SHARE_READ):
                (directory?FILE_SHARE_READ:0),
            create?2:1,0x00200000|0x20|(directory?1:0x40),NULL,0);
        if (status<0) handle=INVALID_HANDLE_VALUE;
    }
    free(acl); free(user); return handle;
}
static HANDLE wp_relative_v1(HANDLE root,const wchar_t *name,int directory,int create) {
    return wp_relative_profile_v2(root,name,directory,create,0);
}
static int wp_close_v1(WpRootV1 **link) {
    WpRootV1 *lease=*link; if (!lease) return 1;
    lease->closing=1;
    if (!wp_close_v1(&lease->parent)) return 0;
    if (lease->directory!=INVALID_HANDLE_VALUE && !CloseHandle(lease->directory)) return 0;
    free(lease); *link=NULL; return 1;
}
static int64_t wp_root_close_impl_v1(int64_t raw) {
    WpRootV1 *lease=(WpRootV1*)(intptr_t)raw;
    return lease && wp_close_v1(&lease);
}
static int64_t wp_root_ready_impl_v1(int64_t raw) {
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
static int64_t wp_root_open_profile_v2(int64_t raw_path,int read_only) {
    const wchar_t *path=(const wchar_t*)(intptr_t)raw_path;
    if (!path || wcslen(path)<4 || wcslen(path)>32760 ||
        !((path[0]>=L'A'&&path[0]<=L'Z')||(path[0]>=L'a'&&path[0]<=L'z')) ||
        path[1]!=L':' || path[2]!=L'\\') return -1;
    wchar_t volume[4]={path[0],L':',L'\\',0};
    if (GetDriveTypeW(volume)!=DRIVE_FIXED) return -1;
    WpRootV1 *lease=(WpRootV1*)calloc(1,sizeof(*lease)); if (!lease) return -1;
    lease->directory=CreateFileW(volume,READ_CONTROL|FILE_READ_ATTRIBUTES|FILE_LIST_DIRECTORY|
        (read_only?FILE_TRAVERSE:0),read_only?FILE_SHARE_READ|FILE_SHARE_WRITE:FILE_SHARE_READ,NULL,OPEN_EXISTING,FILE_FLAG_BACKUP_SEMANTICS|FILE_FLAG_OPEN_REPARSE_POINT,NULL);
    if (lease->directory==INVALID_HANDLE_VALUE) {free(lease);return -1;}
    if (!wp_kind_v1(lease->directory,1,0) || !wp_security_v1(lease->directory,0)) return wp_reject_v1(lease);
    /* A substituted drive could hide unvalidated ancestors. Require the DOS
     * drive to resolve to a volume root, not a directory below a volume. */
    wchar_t final[128];
    DWORD count=GetFinalPathNameByHandleW(lease->directory,final,128,FILE_NAME_NORMALIZED|VOLUME_NAME_GUID);
    wchar_t *end=count && count<128?wcsrchr(final,L'}'):NULL;
    if (!end || end[1]!=L'\\' || end[2]!=0) return wp_reject_v1(lease);
    const wchar_t *cursor=path+3;
    unsigned depth=1;
    while (*cursor) {
        if (++depth>WP_DEPTH_V1) return wp_reject_v1(lease);
        const wchar_t *end=wcschr(cursor,L'\\'); size_t count=end?(size_t)(end-cursor):wcslen(cursor);
        if (!count || count>255) return wp_reject_v1(lease);
        wchar_t name[256]; memcpy(name,cursor,count*sizeof(wchar_t)); name[count]=0;
        WpRootV1 *next=(WpRootV1*)calloc(1,sizeof(*next));
        if (!next) return wp_reject_v1(lease);
        next->directory=wp_relative_profile_v2(lease->directory,name,1,0,read_only);
        if (next->directory==INVALID_HANDLE_VALUE) {free(next);return wp_reject_v1(lease);}
        next->parent=lease;lease=next;
        if (!wp_kind_v1(lease->directory,1,0) || !wp_security_v1(lease->directory,!end)) return wp_reject_v1(lease);
        if (!end) {lease->ready=1;return (int64_t)(intptr_t)lease;}
        cursor=end+1;
    }
    return wp_reject_v1(lease);
}
static int64_t wp_root_open_impl_v1(int64_t raw_path) {
    return wp_root_open_profile_v2(raw_path,0);
}
static int64_t wp_directory_profile_v2(int64_t raw,int64_t raw_name,int64_t create,int read_only) {
    WpRootV1 *root=(WpRootV1*)(intptr_t)raw;
    if (!wp_root_ready_impl_v1(raw)) return -1;
    unsigned depth=0;
    for (WpRootV1 *item=root;item;item=item->parent)
        if (++depth>=WP_DEPTH_V1) return -1;
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
    child->directory=wp_relative_profile_v2(root->directory,(const wchar_t*)(intptr_t)raw_name,1,create!=0,read_only);
    if (child->directory==INVALID_HANDLE_VALUE || !wp_kind_v1(child->directory,1,0) ||
        !wp_security_v1(child->directory,1)) return wp_reject_v1(child);
    child->ready=1;return (int64_t)(intptr_t)child;
}
static int64_t wp_directory_impl_v1(int64_t raw,int64_t raw_name,int64_t create) {
    return wp_directory_profile_v2(raw,raw_name,create,0);
}
static int64_t wp_check_impl_v1(int64_t handle,int64_t maximum) {
    return wp_kind_v1((HANDLE)(intptr_t)handle,0,maximum) && wp_security_v1((HANDLE)(intptr_t)handle,1);
}
static int64_t wp_file_impl_v1(int64_t raw,int64_t name,int64_t create,int64_t maximum) {
    WpRootV1 *root=(WpRootV1*)(intptr_t)raw;
    if (maximum<0 || !wp_root_ready_impl_v1(raw)) return -1;
    HANDLE handle=wp_relative_v1(root->directory,(const wchar_t*)(intptr_t)name,0,create!=0);
    if (handle==INVALID_HANDLE_VALUE) return -1;
    /* The typed owner checks admission; even a rejected handle is returned
     * so failed cleanup can never lose ownership. */
    return (int64_t)(intptr_t)handle;
}
static int64_t wp_publish_impl_v1(int64_t raw,WpEntryV1 *entry,int64_t raw_name) {
    WpRootV1 *root=(WpRootV1*)(intptr_t)raw;
    HANDLE handle=(HANDLE)entry->owner;
    int64_t file=(int64_t)(intptr_t)handle;
    const wchar_t *name=(const wchar_t*)(intptr_t)raw_name;
    if (!wp_root_ready_impl_v1(raw) || !wp_name_v1(name) ||
        !wp_check_impl_v1(file,INT64_MAX) || !FlushFileBuffers(handle)) return -1;
    size_t bytes=wcslen(name)*sizeof(wchar_t), size=sizeof(FILE_RENAME_INFO)+bytes;
    FILE_RENAME_INFO *rename=(FILE_RENAME_INFO*)calloc(1,size); if (!rename) return -1;
    rename->ReplaceIfExists=FALSE;rename->RootDirectory=root->directory;
    rename->FileNameLength=(DWORD)bytes;memcpy(rename->FileName,name,bytes);
    int ok=SetFileInformationByHandle(handle,FileRenameInfo,rename,(DWORD)size);
    /* This is the effect linearization point. The exclusive IO lock remains
     * held, and every alias observes publication consumed even if a subsequent
     * security query, temporary release or identity snapshot fails. */
    if (ok) entry->phase=2;
    DWORD error=GetLastError();free(rename);
    if (!ok) return error==ERROR_ALREADY_EXISTS || error==ERROR_FILE_EXISTS?1:-1;
    return wp_check_impl_v1(file,INT64_MAX)?0:-1;
}
static WpEntryV1 *wp_find_v1(int64_t token,int kind) {
    if (token<=0) return NULL;
    unsigned slot=(unsigned)((uint64_t)token&255);
    WpEntryV1 *entry=&wp_entries_v1[slot];
    return entry->kind==kind && entry->generation==((uint64_t)token>>8)?entry:NULL;
}
static int64_t wp_reserve_v1(int kind) {
    if (wp_generation_v1>=(uint64_t)INT64_MAX/256) return -1;
    for (unsigned slot=0;slot<WP_CAPACITY_V1;slot++) if (!wp_entries_v1[slot].kind) {
        WpEntryV1 *entry=&wp_entries_v1[slot];memset(entry,0,sizeof(*entry));
        entry->kind=kind;entry->generation=++wp_generation_v1;
        return (int64_t)((entry->generation<<8)|slot);
    }
    return -1;
}
static int wp_cleanup_v1(WpEntryV1 *entry) {
    int ok=1;entry->phase=3;
    if (entry->owner) {
        int closed=(entry->kind==1 || entry->kind==3)?wp_root_close_impl_v1((int64_t)(intptr_t)entry->owner):CloseHandle((HANDLE)entry->owner);
        if (closed) entry->owner=NULL;else ok=0;
    }
    for (int i=0;i<WP_PENDING_V1;i++) {
        if (entry->pending_handles[i]) {
            if (CloseHandle(entry->pending_handles[i])) entry->pending_handles[i]=NULL;else ok=0;
        }
        if (entry->pending_memory[i]) {
            if (!LocalFree(entry->pending_memory[i])) entry->pending_memory[i]=NULL;else ok=0;
        }
    }
    if (ok) memset(entry,0,sizeof(*entry));
    return ok;
}
static int64_t wp_finish_open_v1(int64_t token,int64_t owner) {
    WpEntryV1 *entry=wp_active_v1;
    entry->owner=owner==-1?NULL:(void*)(intptr_t)owner;
    if (!entry->owner && !wp_pending_v1(entry)) {memset(entry,0,sizeof(*entry));return -1;}
    return token;
}
static int wp_root_valid_v1(WpEntryV1 *entry) {
    return entry && entry->owner && entry->phase!=3 && !wp_pending_v1(entry) &&
        wp_root_ready_impl_v1((int64_t)(intptr_t)entry->owner);
}
static int wp_file_valid_v1(WpEntryV1 *entry) {
    return entry && entry->owner && entry->phase!=3 && !wp_pending_v1(entry) &&
        wp_check_impl_v1((int64_t)(intptr_t)entry->owner,entry->maximum);
}
static int wp_snapshot_v1(WpEntryV1 *entry) {
    HANDLE handle=(HANDLE)entry->owner;
    return GetFileInformationByHandleEx(handle,FileIdInfo,&entry->identity,sizeof(entry->identity)) &&
        GetFileInformationByHandleEx(handle,FileBasicInfo,&entry->basic,sizeof(entry->basic)) &&
        GetFileSizeEx(handle,&entry->size);
}
static int wp_unchanged_v1(WpEntryV1 *entry) {
    FILE_ID_INFO identity;FILE_BASIC_INFO basic;LARGE_INTEGER size;
    HANDLE handle=(HANDLE)entry->owner;
    return wp_file_valid_v1(entry) &&
        GetFileInformationByHandleEx(handle,FileIdInfo,&identity,sizeof(identity)) &&
        GetFileInformationByHandleEx(handle,FileBasicInfo,&basic,sizeof(basic)) && GetFileSizeEx(handle,&size) &&
        !memcmp(&identity,&entry->identity,sizeof(identity)) && size.QuadPart==entry->size.QuadPart &&
        basic.LastWriteTime.QuadPart==entry->basic.LastWriteTime.QuadPart &&
        basic.ChangeTime.QuadPart==entry->basic.ChangeTime.QuadPart;
}
int64_t rt_windows_private_root_open_v1(int64_t path) {
    AcquireSRWLockExclusive(&wp_lock_v1);int64_t token=wp_reserve_v1(1);
    if (token!=-1) {wp_active_v1=wp_find_v1(token,1);token=wp_finish_open_v1(token,wp_root_open_impl_v1(path));}
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return token;
}
int64_t rt_windows_private_root_ready_v1(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,1);wp_active_v1=entry;
    int valid=wp_root_valid_v1(entry);wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return valid;
}
int64_t rt_windows_private_directory_v1(int64_t root,int64_t name,int64_t create) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *parent=wp_find_v1(root,1);
    int64_t token=parent?wp_reserve_v1(1):-1;
    if (token!=-1) {wp_active_v1=wp_find_v1(token,1);
        token=wp_finish_open_v1(token,wp_root_valid_v1(parent)?
            wp_directory_impl_v1((int64_t)(intptr_t)parent->owner,name,create):-1);}
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return token;
}
int64_t rt_windows_private_file_v1(int64_t root,int64_t name,int64_t create,int64_t maximum) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *parent=wp_find_v1(root,1);
    int64_t token=parent && maximum>=0 && maximum<=8388608?wp_reserve_v1(2):-1;
    if (token!=-1) {WpEntryV1 *entry=wp_find_v1(token,2);wp_active_v1=entry;
        entry->maximum=maximum;entry->root_token=root;entry->phase=create?0:1;entry->created_stage=create!=0;
        int64_t handle=wp_root_valid_v1(parent)?wp_file_impl_v1((int64_t)(intptr_t)parent->owner,name,create,maximum):-1;
        token=wp_finish_open_v1(token,handle);
        if (token!=-1 && handle!=-1 && !create && !wp_snapshot_v1(entry)) entry->phase=3;
    }
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return token;
}
int64_t rt_windows_private_check_v1(int64_t token,int64_t maximum) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,2);wp_active_v1=entry;
    int valid=entry && maximum>=entry->maximum && wp_file_valid_v1(entry);
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return valid;
}
int64_t rt_windows_private_file_write_v1(int64_t token,int64_t buffer,int64_t length) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,2);wp_active_v1=entry;int64_t result=-1;
    if (entry && entry->phase==0 && length>=0 && length<=1048576 &&
        length<=entry->maximum-entry->position && wp_file_valid_v1(entry)) {
        DWORD count=0;
        if (WriteFile((HANDLE)entry->owner,(void*)(intptr_t)buffer,(DWORD)length,&count,NULL)) {
            entry->position+=count;result=count;
        } else entry->phase=3;
    }
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
int64_t rt_windows_private_file_seal_v1(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,2);wp_active_v1=entry;int ok=0;
    if (entry && entry->phase==0 && wp_file_valid_v1(entry) && FlushFileBuffers((HANDLE)entry->owner) && wp_snapshot_v1(entry)) {
        entry->phase=1;ok=1;
    }
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return ok;
}
static int64_t wp_file_size_profile_v2(int64_t token,int kind) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,kind);wp_active_v1=entry;
    int64_t size=entry && (entry->phase==1 || entry->phase==2) && wp_unchanged_v1(entry)?entry->size.QuadPart:-1;
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return size;
}
int64_t rt_windows_private_file_size_v1(int64_t token) {
    return wp_file_size_profile_v2(token,2);
}
static int64_t wp_file_read_profile_v2(int64_t token,int64_t offset,int64_t buffer,int64_t length,int kind) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,kind);wp_active_v1=entry;int64_t result=-1;
    if (entry && (entry->phase==1 || entry->phase==2) && offset>=0 && length>=0 && length<=1048576 &&
        offset<=entry->size.QuadPart && length<=entry->size.QuadPart-offset && wp_unchanged_v1(entry)) {
        LARGE_INTEGER position;position.QuadPart=offset;DWORD count=0;
        if (SetFilePointerEx((HANDLE)entry->owner,position,NULL,FILE_BEGIN) &&
            ReadFile((HANDLE)entry->owner,(void*)(intptr_t)buffer,(DWORD)length,&count,NULL) && wp_unchanged_v1(entry)) result=count;
    }
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
int64_t rt_windows_private_file_read_v1(int64_t token,int64_t offset,int64_t buffer,int64_t length) {
    return wp_file_read_profile_v2(token,offset,buffer,length,2);
}
int64_t rt_windows_private_publish_v1(int64_t root,int64_t file,int64_t name) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *directory=wp_find_v1(root,1),*entry=wp_find_v1(file,2);
    wp_active_v1=entry;int64_t result=-1;
    if (entry && entry->created_stage && entry->root_token==root && entry->phase==1 && wp_root_valid_v1(directory) && wp_unchanged_v1(entry)) {
        result=wp_publish_impl_v1((int64_t)(intptr_t)directory->owner,entry,name);
        if (entry->phase==2 && (result!=0 || !wp_snapshot_v1(entry))) {entry->phase=3;result=-1;}
    }
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
int64_t rt_windows_private_root_close_v1(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,1);
    int ok=entry && wp_cleanup_v1(entry);ReleaseSRWLockExclusive(&wp_lock_v1);return ok;
}
int64_t rt_windows_private_file_close_v1(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,2);
    int ok=entry && wp_cleanup_v1(entry);ReleaseSRWLockExclusive(&wp_lock_v1);return ok;
}

/* V2 readonly capabilities use distinct kinds in the SAME registry. None of
 * the V1 mutating ports accept kind 3 (root) or kind 4 (file), even by cast. */
int64_t rt_windows_private_read_root_open_v2(int64_t path) {
    AcquireSRWLockExclusive(&wp_lock_v1);int64_t token=wp_reserve_v1(3);
    if (token!=-1) {wp_active_v1=wp_find_v1(token,3);token=wp_finish_open_v1(token,wp_root_open_profile_v2(path,1));}
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return token;
}
int64_t rt_windows_private_read_root_ready_v2(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,3);wp_active_v1=entry;
    int valid=wp_root_valid_v1(entry);wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return valid;
}
int64_t rt_windows_private_read_directory_v2(int64_t root,int64_t name) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *parent=wp_find_v1(root,3);
    int64_t token=parent?wp_reserve_v1(3):-1;
    if (token!=-1) {wp_active_v1=wp_find_v1(token,3);
        token=wp_finish_open_v1(token,wp_root_valid_v1(parent)?
            wp_directory_profile_v2((int64_t)(intptr_t)parent->owner,name,0,1):-1);}
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return token;
}
int64_t rt_windows_private_read_file_open_v2(int64_t root,int64_t name,int64_t maximum) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *parent=wp_find_v1(root,3);
    int64_t token=parent && maximum>=0 && maximum<=8388608?wp_reserve_v1(4):-1;
    if (token!=-1) {
        WpEntryV1 *entry=wp_find_v1(token,4);wp_active_v1=entry;
        entry->maximum=maximum;entry->root_token=root;entry->phase=1;
        HANDLE handle=wp_root_valid_v1(parent)?wp_relative_profile_v2(
            ((WpRootV1*)parent->owner)->directory,(const wchar_t*)(intptr_t)name,0,0,1):INVALID_HANDLE_VALUE;
        token=wp_finish_open_v1(token,(int64_t)(intptr_t)handle);
        if (token!=-1 && handle!=INVALID_HANDLE_VALUE && !wp_snapshot_v1(entry)) entry->phase=3;
    }
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return token;
}
int64_t rt_windows_private_read_file_check_v2(int64_t token,int64_t maximum) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,4);wp_active_v1=entry;
    int valid=entry && maximum>=entry->maximum && wp_unchanged_v1(entry);
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return valid;
}
int64_t rt_windows_private_read_file_size_v2(int64_t token) {return wp_file_size_profile_v2(token,4);}
int64_t rt_windows_private_read_file_read_v2(int64_t token,int64_t offset,int64_t buffer,int64_t length) {
    return wp_file_read_profile_v2(token,offset,buffer,length,4);
}
int64_t rt_windows_private_read_root_close_v2(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,3);
    int ok=entry && wp_cleanup_v1(entry);ReleaseSRWLockExclusive(&wp_lock_v1);return ok;
}
int64_t rt_windows_private_read_file_close_v2(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,4);
    int ok=entry && wp_cleanup_v1(entry);ReleaseSRWLockExclusive(&wp_lock_v1);return ok;
}
static int wp_volume_guid_v2(HANDLE handle,wchar_t volume[64]) {
    wchar_t path[32900];
    DWORD length=GetFinalPathNameByHandleW(handle,path,32900,FILE_NAME_NORMALIZED|VOLUME_NAME_GUID);
    if (!length || length>=32900 || wcsncmp(path,L"\\\\?\\Volume{",11)) return 0;
    wchar_t* end=wcschr(path,L'}');
    if (!end || end[1]!=L'\\') return 0;
    size_t count=(size_t)(end-path)+1;if (count>=64) return 0;
    memcpy(volume,path,count*sizeof(wchar_t));volume[count]=0;return 1;
}
/* Generic retained-directory identity only; never a deployment/exec role. A
 * failed security temporary release stays on the root being validated. */
int64_t rt_windows_private_roots_same_directory_v2(int64_t writer,int64_t reader) {
    AcquireSRWLockExclusive(&wp_lock_v1);
    WpEntryV1 *mutable_root=wp_find_v1(writer,1),*read_root=wp_find_v1(reader,3);
    int64_t result=-1;FILE_ID_INFO first,second;wchar_t first_volume[64],second_volume[64];
    if (!mutable_root || !read_root) goto done;
    wp_active_v1=mutable_root;
    if (!wp_root_valid_v1(mutable_root) || !GetFileInformationByHandleEx(
        ((WpRootV1*)mutable_root->owner)->directory,FileIdInfo,&first,sizeof(first)) ||
        !wp_volume_guid_v2(((WpRootV1*)mutable_root->owner)->directory,first_volume)) goto done;
    wp_active_v1=read_root;
    if (!wp_root_valid_v1(read_root) || !GetFileInformationByHandleEx(
        ((WpRootV1*)read_root->owner)->directory,FileIdInfo,&second,sizeof(second)) ||
        !wp_volume_guid_v2(((WpRootV1*)read_root->owner)->directory,second_volume)) goto done;
    int compared=CompareStringOrdinal(first_volume,-1,second_volume,-1,TRUE);
    if (!compared) goto done;
    result=compared==CSTR_EQUAL &&
        !memcmp(&first,&second,sizeof(first));
done:
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
static int wp_content_v2(HANDLE handle,uint8_t* expected,int64_t length,int compare) {
    LARGE_INTEGER zero;zero.QuadPart=0;
    if (!SetFilePointerEx(handle,zero,NULL,FILE_BEGIN)) return 0;
    uint8_t chunk[65536];int64_t offset=0;
    while (offset<length) {
        DWORD count=0,wanted=(DWORD)(length-offset>65536?65536:length-offset);
        if (!ReadFile(handle,compare?chunk:expected+offset,wanted,&count,NULL) || count!=wanted) return 0;
        if (compare && memcmp(chunk,expected+offset,wanted)) return 0;
        offset+=wanted;
    }
    return 1;
}
/* Borrowed output: reader token, remaining stage token, historical rename
 * effect. All outputs are initialized BEFORE any side effect. Return 1 means
 * known no-effect collision; 0 means verified readonly handoff; -1 is error. */
int64_t rt_windows_private_publish_shared_read_v2(int64_t root,int64_t stage,int64_t name,int64_t output) {
    if (!output) return -1;
    int64_t* out=(int64_t*)(intptr_t)output;out[0]=out[1]=out[2]=0;
    AcquireSRWLockExclusive(&wp_lock_v1);
    WpEntryV1 *directory=wp_find_v1(root,1),*entry=wp_find_v1(stage,2);wp_active_v1=entry;
    int64_t result=-1;uint8_t* bytes=NULL;
    if (entry) out[1]=stage;
    if (!entry || !entry->created_stage || entry->root_token!=root || entry->phase!=1 ||
        entry->maximum<0 || entry->maximum>8388608 || entry->size.QuadPart<0 ||
        entry->size.QuadPart>entry->maximum || !wp_root_valid_v1(directory) || !wp_unchanged_v1(entry)) goto done;
    int64_t length=entry->size.QuadPart;
    bytes=(uint8_t*)malloc((size_t)(length?length:1));if (!bytes) goto done;
    if (!wp_content_v2((HANDLE)entry->owner,bytes,length,0) || !wp_unchanged_v1(entry)) goto done;
    /* Phase 4 consumes aliases' mutation while the transition is in flight.
     * A proven no-effect collision restores the original sealed stage only. */
    entry->phase=4;
    result=wp_publish_impl_v1((int64_t)(intptr_t)directory->owner,entry,name);
    if (entry->phase==2) out[2]=1;
    if (result==1) {entry->phase=1;goto done;}
    if (result!=0 || !out[2]) {entry->phase=3;result=-1;goto done;}
    FILE_ID_INFO expected=entry->identity;
    entry->phase=3; /* Any failure from here is cleanup-only, never publishable. */
    if (!CloseHandle((HANDLE)entry->owner)) {result=-1;goto done;}
    entry->owner=NULL;
    HANDLE reader=wp_relative_profile_v2(((WpRootV1*)directory->owner)->directory,
        (const wchar_t*)(intptr_t)name,0,0,1);
    if (reader==INVALID_HANDLE_VALUE) {
        if (!wp_pending_v1(entry)) {memset(entry,0,sizeof(*entry));out[1]=0;}
        result=-1;goto done;
    }
    entry->owner=reader;entry->kind=4;entry->created_stage=0;out[0]=stage;out[1]=0;
    FILE_ID_INFO actual;LARGE_INTEGER size;
    if (!wp_check_impl_v1((int64_t)(intptr_t)reader,entry->maximum) ||
        !GetFileInformationByHandleEx(reader,FileIdInfo,&actual,sizeof(actual)) ||
        memcmp(&actual,&expected,sizeof(actual)) || !GetFileSizeEx(reader,&size) || size.QuadPart!=length ||
        !wp_content_v2(reader,bytes,length,1) || !wp_check_impl_v1((int64_t)(intptr_t)reader,entry->maximum) ||
        !wp_snapshot_v1(entry) || memcmp(&entry->identity,&expected,sizeof(expected)) || entry->size.QuadPart!=length) {
        result=-1;goto done;
    }
    entry->phase=1;result=0;
done:
    free(bytes);wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}

#else
int64_t rt_windows_private_root_open_v1(int64_t path) {(void)path;return -1;}
int64_t rt_windows_private_directory_v1(int64_t root,int64_t name,int64_t create) {(void)root;(void)name;(void)create;return -1;}
int64_t rt_windows_private_file_v1(int64_t root,int64_t name,int64_t create,int64_t maximum) {(void)root;(void)name;(void)create;(void)maximum;return -1;}
int64_t rt_windows_private_publish_v1(int64_t root,int64_t file,int64_t name) {(void)root;(void)file;(void)name;return -1;}
int64_t rt_windows_private_check_v1(int64_t file,int64_t maximum) {(void)file;(void)maximum;return 0;}
int64_t rt_windows_private_root_close_v1(int64_t root) {(void)root;return 0;}
int64_t rt_windows_private_root_ready_v1(int64_t root) {(void)root;return 0;}
int64_t rt_windows_private_file_close_v1(int64_t file) {(void)file;return 0;}
int64_t rt_windows_private_file_write_v1(int64_t file,int64_t buffer,int64_t length) {(void)file;(void)buffer;(void)length;return -1;}
int64_t rt_windows_private_file_read_v1(int64_t file,int64_t offset,int64_t buffer,int64_t length) {(void)file;(void)offset;(void)buffer;(void)length;return -1;}
int64_t rt_windows_private_file_size_v1(int64_t file) {(void)file;return -1;}
int64_t rt_windows_private_file_seal_v1(int64_t file) {(void)file;return 0;}
int64_t rt_windows_private_read_root_open_v2(int64_t path) {(void)path;return -1;}
int64_t rt_windows_private_read_root_ready_v2(int64_t root) {(void)root;return 0;}
int64_t rt_windows_private_read_directory_v2(int64_t root,int64_t name) {(void)root;(void)name;return -1;}
int64_t rt_windows_private_read_file_open_v2(int64_t root,int64_t name,int64_t maximum) {(void)root;(void)name;(void)maximum;return -1;}
int64_t rt_windows_private_read_file_check_v2(int64_t file,int64_t maximum) {(void)file;(void)maximum;return 0;}
int64_t rt_windows_private_read_file_size_v2(int64_t file) {(void)file;return -1;}
int64_t rt_windows_private_read_file_read_v2(int64_t file,int64_t offset,int64_t buffer,int64_t length) {(void)file;(void)offset;(void)buffer;(void)length;return -1;}
int64_t rt_windows_private_read_root_close_v2(int64_t root) {(void)root;return 0;}
int64_t rt_windows_private_read_file_close_v2(int64_t file) {(void)file;return 0;}
int64_t rt_windows_private_roots_same_directory_v2(int64_t writer,int64_t reader) {(void)writer;(void)reader;return -1;}
int64_t rt_windows_private_publish_shared_read_v2(int64_t root,int64_t stage,int64_t name,int64_t output) {
    (void)root;(void)stage;(void)name;if (output) {int64_t* out=(int64_t*)(intptr_t)output;out[0]=out[1]=out[2]=0;}return -1;
}

#endif
/* Private facade temporaries use malloc/free, whose release has no fallible
 * OS handle semantics. They never use an unchecked HeapFree owner. */
#include <stdlib.h>
int64_t rt_windows_private_alloc_v1(int64_t size) {return size>0 && size<=2097168?(int64_t)(intptr_t)calloc(1,(size_t)size):0;}
void rt_windows_private_free_v1(int64_t memory) {free((void*)(intptr_t)memory);}
#endif
