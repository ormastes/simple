/* Independently configured Windows dedicated-volume bound. Native length is
 * the envelope, never a free-space estimate or Linux project-quota emulation. */
#ifndef SIMPLE_WORKSPACE_STORAGE_WINDOWS_PRIVATE_H
#define SIMPLE_WORKSPACE_STORAGE_WINDOWS_PRIVATE_H
#include <windows.h>
#include <winioctl.h>
#include <aclapi.h>
#include <wchar.h>

typedef struct {
    HANDLE parent, workspace, volume;
    wchar_t parent_path[4096], workspace_path[4224];
    DWORD volume_serial, file_high, file_low;
    int locked;
} WsNativeV1;
static int ws_windows_error_v1(void) {
    DWORD error=GetLastError();
    return error==ERROR_ACCESS_DENIED?EACCES:error==ERROR_FILE_NOT_FOUND||error==ERROR_PATH_NOT_FOUND?ENOENT:EIO;
}
static int ws_windows_path_v1(const char* source,wchar_t* target,int count) {
    return MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,source,-1,target,count)>0?0:EINVAL;
}
static int ws_windows_trusted_sid_v1(PSID sid,PSID service) {
    return sid&&IsValidSid(sid)&&(EqualSid(sid,service)||
        IsWellKnownSid(sid,WinLocalSystemSid)||IsWellKnownSid(sid,WinBuiltinAdministratorsSid));
}
static int ws_windows_protected_descriptor_v1(PSECURITY_DESCRIPTOR security,PSID service) {
    PSID owner=NULL;PACL dacl=NULL;BOOL defaulted=FALSE,present=FALSE;
    if(!security||!service||!IsValidSid(service)||
            !GetSecurityDescriptorOwner(security,&owner,&defaulted)||
            !ws_windows_trusted_sid_v1(owner,service)||
            !GetSecurityDescriptorDacl(security,&present,&dacl,&defaulted)||!present||!dacl)return EACCES;
    /* A foreign owner has implicit WRITE_DAC even if no allow ACE grants it.
     * Refuse before considering writable ACEs; no OWNER_RIGHTS exception. */
    for(DWORD i=0;i<dacl->AceCount;i++) {
        void* raw=NULL;if(!GetAce(dacl,i,&raw))return EACCES;
        ACE_HEADER* header=(ACE_HEADER*)raw;
        if(header->AceType==ACCESS_DENIED_ACE_TYPE)continue;
        if(header->AceType!=ACCESS_ALLOWED_ACE_TYPE)return EACCES;
        ACCESS_ALLOWED_ACE* ace=(ACCESS_ALLOWED_ACE*)raw;
        if(header->AceFlags&INHERIT_ONLY_ACE)continue;
        DWORD writes=FILE_ADD_FILE|FILE_ADD_SUBDIRECTORY|FILE_DELETE_CHILD|DELETE|
            WRITE_DAC|WRITE_OWNER|GENERIC_WRITE|GENERIC_ALL;
        if((ace->Mask&writes)&&!ws_windows_trusted_sid_v1((PSID)&ace->SidStart,service))return EACCES;
    }
    return 0;
}
static int ws_windows_protected_parent_v1(HANDLE directory) {
    PSECURITY_DESCRIPTOR security=NULL;
    DWORD error=GetSecurityInfo(directory,SE_FILE_OBJECT,DACL_SECURITY_INFORMATION|OWNER_SECURITY_INFORMATION,
        NULL,NULL,NULL,NULL,&security);
    if(error!=ERROR_SUCCESS||!security){if(security)LocalFree(security);return EACCES;}
    HANDLE token=NULL;DWORD needed=0;TOKEN_USER* user=NULL;int accepted=0;
    if(!OpenProcessToken(GetCurrentProcess(),TOKEN_QUERY,&token))goto done;
    (void)GetTokenInformation(token,TokenUser,NULL,0,&needed);
    if(!needed||needed>65536)goto done;
    user=(TOKEN_USER*)malloc(needed);if(!user)goto done;
    if(!GetTokenInformation(token,TokenUser,user,needed,&needed))goto done;
    accepted=ws_windows_protected_descriptor_v1(security,user->User.Sid)==0;
done:
    if(token)CloseHandle(token);free(user);LocalFree(security);
    return accepted?0:EACCES;
}
static void ws_native_close_v1(WsNativeV1* native) {
    if(native->workspace&&native->workspace!=INVALID_HANDLE_VALUE)CloseHandle(native->workspace);
    if(native->parent&&native->parent!=INVALID_HANDLE_VALUE)CloseHandle(native->parent);
    if(native->volume&&native->volume!=INVALID_HANDLE_VALUE) {
        if(native->locked){DWORD bytes;DeviceIoControl(native->volume,FSCTL_UNLOCK_VOLUME,NULL,0,NULL,0,&bytes,NULL);}
        CloseHandle(native->volume);
    }
    native->workspace=native->parent=native->volume=NULL;native->locked=0;
}
static int ws_windows_measure_v1(WsNativeV1* native,int64_t hard,int64_t* used,int64_t* inodes) {
    GET_LENGTH_INFORMATION length;NTFS_VOLUME_DATA_BUFFER data;DWORD bytes=0;
    if(!DeviceIoControl(native->volume,IOCTL_DISK_GET_LENGTH_INFO,NULL,0,&length,sizeof(length),&bytes,NULL)||
            bytes<sizeof(length)||length.Length.QuadPart!=hard)return ESTALE;
    if(!DeviceIoControl(native->volume,FSCTL_GET_NTFS_VOLUME_DATA,NULL,0,&data,sizeof(data),&bytes,NULL)||
            bytes<sizeof(data)||!data.BytesPerCluster||data.TotalClusters.QuadPart<0||
            data.FreeClusters.QuadPart<0||data.FreeClusters.QuadPart>data.TotalClusters.QuadPart)return ENOTSUP;
    uint64_t occupied=(uint64_t)(data.TotalClusters.QuadPart-data.FreeClusters.QuadPart);
    if(occupied>(uint64_t)INT64_MAX/data.BytesPerCluster)return EOVERFLOW;
    *used=(int64_t)(occupied*data.BytesPerCluster);
    *inodes=-1; /* unavailable; never project unknown inode usage as zero */
    return 0;
}
static int ws_windows_identity_v1(WsNativeV1* native,char* pool,size_t pool_size,
        char* workspace,size_t workspace_size) {
    wchar_t final[4096];
    DWORD count=GetFinalPathNameByHandleW(native->parent,final,4096,FILE_NAME_NORMALIZED|VOLUME_NAME_GUID);
    if(!count||count>=4096||wcsncmp(final,L"\\\\?\\Volume{",11))return ESTALE;
    wchar_t* end=wcschr(final,L'}');
    if(!end||end[1]!=L'\\'||end[2]!=0)return EINVAL; /* dedicated volume root only */
    char guid[128];
    if(!WideCharToMultiByte(CP_UTF8,WC_ERR_INVALID_CHARS,final,-1,guid,sizeof(guid),NULL,NULL))return EINVAL;
    BY_HANDLE_FILE_INFORMATION root,child;
    if(!GetFileInformationByHandle(native->parent,&root)||!GetFileInformationByHandle(native->workspace,&child))return EIO;
    if(!(root.dwFileAttributes&FILE_ATTRIBUTE_DIRECTORY)||!(child.dwFileAttributes&FILE_ATTRIBUTE_DIRECTORY)||
            (root.dwFileAttributes&FILE_ATTRIBUTE_REPARSE_POINT)||(child.dwFileAttributes&FILE_ATTRIBUTE_REPARSE_POINT)||
            root.dwVolumeSerialNumber!=child.dwVolumeSerialNumber)return ESTALE;
    int a=snprintf(pool,pool_size,"windows-volume:%s:%08lx",guid,(unsigned long)root.dwVolumeSerialNumber);
    int b=snprintf(workspace,workspace_size,"file:%08lx:%08lx:%08lx:%08lx:%08lx",
        (unsigned long)child.dwVolumeSerialNumber,(unsigned long)child.nFileIndexHigh,
        (unsigned long)child.nFileIndexLow,(unsigned long)child.ftCreationTime.dwHighDateTime,
        (unsigned long)child.ftCreationTime.dwLowDateTime);
    native->volume_serial=child.dwVolumeSerialNumber;native->file_high=child.nFileIndexHigh;native->file_low=child.nFileIndexLow;
    return a>0&&(size_t)a<pool_size&&b>0&&(size_t)b<workspace_size?0:EOVERFLOW;
}
static int ws_native_open_v1(WsNativeV1* native,const char* kind,const char* parent,
        const char* leaf,const char* expected_pool,const char* expected_workspace,
        uint32_t quota,int64_t hard,int64_t* used,int64_t* inodes) {
    memset(native,0,sizeof(*native));
    if(strcmp(kind,"windows-dedicated-volume-v1")||quota)return ENOTSUP;
    if(ws_windows_path_v1(parent,native->parent_path,4096))return EINVAL;
    size_t count=wcslen(native->parent_path);
    if(count<12||wcsncmp(native->parent_path,L"\\\\?\\Volume{",11)||native->parent_path[count-1]!=L'\\')return EINVAL;
    wchar_t name[128];if(ws_windows_path_v1(leaf,name,128))return EINVAL;
    if(swprintf(native->workspace_path,4224,L"%ls%ls",native->parent_path,name)<0)return EINVAL;
    native->parent=CreateFileW(native->parent_path,FILE_READ_ATTRIBUTES|READ_CONTROL,
        FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,
        FILE_FLAG_BACKUP_SEMANTICS|FILE_FLAG_OPEN_REPARSE_POINT,NULL);
    if(native->parent==INVALID_HANDLE_VALUE)return ws_windows_error_v1();
    int error=ws_windows_protected_parent_v1(native->parent);if(error)return error;
    native->workspace=CreateFileW(native->workspace_path,FILE_READ_ATTRIBUTES,
        FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,
        FILE_FLAG_BACKUP_SEMANTICS|FILE_FLAG_OPEN_REPARSE_POINT,NULL);
    if(native->workspace==INVALID_HANDLE_VALUE)return ws_windows_error_v1();
    char pool[256],workspace[256];
    error=ws_windows_identity_v1(native,pool,sizeof(pool),workspace,sizeof(workspace));if(error)return error;
    if(strcmp(pool,expected_pool)||strcmp(workspace,expected_workspace))return ESTALE;
    wchar_t volume[4096];memcpy(volume,native->parent_path,(count+1)*sizeof(wchar_t));volume[count-1]=0;
    native->volume=CreateFileW(volume,GENERIC_READ|GENERIC_WRITE,FILE_SHARE_READ|FILE_SHARE_WRITE,
        NULL,OPEN_EXISTING,0,NULL);
    if(native->volume==INVALID_HANDLE_VALUE)return ws_windows_error_v1();
    return ws_windows_measure_v1(native,hard,used,inodes);
}
static int ws_native_observe_v1(WsNativeV1* native,const char* leaf,const char* pool,
        const char* workspace,int64_t hard,int64_t* used,int64_t* inodes) {
    (void)leaf;
    if(!native->parent||!native->workspace)return ESTALE;
    HANDLE current=CreateFileW(native->workspace_path,FILE_READ_ATTRIBUTES,
        FILE_SHARE_READ|FILE_SHARE_WRITE|FILE_SHARE_DELETE,NULL,OPEN_EXISTING,
        FILE_FLAG_BACKUP_SEMANTICS|FILE_FLAG_OPEN_REPARSE_POINT,NULL);
    if(current==INVALID_HANDLE_VALUE)return ws_windows_error_v1();
    BY_HANDLE_FILE_INFORMATION identity;
    int equal=GetFileInformationByHandle(current,&identity)&&!(identity.dwFileAttributes&FILE_ATTRIBUTE_REPARSE_POINT)&&
        identity.dwVolumeSerialNumber==native->volume_serial&&identity.nFileIndexHigh==native->file_high&&identity.nFileIndexLow==native->file_low;
    CloseHandle(current);if(!equal)return ESTALE;
    char actual_pool[256],actual_workspace[256];
    int error=ws_windows_identity_v1(native,actual_pool,sizeof(actual_pool),actual_workspace,sizeof(actual_workspace));
    if(error)return error;
    if(strcmp(pool,actual_pool)||strcmp(workspace,actual_workspace))return ESTALE;
    error=ws_windows_protected_parent_v1(native->parent);if(error)return error;
    return ws_windows_measure_v1(native,hard,used,inodes);
}
static int ws_native_release_if_absent_v1(WsNativeV1* native,const char* leaf,
        int64_t hard,int64_t* used,int64_t* inodes) {
    (void)native;(void)leaf;(void)hard;(void)used;(void)inodes;
    /* Workspace absence plus a volume lock cannot prove no renamed/recycled
     * data remains. A separately authorized exact-volume disposal or verified
     * empty owner is required. Preserve every handle and host charge. */
    return ENOTSUP;
}

#endif
