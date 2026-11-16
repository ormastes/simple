/* Retained journal owner. Included after private-root definitions; no native
 * handle or pathname construction port is exported. Kind 5 shares the private
 * registry lock, so copied Simple owners cannot interleave CAS operations. */
#ifndef SIMPLE_WINDOWS_JOURNAL_STORE_V1_H
#define SIMPLE_WINDOWS_JOURNAL_STORE_V1_H
#define WJ_MAX_V1 8388608
#if defined(_WIN32)
typedef struct {
    uint64_t sequence;
    uint8_t *payload;
    int64_t length;
    int phase; /* 0 free, 1 prepared/uncertain, 2 published, 3 consumed */
    wchar_t name[69];
} WjConsumptionV1;
static uint64_t wj_consumption_sequence_v1;
typedef struct {
    WpRootV1 *root;
    FILE_ID_INFO ancestry[WP_DEPTH_V1], lock_id, stage_id;
    unsigned depth;
    HANDLE lock, directories[3], file;
    FILE_ID_INFO directory_ids[3];
    wchar_t directory_names[3][129], stage_name[129], target_name[129];
    int directory_count, locked, ready, closing, stage, rename_attempted;
    uint64_t serial;
    WjConsumptionV1 consumption[64];
    int64_t consumption_bytes;
} WjStoreV1;

/* Only canonical ASCII names are admitted, including on NT namespace calls.
 * Backslashes, ADS, Win32 trimming, device names and internal names cannot be
 * used to escape the bounded retained directory walk. */
static int wj_parts_v1(const wchar_t *path,wchar_t parts[4][129],int *count) {
    if (!path) return 0;
    size_t total=0;int part=0,length=0;
    for (const wchar_t *cursor=path;;cursor++) {
        wchar_t ch=*cursor;
        if (total++>512) return 0;
        if (!ch || ch==L'/') {
            if (!length || part>=4) return 0;
            parts[part][length]=0;
            if (!wcscmp(parts[part],L".") || !wcscmp(parts[part],L"..") ||
                parts[part][length-1]==L'.' ||
                !_wcsnicmp(parts[part],L".journal-stage-",15) ||
                !_wcsicmp(parts[part],L"parent.lock")) return 0;
            /* NT itself does not expand DOS device aliases, but refusing them
             * keeps the admitted namespace canonical across future tooling. */
            wchar_t base[129];wcscpy(base,parts[part]);wchar_t *dot=wcschr(base,L'.');
            if (dot) *dot=0;
            if (!_wcsicmp(base,L"CON") || !_wcsicmp(base,L"PRN") ||
                !_wcsicmp(base,L"AUX") || !_wcsicmp(base,L"NUL") ||
                (wcslen(base)==4 && (!_wcsnicmp(base,L"COM",3) ||
                    !_wcsnicmp(base,L"LPT",3)) && base[3]>=L'0' && base[3]<=L'9')) return 0;
            part++;length=0;if (!ch) {*count=part;return 1;}
            if (part==4) return 0;
        } else {
            if (length>=128 || !((ch>=L'a' && ch<=L'z') ||
                (ch>=L'A' && ch<=L'Z') || (ch>=L'0' && ch<=L'9') ||
                ch==L'_' || ch==L'-' || ch==L'.')) return 0;
            parts[part][length++]=ch;
        }
    }
}
static int wj_missing_v1(NTSTATUS status) {
    return (uint32_t)status==0xc0000034u || (uint32_t)status==0xc000003au;
}
static int wj_consumption_name_v1(wchar_t parts[4][129],int count) {
    if (count!=2 || wcscmp(parts[0],L"primary-connection-consumed") ||
        wcslen(parts[1])!=68 || wcscmp(parts[1]+64,L".sdn")) return 0;
    for (int index=0;index<64;index++)
        if (!((parts[1][index]>=L'0' && parts[1][index]<=L'9') ||
            (parts[1][index]>=L'a' && parts[1][index]<=L'f'))) return 0;
    return 1;
}
static void wj_consumption_release_v1(WjStoreV1 *store,WjConsumptionV1 *receipt) {
    if (receipt->payload) {
        store->consumption_bytes-=receipt->length;free(receipt->payload);receipt->payload=NULL;
    }
    receipt->length=0;receipt->phase=3;
}
/* Every acquired HANDLE is attached immediately to its bounded owner slot,
 * including failed admission. OPEN_IF supplies a private descriptor only for
 * creation and still validates the actual existing descriptor afterward. */
static NTSTATUS wj_open_v1(HANDLE parent,const wchar_t *name,int directory,
    ULONG disposition,int mode,HANDLE *owned) {
    if (*owned || !wp_name_v1(name) || wp_pending_v1(wp_active_v1)) return (NTSTATUS)0xc000000du;
    HMODULE library=GetModuleHandleW(L"ntdll.dll");
    WpCreateV1 open=library?(WpCreateV1)GetProcAddress(library,"NtCreateFile"):NULL;
    TOKEN_USER *user=open?wp_user_v1():NULL;if (!user) return (NTSTATUS)0xc0000022u;
    DWORD size=sizeof(ACL)+sizeof(ACCESS_ALLOWED_ACE)+GetLengthSid(user->User.Sid);
    PACL acl=(PACL)malloc(size);SECURITY_DESCRIPTOR descriptor;
    int ok=acl && InitializeAcl(acl,size,ACL_REVISION) &&
        AddAccessAllowedAce(acl,ACL_REVISION,FILE_ALL_ACCESS,user->User.Sid) &&
        InitializeSecurityDescriptor(&descriptor,SECURITY_DESCRIPTOR_REVISION) &&
        SetSecurityDescriptorOwner(&descriptor,user->User.Sid,FALSE) &&
        SetSecurityDescriptorDacl(&descriptor,TRUE,acl,FALSE) &&
        SetSecurityDescriptorControl(&descriptor,SE_DACL_PROTECTED,SE_DACL_PROTECTED);
    NTSTATUS status=(NTSTATUS)0xc0000017u;
    if (ok) {
        UNICODE_STRING string;string.Buffer=(PWSTR)name;
        string.Length=(USHORT)(wcslen(name)*sizeof(wchar_t));string.MaximumLength=string.Length;
        OBJECT_ATTRIBUTES attributes;memset(&attributes,0,sizeof(attributes));
        attributes.Length=sizeof(attributes);attributes.RootDirectory=parent;
        attributes.ObjectName=&string;attributes.Attributes=OBJ_CASE_INSENSITIVE;
        attributes.SecurityDescriptor=disposition==1?NULL:&descriptor;
        IO_STATUS_BLOCK result;HANDLE handle=NULL;
        ACCESS_MASK access=READ_CONTROL|FILE_READ_ATTRIBUTES|SYNCHRONIZE;
        access|=directory?FILE_LIST_DIRECTORY|FILE_TRAVERSE|FILE_ADD_FILE|FILE_ADD_SUBDIRECTORY:
            (mode==0?GENERIC_READ:(GENERIC_READ|GENERIC_WRITE));
        if (!directory && mode==1) access|=DELETE;
        ULONG share=directory?FILE_SHARE_READ|FILE_SHARE_WRITE:
            (mode==2?FILE_SHARE_READ|FILE_SHARE_WRITE:(mode==0?FILE_SHARE_READ|FILE_SHARE_DELETE:0));
        status=open(&handle,access,&attributes,&result,NULL,FILE_ATTRIBUTE_NORMAL,share,
            disposition,0x00200000|0x20|(directory?1:0x40),NULL,0);
        if (status>=0) *owned=handle;
    }
    free(acl);free(user);return status;
}
static int wj_identity_v1(HANDLE handle,FILE_ID_INFO *identity) {
    return GetFileInformationByHandleEx(handle,FileIdInfo,identity,sizeof(*identity));
}
static int wj_same_v1(HANDLE handle,const FILE_ID_INFO *expected) {
    FILE_ID_INFO current;return wj_identity_v1(handle,&current) && !memcmp(&current,expected,sizeof(current));
}
static HANDLE wj_parent_v1(WjStoreV1 *store) {
    return store->directory_count?store->directories[store->directory_count-1]:store->root->directory;
}
static int wj_directories_current_v1(WjStoreV1 *store) {
    WpRootV1 parent;memset(&parent,0,sizeof(parent));parent.directory=store->root->directory;
    for (int index=0;index<store->directory_count;index++) {
        HANDLE directory=store->directories[index];
        if (!wp_kind_v1(directory,1,0) || !wp_security_v1(directory,1) ||
            !wp_final_binding_v2(&parent,directory,store->directory_names[index],&store->directory_ids[index])) return 0;
        parent.directory=directory;
    }
    return !wp_pending_v1(wp_active_v1);
}
static int wj_current_v1(WpEntryV1 *entry) {
    WjStoreV1 *store=entry?(WjStoreV1*)entry->owner:NULL;
    if (!store || !store->ready || store->closing || !store->locked ||
        entry->phase==3 || wp_pending_v1(entry) ||
        !wp_root_ready_impl_v1((int64_t)(intptr_t)store->root)) return 0;
    unsigned index=0;
    for (WpRootV1 *root=store->root;root;root=root->parent) {
        if (index>=store->depth || !wj_same_v1(root->directory,&store->ancestry[index++])) return 0;
    }
    if (index!=store->depth || !store->root->parent ||
        !wp_security_v1(store->root->parent->directory,1) ||
        !wp_final_binding_v2(store->root->parent,store->root->directory,L"journal",&store->ancestry[0]) ||
        !wp_kind_v1(store->lock,0,0) || !wp_security_v1(store->lock,1) ||
        !wp_final_binding_v2(store->root,store->lock,L"parent.lock",&store->lock_id)) return 0;
    return wj_directories_current_v1(store);
}
static int wj_pending_cleanup_v1(WpEntryV1 *entry) {
    for (int index=0;index<WP_PENDING_V1;index++) {
        if (entry->pending_handles[index]) {
            if (!CloseHandle(entry->pending_handles[index])) return 0;
            entry->pending_handles[index]=NULL;
        }
        if (entry->pending_memory[index]) {
            if (LocalFree(entry->pending_memory[index])) return 0;
            entry->pending_memory[index]=NULL;
        }
    }
    return 1;
}
/* A failed rename is an uncertain effect. Resolve by retained identity and
 * final native binding, never by reopening a path or deleting the destination.
 * If neither binding is provable, retain the lock and all ownership for retry. */
static int wj_transient_cleanup_v1(WpEntryV1 *entry) {
    WjStoreV1 *store=(WjStoreV1*)entry->owner;
    if (!wj_pending_cleanup_v1(entry)) return 0;
    if (store->file) {
        if (store->stage) {
            WpRootV1 parent;memset(&parent,0,sizeof(parent));parent.directory=wj_parent_v1(store);
            if (store->rename_attempted && wp_final_binding_v2(&parent,store->file,store->target_name,&store->stage_id)) {
                store->stage=0;
            } else {
                if (store->rename_attempted &&
                    !wp_final_binding_v2(&parent,store->file,store->stage_name,&store->stage_id)) return 0;
                FILE_DISPOSITION_INFO disposition;disposition.DeleteFile=TRUE;
                if (!SetFileInformationByHandle(store->file,FileDispositionInfo,&disposition,sizeof(disposition))) return 0;
                store->stage=0;
            }
        }
        if (!CloseHandle(store->file)) return 0;
        store->file=NULL;store->rename_attempted=0;
    }
    while (store->directory_count) {
        int index=store->directory_count-1;
        if (!CloseHandle(store->directories[index])) return 0;
        store->directories[index]=NULL;store->directory_count--;
    }
    return wj_pending_cleanup_v1(entry);
}
static int wj_cleanup_v1(WpEntryV1 *entry) {
    WjStoreV1 *store=(WjStoreV1*)entry->owner;entry->phase=3;
    if (!store) {
        if (!wj_pending_cleanup_v1(entry)) return 0;
        memset(entry,0,sizeof(*entry));return 1;
    }
    store->closing=1;store->ready=0;
    if (!wj_transient_cleanup_v1(entry)) return 0;
    /* Close even the duplicated ancestry before releasing the byte lock.
     * A failed close keeps this generation and the exact parent lock owned. */
    if (!wp_close_v1(&store->root)) return 0;
    if (store->locked) {
        OVERLAPPED offset;memset(&offset,0,sizeof(offset));
        if (!UnlockFileEx(store->lock,0,1,0,&offset)) return 0;
        store->locked=0;
    }
    if (store->lock) {
        if (!CloseHandle(store->lock)) return 0;
        store->lock=NULL;
    }
    for (int index=0;index<64;index++) wj_consumption_release_v1(store,&store->consumption[index]);
    free(store);memset(entry,0,sizeof(*entry));return 1;
}
static int64_t wj_fail_v1(WpEntryV1 *entry) {
    if (entry) {entry->phase=3;if (entry->owner) ((WjStoreV1*)entry->owner)->closing=1;}
    return -1;
}
/* 1 = opened, 0 = exact missing, -1 = error; every nonempty slot is retained.
 * Only write operations create the caller-admitted descendant directories. */
static int wj_walk_v1(WjStoreV1 *store,wchar_t parts[4][129],int count,int create) {
    if (store->directory_count || store->file) return -1;
    for (int index=0;index<count-1;index++) {
        HANDLE parent=wj_parent_v1(store);
        NTSTATUS status=wj_open_v1(parent,parts[index],1,create?3:1,0,&store->directories[index]);
        if (status<0) return wj_missing_v1(status)?0:-1;
        store->directory_count++;
        wcscpy(store->directory_names[index],parts[index]);
        if (!wj_identity_v1(store->directories[index],&store->directory_ids[index]) ||
            !wj_directories_current_v1(store)) return -1;
    }
    return 1;
}
static int wj_file_current_v1(WjStoreV1 *store,const wchar_t *name,
    const FILE_ID_INFO *identity,int64_t maximum) {
    WpRootV1 parent;memset(&parent,0,sizeof(parent));parent.directory=wj_parent_v1(store);
    return wj_directories_current_v1(store) && wp_kind_v1(store->file,0,maximum) &&
        wp_security_v1(store->file,1) && wp_final_binding_v2(&parent,store->file,name,identity) &&
        !wp_pending_v1(wp_active_v1);
}
static int wj_utf8_v1(const uint8_t *bytes,int64_t length) {
    return length==0 || (bytes && length>0 && length<=WJ_MAX_V1 &&
        MultiByteToWideChar(CP_UTF8,MB_ERR_INVALID_CHARS,(const char*)bytes,(int)length,NULL,0)>0);
}
/* Replacement also admits the actual destination object before touching its
 * name. A reparse, hard link, oversized object or insecure ACL is an error,
 * never a permission to repair or overwrite somebody else's object. */
static int wj_inspect_leaf_v1(WjStoreV1 *store,const wchar_t *name) {
    NTSTATUS status=wj_open_v1(wj_parent_v1(store),name,0,1,0,&store->file);
    if (status<0) return wj_missing_v1(status)?0:-1;
    FILE_ID_INFO identity;
    if (!wj_identity_v1(store->file,&identity) ||
        !wj_file_current_v1(store,name,&identity,WJ_MAX_V1)) return -1;
    if (!CloseHandle(store->file)) return -1;
    store->file=NULL;return 1;
}
/* Actual payload bytes and metadata are compared while the private registry
 * lock excludes all aliases. FILE_SHARE_WRITE is denied for the entire read. */
static int64_t wj_read_leaf_v1(WjStoreV1 *store,const wchar_t *name,
    uint8_t *buffer,int64_t maximum) {
    NTSTATUS status=wj_open_v1(wj_parent_v1(store),name,0,1,0,&store->file);
    if (status<0) return wj_missing_v1(status)?-2:-1;
    FILE_ID_INFO identity;FILE_BASIC_INFO before,after;LARGE_INTEGER size,final_size;
    if (!wj_identity_v1(store->file,&identity) ||
        !wj_file_current_v1(store,name,&identity,maximum) ||
        !GetFileInformationByHandleEx(store->file,FileBasicInfo,&before,sizeof(before)) ||
        !GetFileSizeEx(store->file,&size) || size.QuadPart<0 || size.QuadPart>maximum) return -1;
    int64_t offset=0;
    while (offset<size.QuadPart) {
        DWORD count=0,wanted=(DWORD)(size.QuadPart-offset>65536?65536:size.QuadPart-offset);
        if (!ReadFile(store->file,buffer+offset,wanted,&count,NULL) || count!=wanted) return -1;
        offset+=wanted;
    }
    if (!wj_file_current_v1(store,name,&identity,maximum) ||
        !GetFileInformationByHandleEx(store->file,FileBasicInfo,&after,sizeof(after)) ||
        !GetFileSizeEx(store->file,&final_size) || final_size.QuadPart!=size.QuadPart ||
        before.LastWriteTime.QuadPart!=after.LastWriteTime.QuadPart ||
        before.ChangeTime.QuadPart!=after.ChangeTime.QuadPart ||
        !wj_utf8_v1(buffer,size.QuadPart)) return -1;
    if (!CloseHandle(store->file)) return -1;
    store->file=NULL;return size.QuadPart;
}
int64_t rt_windows_journal_open_v1(int64_t root_token) {
    AcquireSRWLockExclusive(&wp_lock_v1);
    WpEntryV1 *parent=wp_find_v1(root_token,1);int64_t token=parent?wp_reserve_v1(5):-1;
    if (token==-1) goto done;
    WpEntryV1 *entry=wp_find_v1(token,5);wp_active_v1=entry;
    WjStoreV1 *store=(WjStoreV1*)calloc(1,sizeof(*store));entry->owner=store;
    if (!store || !wp_root_valid_v1(parent)) goto rejected;
    /* Clone the retained chain before opening the fixed child; never borrow
     * parent ownership or reconstruct its path. */
    store->root=(WpRootV1*)calloc(1,sizeof(*store->root));
    if (!store->root) goto rejected;
    store->root->directory=INVALID_HANDLE_VALUE;
    WpRootV1 **tail=&store->root->parent;
    for (WpRootV1 *item=(WpRootV1*)parent->owner;item;item=item->parent) {
        if (++store->depth>=WP_DEPTH_V1) goto rejected;
        WpRootV1 *copy=(WpRootV1*)calloc(1,sizeof(*copy));if (!copy) goto rejected;
        copy->directory=INVALID_HANDLE_VALUE;*tail=copy;tail=&copy->parent;
        HANDLE duplicate=NULL;
        if (!DuplicateHandle(GetCurrentProcess(),item->directory,GetCurrentProcess(),&duplicate,0,FALSE,DUPLICATE_SAME_ACCESS)) goto rejected;
        copy->directory=duplicate;
    }
    HANDLE journal=NULL;
    if (wj_open_v1(((WpRootV1*)parent->owner)->directory,L"journal",1,3,0,&journal)<0) goto rejected;
    store->root->directory=journal;store->root->ready=1;store->depth++;
    unsigned index=0;
    for (WpRootV1 *item=store->root;item;item=item->parent)
        if (!wj_identity_v1(item->directory,&store->ancestry[index++])) goto rejected;
    if (!wp_root_ready_impl_v1((int64_t)(intptr_t)store->root) ||
        wj_open_v1(journal,L"parent.lock",0,3,2,&store->lock)<0 ||
        !wp_kind_v1(store->lock,0,0) || !wp_security_v1(store->lock,1) ||
        !wj_identity_v1(store->lock,&store->lock_id)) goto rejected;
    OVERLAPPED offset;memset(&offset,0,sizeof(offset));
    if (!LockFileEx(store->lock,LOCKFILE_EXCLUSIVE_LOCK|LOCKFILE_FAIL_IMMEDIATELY,0,1,0,&offset)) goto rejected;
    store->locked=1;store->ready=1;
    if (!wj_current_v1(entry)) goto rejected;
    goto done;
rejected:
    /* Once an owner exists, report a cleanup-capable generation even when a
     * best-effort close might succeed. In particular, directory creation and
     * failed admission never become an unqualified constructor rejection. */
    if (store) wj_fail_v1(entry);
    else if (wj_cleanup_v1(entry)) token=-1;
done:
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return token;
}
int64_t rt_windows_journal_live_v1(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,5);wp_active_v1=entry;
    int current=wj_current_v1(entry);if (entry && !current) wj_fail_v1(entry);
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return current;
}
int64_t rt_windows_journal_read_v1(int64_t token,int64_t raw_path,int64_t raw_buffer,int64_t maximum) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,5);wp_active_v1=entry;
    int64_t result=-1;wchar_t parts[4][129];int count=0;
    if (!entry || maximum<0 || maximum>WJ_MAX_V1 || !raw_buffer ||
        !wj_parts_v1((const wchar_t*)(intptr_t)raw_path,parts,&count)) goto done;
    if (!wj_current_v1(entry)) goto failed;
    WjStoreV1 *store=(WjStoreV1*)entry->owner;
    int walk=wj_walk_v1(store,parts,count,0);
    result=walk==0?-2:(walk<0?-1:wj_read_leaf_v1(store,parts[count-1],(uint8_t*)(intptr_t)raw_buffer,maximum));
    if (result==-1 || !wj_current_v1(entry) || !wj_transient_cleanup_v1(entry)) goto failed;
    goto done;
failed:
    result=wj_fail_v1(entry);
done:
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
static int64_t wj_write_v1(int64_t token,int64_t raw_path,int64_t raw_payload,int64_t length,
    int mode,int64_t raw_expected,int64_t expected_length) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,5);wp_active_v1=entry;
    int64_t result=-1;wchar_t parts[4][129];int count=0;
    const wchar_t *path=(const wchar_t*)(intptr_t)raw_path;
    const uint8_t *payload=(const uint8_t*)(intptr_t)raw_payload;
    if (!entry || length<0 || length>WJ_MAX_V1 || !wj_utf8_v1(payload,length) ||
        !wj_parts_v1(path,parts,&count) ||
        (mode==1 && wcscmp(path,L"parent.lease")) ||
        (mode==3 && !wj_consumption_name_v1(parts,count)) ||
        (mode==2 && (wcscmp(path,L"database-wal/CURRENT") || expected_length < -1 ||
            expected_length>WJ_MAX_V1 || (expected_length>=0 && !wj_utf8_v1((const uint8_t*)(intptr_t)raw_expected,expected_length))))) goto done;
    if (!wj_current_v1(entry)) goto failed;
    WjStoreV1 *store=(WjStoreV1*)entry->owner;
    WjConsumptionV1 *receipt=NULL;
    if (mode==3) {
        if (wj_consumption_sequence_v1>=(uint64_t)INT64_MAX ||
            length>WJ_MAX_V1-store->consumption_bytes) goto done;
        for (int index=0;index<64;index++)
            if (store->consumption[index].phase==0 || store->consumption[index].phase==3) {
                receipt=&store->consumption[index];break;
            }
        if (!receipt) goto done;
    }
    if (mode==2) {
        uint8_t *observed=(uint8_t*)malloc(WJ_MAX_V1);if (!observed) goto done;
        int walk=wj_walk_v1(store,parts,count,0);
        int64_t size=walk==0?-2:(walk<0?-1:wj_read_leaf_v1(store,parts[count-1],observed,WJ_MAX_V1));
        int match=expected_length<0?size==-2:
            (size==expected_length && (!size || !memcmp(observed,(const void*)(intptr_t)raw_expected,(size_t)size)));
        free(observed);
        if (size==-1 || !wj_current_v1(entry) || !wj_transient_cleanup_v1(entry)) goto failed;
        if (!match) {result=0;goto done;}
    }
    if (wj_walk_v1(store,parts,count,1)!=1) goto failed;
    wcscpy(store->target_name,parts[count-1]);
    int destination=wj_inspect_leaf_v1(store,store->target_name);
    if (destination<0 || !wj_current_v1(entry)) goto failed;
    if ((mode==0 || mode==3) && destination==1) {
        result=0;if (!wj_transient_cleanup_v1(entry)) goto failed;
        goto done;
    }
    if (receipt) {
        receipt->payload=(uint8_t*)malloc((size_t)length+1);
        if (!receipt->payload) goto failed;
        if (length) memcpy(receipt->payload,payload,(size_t)length);
        receipt->length=length;store->consumption_bytes+=length;
        receipt->sequence=++wj_consumption_sequence_v1;receipt->phase=1;
        wcscpy(receipt->name,parts[1]);
    }
    if (store->serial==UINT64_MAX) goto failed;
    store->serial++;
    FILETIME now;GetSystemTimeAsFileTime(&now);
    uint64_t instant=((uint64_t)now.dwHighDateTime<<32)|now.dwLowDateTime;
    /* CREATE, never OPEN_IF, remains authoritative if a crashed process left
     * an identically named stage. Time/PID avoid routine restart collisions. */
    int named=swprintf(store->stage_name,129,L".journal-stage-%lu-%llu-%llu-%llu",
        (unsigned long)GetCurrentProcessId(),(unsigned long long)instant,
        (unsigned long long)entry->generation,(unsigned long long)store->serial);
    if (named<=0 || named>=129) goto failed;
    NTSTATUS opened=wj_open_v1(wj_parent_v1(store),store->stage_name,0,2,1,&store->file);
    if (opened<0) goto failed;
    store->stage=1;store->rename_attempted=0;
    if (!wj_identity_v1(store->file,&store->stage_id) ||
        !wj_file_current_v1(store,store->stage_name,&store->stage_id,0)) goto failed;
    int64_t offset=0;
    while (offset<length) {
        DWORD count_written=0,wanted=(DWORD)(length-offset>65536?65536:length-offset);
        if (!WriteFile(store->file,payload+offset,wanted,&count_written,NULL) || count_written!=wanted) goto failed;
        offset+=wanted;
    }
    LARGE_INTEGER actual;
    if (!FlushFileBuffers(store->file) || !GetFileSizeEx(store->file,&actual) ||
        actual.QuadPart!=length || !wj_current_v1(entry) ||
        !wj_file_current_v1(store,store->stage_name,&store->stage_id,length)) goto failed;
    size_t bytes=wcslen(store->target_name)*sizeof(wchar_t),rename_size=sizeof(FILE_RENAME_INFO)+bytes;
    FILE_RENAME_INFO *rename=(FILE_RENAME_INFO*)calloc(1,rename_size);
    if (!rename) goto failed;
    rename->ReplaceIfExists=mode==1 || mode==2;rename->RootDirectory=wj_parent_v1(store);
    rename->FileNameLength=(DWORD)bytes;memcpy(rename->FileName,store->target_name,bytes);
    store->rename_attempted=1;
    int renamed=SetFileInformationByHandle(store->file,FileRenameInfo,rename,(DWORD)rename_size);
    DWORD error=GetLastError();free(rename);
    if (!renamed) {
        /* A collision after the destination's exact-absence check is an
         * external namespace mutation, not an admitted existing record. */
        (void)error;
        goto failed;
    }
    /* Consume publication before any fallible query or close. */
    store->stage=0;
    if (!wj_current_v1(entry) || !wj_file_current_v1(store,store->target_name,&store->stage_id,length) ||
        !wj_transient_cleanup_v1(entry)) goto failed;
    if (receipt) {receipt->phase=2;result=(int64_t)receipt->sequence;}
    else result=1;
    goto done;
failed:
    result=wj_fail_v1(entry);
done:
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
int64_t rt_windows_journal_publish_v1(int64_t token,int64_t path,int64_t payload,int64_t length,int64_t consumption) {
    if (consumption!=0 && consumption!=1) return -1;
    return wj_write_v1(token,path,payload,length,consumption?3:0,0,-1);
}
int64_t rt_windows_journal_replace_v1(int64_t token,int64_t path,int64_t payload,int64_t length) {
    return wj_write_v1(token,path,payload,length,1,0,-1);
}
int64_t rt_windows_journal_compare_replace_v1(int64_t token,int64_t path,int64_t payload,int64_t length,int64_t expected,int64_t expected_length) {
    return wj_write_v1(token,path,payload,length,2,expected,expected_length);
}
int64_t rt_windows_journal_consumption_claim_v1(int64_t token,int64_t sequence,int64_t raw_expected,int64_t length) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,5);wp_active_v1=entry;
    int64_t result=-1;WjConsumptionV1 *receipt=NULL;WjStoreV1 *store=NULL;
    if (!wj_current_v1(entry)) goto failed;
    store=(WjStoreV1*)entry->owner;
    for (int index=0;index<64;index++)
        if (store->consumption[index].sequence==(uint64_t)sequence &&
            store->consumption[index].phase==2) {receipt=&store->consumption[index];break;}
    if (!receipt) {result=0;goto done;}
    /* No error path can resurrect a copied receipt, including wrong payload,
     * failed allocation, changed record bytes and uncertain native cleanup. */
    receipt->phase=3;
    if (length<0 || length>WJ_MAX_V1 || !wj_utf8_v1((const uint8_t*)(intptr_t)raw_expected,length) ||
        length!=receipt->length || (length && memcmp(receipt->payload,(const void*)(intptr_t)raw_expected,(size_t)length))) {
        result=0;goto done;
    }
    uint8_t *observed=(uint8_t*)malloc((size_t)receipt->length+1);
    if (!observed) goto failed;
    wchar_t parts[4][129];wcscpy(parts[0],L"primary-connection-consumed");wcscpy(parts[1],receipt->name);
    int walk=wj_walk_v1(store,parts,2,0);
    int64_t size=walk==1?wj_read_leaf_v1(store,parts[1],observed,receipt->length):-1;
    int exact=size==receipt->length && (!size || !memcmp(observed,receipt->payload,(size_t)size));
    free(observed);
    if (!exact || !wj_current_v1(entry) || !wj_transient_cleanup_v1(entry)) goto failed;
    result=1;goto done;
failed:
    result=wj_fail_v1(entry);
done:
    if (receipt) wj_consumption_release_v1(store,receipt);
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
int64_t rt_windows_journal_close_v1(int64_t token) {
    AcquireSRWLockExclusive(&wp_lock_v1);WpEntryV1 *entry=wp_find_v1(token,5);wp_active_v1=entry;
    int closed=entry?wj_cleanup_v1(entry):-1;
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return closed;
}
#else
int64_t rt_windows_journal_open_v1(int64_t root) {(void)root;return -1;}
int64_t rt_windows_journal_live_v1(int64_t token) {(void)token;return 0;}
int64_t rt_windows_journal_read_v1(int64_t token,int64_t path,int64_t buffer,int64_t maximum) {
    (void)token;(void)path;(void)buffer;(void)maximum;return -1;
}
int64_t rt_windows_journal_publish_v1(int64_t token,int64_t path,int64_t payload,int64_t length,int64_t consumption) {
    (void)token;(void)path;(void)payload;(void)length;(void)consumption;return -1;
}
int64_t rt_windows_journal_replace_v1(int64_t token,int64_t path,int64_t payload,int64_t length) {
    (void)token;(void)path;(void)payload;(void)length;return -1;
}
int64_t rt_windows_journal_compare_replace_v1(int64_t token,int64_t path,int64_t payload,int64_t length,int64_t expected,int64_t expected_length) {
    (void)token;(void)path;(void)payload;(void)length;(void)expected;(void)expected_length;return -1;
}
int64_t rt_windows_journal_consumption_claim_v1(int64_t token,int64_t sequence,int64_t expected,int64_t length) {
    (void)token;(void)sequence;(void)expected;(void)length;return -1;
}
int64_t rt_windows_journal_close_v1(int64_t token) {(void)token;return -1;}
#endif
#endif
