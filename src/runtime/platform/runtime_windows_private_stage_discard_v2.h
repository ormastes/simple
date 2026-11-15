/* Exact private created-stage retirement, using the existing kind-2 owner.
 * No pathname reopen, root adoption, foreign HANDLE or separate registry. */
#ifndef SIMPLE_WINDOWS_PRIVATE_STAGE_DISCARD_V2_H
#define SIMPLE_WINDOWS_PRIVATE_STAGE_DISCARD_V2_H
#if defined(_WIN32)
static int wps_discard_temporaries_v2(WpEntryV1 *entry) {
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
/* 1 discarded and released, 2 known published owner released WITHOUT delete,
 * 3 pending-only owner released (no file/namespace was ever acquired),
 * 0 retained failure, -1 rejected authority, -2 exact stale generation.
 * Only the successful disposition flag permits retry without namespace
 * revalidation: its only remaining operation is closing this exact owner. */
int64_t rt_windows_private_stage_discard_v2(int64_t root_token,int64_t stage_token) {
    AcquireSRWLockExclusive(&wp_lock_v1);
    WpEntryV1 *entry=wp_find_v1(stage_token,2),*root=wp_find_v1(root_token,1);
    int64_t result=-2;wp_active_v1=entry;
    if (!entry) goto done;
    result=-1;
    if (!entry->created_stage || entry->root_token!=root_token) goto done;
    /* Failed admission can retain security TOKEN/LocalFree ownership before
     * NtCreateFile acquired any file. Collect that exact pending-only owner;
     * an absent original name must not strand resources or imply deletion. */
    if (!entry->owner && !entry->original_stage_name[0] &&
        !entry->stage_disposition_set && !entry->stage_publication_confirmed) {
        result=wp_cleanup_v1(entry)?3:0;goto done;
    }
    if (!entry->original_stage_name[0]) goto done;
    if (entry->stage_publication_confirmed) {
        /* This fact was set at rename success, before fallible verification.
         * Cleanup releases only owned handles; it never infers publication
         * from a pathname query and never deletes a published destination. */
        result=wp_cleanup_v1(entry)?2:0;goto done;
    }
    if (entry->stage_disposition_set) {
        result=wp_cleanup_v1(entry);goto done;
    }
    /* Defensive refusal for any legacy phase-2 entry without the new fact. */
    if (entry->phase==2 || !entry->owner || !root) goto done;
    entry->phase=3;result=0;
    if (!wps_discard_temporaries_v2(entry) || !wps_discard_temporaries_v2(root) ||
        !wp_root_valid_v1(root) ||
        !wp_kind_v1((HANDLE)entry->owner,0,entry->maximum) ||
        !wp_security_v1((HANDLE)entry->owner,1)) goto done;
    FILE_ID_INFO current;
    if (!GetFileInformationByHandleEx((HANDLE)entry->owner,FileIdInfo,&current,sizeof(current))) goto done;
    if (entry->original_stage_identity_ready &&
        memcmp(&current,&entry->original_stage_identity,sizeof(current))) goto done;
    /* The name was captured at FILE_CREATE while this generation acquired
     * its retained HANDLE. If the initial identity query failed, phase 3 has
     * barred publication ever since; recovery still uses that same HANDLE. */
    if (!wp_final_binding_v2((WpRootV1*)root->owner,(HANDLE)entry->owner,
        entry->original_stage_name,&current) || !wp_root_valid_v1(root) || wp_pending_v1(entry)) goto done;
    entry->original_stage_identity=current;entry->original_stage_identity_ready=1;
    FILE_DISPOSITION_INFO disposition;disposition.DeleteFile=TRUE;
    if (!SetFileInformationByHandle((HANDLE)entry->owner,FileDispositionInfo,&disposition,sizeof(disposition))) goto done;
    /* Consume namespace authority before any fallible close. Failed close
     * keeps this flag, generation, HANDLE and security temporaries retryable. */
    entry->stage_disposition_set=1;
    result=wp_cleanup_v1(entry);
done:
    wp_active_v1=NULL;ReleaseSRWLockExclusive(&wp_lock_v1);return result;
}
#else
int64_t rt_windows_private_stage_discard_v2(int64_t root,int64_t stage) {
    (void)root;(void)stage;return -1;
}
#endif
#endif
