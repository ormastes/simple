/* Hosted native workspace storage capability. Included once by the hosted
 * runtime owner, or compiled with that owner for the focused native fixture. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "runtime.h"
#include "runtime_workspace_storage_v1.h"
#include <errno.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#if defined(__linux__)
#include <pthread.h>
#include "runtime_workspace_storage_linux_private.h"
#include "runtime_workspace_user_observation_linux_private.h"
#include "runtime_workspace_executable_prep_linux_private.h"
static pthread_mutex_t ws_lock_v1 = PTHREAD_MUTEX_INITIALIZER;
static int ws_lock_acquire_v1(void) { return pthread_mutex_lock(&ws_lock_v1); }
static void ws_lock_release_v1(void) { (void)pthread_mutex_unlock(&ws_lock_v1); }
#elif defined(_WIN32)
#include "runtime_workspace_storage_windows_private.h"
static SRWLOCK ws_lock_v1 = SRWLOCK_INIT;
static int ws_lock_acquire_v1(void) { AcquireSRWLockExclusive(&ws_lock_v1); return 0; }
static void ws_lock_release_v1(void) { ReleaseSRWLockExclusive(&ws_lock_v1); }
#else
typedef struct { int unused; } WsNativeV1;
static int ws_lock_acquire_v1(void) { return ENOTSUP; }
static void ws_lock_release_v1(void) {}
static void ws_native_close_v1(WsNativeV1* n) { (void)n; }
static int ws_native_open_v1(WsNativeV1* n,const char* k,const char* p,const char* l,
    const char* pi,const char* wi,uint32_t q,int64_t h,int64_t* u,int64_t* i) {
    (void)n;(void)k;(void)p;(void)l;(void)pi;(void)wi;(void)q;(void)h;(void)u;(void)i;return ENOTSUP;
}
static int ws_native_observe_v1(WsNativeV1* n,const char* l,const char* p,const char* w,
    int64_t h,int64_t* u,int64_t* i) {(void)n;(void)l;(void)p;(void)w;(void)h;(void)u;(void)i;return ENOTSUP;}
static int ws_native_release_if_absent_v1(WsNativeV1* n,const char* l,int64_t h,int64_t* u,int64_t* i) {
    (void)n;(void)l;(void)h;(void)u;(void)i;return ENOTSUP;
}
#endif

#if !defined(__linux__)
typedef struct { int unavailable; } WsUserNativeV1;
#endif

#define WS_SLOT_COUNT_V1 32
typedef struct {
    int64_t token, hard_bytes, used_bytes, used_inodes;
    uint32_t quota;
    int released, role, busy; /* role1 storage, role2 read-only user observation */
    char kind[64], parent[4096], leaf[128], pool[256], workspace[256], policy[65];
    WsNativeV1 native;
    WsUserNativeV1 user;
} WsSlotV1;
static WsSlotV1 ws_slots_v1[WS_SLOT_COUNT_V1];
static int64_t ws_next_token_v1 = 1;

static int ws_copy_text_v1(int64_t value, char* output, size_t capacity) {
    int64_t count = rt_string_len(value);
    const uint8_t* bytes = rt_string_data(value);
    if (!bytes || count <= 0 || (uint64_t)count >= capacity ||
            memchr(bytes,0,(size_t)count) || memchr(bytes,'\n',(size_t)count) ||
            memchr(bytes,'\r',(size_t)count) || memchr(bytes,'\t',(size_t)count)) return 0;
    memcpy(output, bytes, (size_t)count); output[count] = 0; return 1;
}
static int ws_digest_v1(const char* value) {
    if (strlen(value) != 64) return 0;
    for (size_t i=0;i<64;i++) if (!((value[i]>='0'&&value[i]<='9') ||
            (value[i]>='a'&&value[i]<='f'))) return 0;
    return 1;
}
static int ws_leaf_v1(const char* value) {
    if (!strcmp(value,".") || !strcmp(value,"..")) return 0;
    for (size_t i=0;value[i];i++) {
        unsigned char c=(unsigned char)value[i];
        if (!((c>='a'&&c<='z')||(c>='A'&&c<='Z')||(c>='0'&&c<='9')||c=='_'||c=='-'||c=='.')) return 0;
    }
    return 1;
}
static WsSlotV1* ws_find_v1(int64_t token) {
    if (token <= 0) return NULL;
    for (size_t i=0;i<WS_SLOT_COUNT_V1;i++) if (ws_slots_v1[i].token==token) return &ws_slots_v1[i];
    return NULL;
}
static int64_t ws_open_or_recover_v1(int64_t kind,int64_t parent,int64_t leaf,
        int64_t pool,int64_t workspace,int64_t quota,int64_t hard,int64_t policy,int recover) {
    WsSlotV1 candidate; memset(&candidate,0,sizeof(candidate));
    if (!ws_copy_text_v1(kind,candidate.kind,sizeof(candidate.kind)) ||
            !ws_copy_text_v1(parent,candidate.parent,sizeof(candidate.parent)) ||
            !ws_copy_text_v1(leaf,candidate.leaf,sizeof(candidate.leaf)) ||
            !ws_copy_text_v1(pool,candidate.pool,sizeof(candidate.pool)) ||
            !ws_copy_text_v1(workspace,candidate.workspace,sizeof(candidate.workspace)) ||
            !ws_copy_text_v1(policy,candidate.policy,sizeof(candidate.policy)) ||
            !ws_leaf_v1(candidate.leaf) || !ws_digest_v1(candidate.policy) ||
            quota < 0 || (uint64_t)quota > UINT32_MAX || hard <= 0 || hard > INT64_C(1125899906842624)) return -EINVAL;
    candidate.quota=(uint32_t)quota; candidate.hard_bytes=hard;candidate.role=1;
    int lock_error=ws_lock_acquire_v1(); if(lock_error)return -lock_error;
    size_t slot=WS_SLOT_COUNT_V1;
    for(size_t i=0;i<WS_SLOT_COUNT_V1;i++) {
        WsSlotV1* existing=&ws_slots_v1[i];
        /* One scope may not acquire independent concurrent native leases.
         * Host replay must reuse its live owner or recover after process exit. */
        if(existing->token&&existing->role==1&&(!strcmp(existing->pool,candidate.pool))&&
                (!strcmp(existing->workspace,candidate.workspace)||existing->quota==candidate.quota)) {
            if(recover&&!strcmp(existing->kind,candidate.kind)&&!strcmp(existing->parent,candidate.parent)&&
                    !strcmp(existing->leaf,candidate.leaf)&&!strcmp(existing->workspace,candidate.workspace)&&
                    !strcmp(existing->policy,candidate.policy)&&existing->quota==candidate.quota&&existing->hard_bytes==hard) {
                /* Recover retained cleanup authority even when observation is
                 * currently failing. This is a lease, not a readiness receipt. */
                if(!existing->released&&!existing->busy)(void)ws_native_observe_v1(&existing->native,existing->leaf,existing->pool,
                    existing->workspace,hard,&existing->used_bytes,&existing->used_inodes);
                int64_t token=existing->token;ws_lock_release_v1();return token;
            }
            ws_lock_release_v1();return -EBUSY;
        }
        if(!existing->token&&slot==WS_SLOT_COUNT_V1)slot=i;
    }
    if(slot==WS_SLOT_COUNT_V1||ws_next_token_v1==INT64_MAX) {ws_lock_release_v1();return -ENOSPC;}
    int error=ws_native_open_v1(&candidate.native,candidate.kind,candidate.parent,candidate.leaf,
        candidate.pool,candidate.workspace,candidate.quota,hard,&candidate.used_bytes,&candidate.used_inodes);
    if(error) {ws_native_close_v1(&candidate.native);ws_lock_release_v1();return -error;}
    candidate.token=ws_next_token_v1++;ws_slots_v1[slot]=candidate;
    ws_lock_release_v1();return candidate.token;
}
int64_t rt_workspace_storage_open_v1(int64_t kind,int64_t parent,int64_t leaf,
        int64_t pool,int64_t workspace,int64_t quota,int64_t hard,int64_t policy) {
    return ws_open_or_recover_v1(kind,parent,leaf,pool,workspace,quota,hard,policy,0);
}
int64_t rt_workspace_storage_recover_v1(int64_t kind,int64_t parent,int64_t leaf,
        int64_t pool,int64_t workspace,int64_t quota,int64_t hard,int64_t policy) {
    return ws_open_or_recover_v1(kind,parent,leaf,pool,workspace,quota,hard,policy,1);
}
int64_t rt_workspace_storage_observe_v1(int64_t token) {
    char result[1024]; result[0]=0;
    if(ws_lock_acquire_v1())return rt_string_new((const uint8_t*)"",0);
    WsSlotV1* slot=ws_find_v1(token);
    if(slot&&slot->role==1&&!slot->busy) {
        int error=slot->released?0:ws_native_observe_v1(&slot->native,slot->leaf,slot->pool,
            slot->workspace,slot->hard_bytes,&slot->used_bytes,&slot->used_inodes);
        if(!error) {
            int count=snprintf(result,sizeof(result),"workspace-storage-native-v1\n%s\n%s\n%s\n%u\n%lld\n%lld\n%lld\n%s\n%s\n",
                slot->kind,slot->pool,slot->workspace,slot->quota,(long long)slot->hard_bytes,
                (long long)slot->used_bytes,(long long)slot->used_inodes,slot->policy,
                slot->released?"released":"retained");
            if(count<0||(size_t)count>=sizeof(result))result[0]=0;
        }
    }
    ws_lock_release_v1();return rt_string_new((const uint8_t*)result,strlen(result));
}
int64_t rt_workspace_storage_release_if_absent_v1(int64_t token) {
    int error=ws_lock_acquire_v1();if(error)return -error;
    WsSlotV1* slot=ws_find_v1(token);
    if(!slot||slot->role!=1) {ws_lock_release_v1();return -ESTALE;}
    if(slot->busy){ws_lock_release_v1();return -EBUSY;}
    if(!slot->released) {
        error=ws_native_release_if_absent_v1(&slot->native,slot->leaf,slot->hard_bytes,
            &slot->used_bytes,&slot->used_inodes);
        if(!error)slot->released=1;
    }
    ws_lock_release_v1();return -error;
}
int64_t rt_workspace_storage_forget_released_v1(int64_t token) {
    int error=ws_lock_acquire_v1();if(error)return -error;
    WsSlotV1* slot=ws_find_v1(token);
    if(!slot||slot->role!=1)error=ESTALE;
    else if(slot->busy||!slot->released)error=EBUSY;
    else {ws_native_close_v1(&slot->native);memset(slot,0,sizeof(*slot));}
    ws_lock_release_v1();return -error;
}

int64_t rt_linux_container_user_open_v1(int64_t pid,int64_t cgroup,int64_t binding) {
#if defined(__linux__)
    WsSlotV1 candidate;memset(&candidate,0,sizeof(candidate));candidate.role=2;
    if(pid<=0||pid>INT_MAX||!ws_copy_text_v1(cgroup,candidate.parent,sizeof(candidate.parent))||
            !ws_copy_text_v1(binding,candidate.policy,sizeof(candidate.policy))||!ws_digest_v1(candidate.policy))return -EINVAL;
    int error=ws_lock_acquire_v1();if(error)return -error;
    size_t slot=WS_SLOT_COUNT_V1;
    for(size_t i=0;i<WS_SLOT_COUNT_V1;i++)if(!ws_slots_v1[i].token){slot=i;break;}
    if(slot==WS_SLOT_COUNT_V1||ws_next_token_v1==INT64_MAX){ws_lock_release_v1();return -ENOSPC;}
    error=ws_user_open_v1(&candidate.user,(pid_t)pid,candidate.parent);
    if(error){ws_user_close_v1(&candidate.user);ws_lock_release_v1();return -error;}
    candidate.token=ws_next_token_v1++;ws_slots_v1[slot]=candidate;
    ws_lock_release_v1();return candidate.token;
#else
    (void)pid;(void)cgroup;(void)binding;return -ENOTSUP;
#endif
}
int64_t rt_linux_container_user_observe_v1(int64_t token,int64_t binding) {
    char result[6144];result[0]=0;
#if defined(__linux__)
    char expected[65];
    if(!ws_copy_text_v1(binding,expected,sizeof(expected))||!ws_digest_v1(expected))return rt_string_new((const uint8_t*)"",0);
    if(ws_lock_acquire_v1())return rt_string_new((const uint8_t*)"",0);
    WsSlotV1* slot=ws_find_v1(token);
    if(slot&&slot->role==2&&!slot->busy&&!strcmp(slot->policy,expected)&&!ws_user_refresh_v1(&slot->user,slot->parent)) {
        struct timespec now;
        if(clock_gettime(CLOCK_REALTIME,&now)==0&&now.tv_sec>0&&now.tv_sec<INT64_MAX/1000) {
            WsUserFactsV1* f=&slot->user.facts;
            int count=snprintf(result,sizeof(result),"linux-container-user-native-v1\n%lld\n%ld\n%llu\n%u\n%u\n%u\n%u\n%u\n%u\n%u\n%u\n%llu\n%llu\n%llu\n%llu\n%s\n%s\n%s\n%lld\n%s\n",
                (long long)token,(long)slot->user.pid,(unsigned long long)f->start_ticks,
                f->observer_uid,f->observer_gid,f->effective_uid,f->effective_gid,f->filesystem_uid,f->filesystem_gid,
                f->container_uid,f->container_gid,(unsigned long long)f->target_ns_device,(unsigned long long)f->target_ns_inode,
                (unsigned long long)f->observer_ns_device,(unsigned long long)f->observer_ns_inode,
                f->cgroup,f->uid_digest,f->gid_digest,(long long)now.tv_sec*1000+now.tv_nsec/1000000,slot->policy);
            if(count<0||(size_t)count>=sizeof(result))result[0]=0;
        }
    }
    ws_lock_release_v1();
#else
    (void)token;(void)binding;
#endif
    return rt_string_new((const uint8_t*)result,strlen(result));
}
int64_t rt_linux_container_user_close_v1(int64_t token,int64_t binding) {
#if defined(__linux__)
    char expected[65];
    if(!ws_copy_text_v1(binding,expected,sizeof(expected))||!ws_digest_v1(expected))return -EINVAL;
    int error=ws_lock_acquire_v1();if(error)return -error;
    WsSlotV1* slot=ws_find_v1(token);
    if(!slot||slot->role!=2||strcmp(slot->policy,expected))error=ESTALE;
    else if(slot->busy)error=EBUSY;
    else {ws_user_close_v1(&slot->user);memset(slot,0,sizeof(*slot));}
    ws_lock_release_v1();return -error;
#else
    (void)token;(void)binding;return -ENOTSUP;
#endif
}

int64_t rt_workspace_storage_prepare_executable_v1(int64_t storage_token,int64_t user_token,
        int64_t mapping_binding,int64_t stage_digest,int64_t expires_unix_ms,
        int64_t input_relative,int64_t output_relative,int64_t executable_relative,int64_t expected_digest) {
    char record[12288];record[0]=0;
#if defined(__linux__)
    char mapping[65],stage[65],input[4096],output[4096],executable[64],digest[65];
    if(!ws_copy_text_v1(mapping_binding,mapping,sizeof(mapping))||!ws_digest_v1(mapping)||
       !ws_copy_text_v1(stage_digest,stage,sizeof(stage))||!ws_digest_v1(stage)||
       !ws_copy_text_v1(input_relative,input,sizeof(input))||!ws_copy_text_v1(output_relative,output,sizeof(output))||
       !ws_copy_text_v1(executable_relative,executable,sizeof(executable))||
       !ws_copy_text_v1(expected_digest,digest,sizeof(digest))||!ws_digest_v1(digest))return rt_string_new((const uint8_t*)"",0);
    if(ws_lock_acquire_v1())return rt_string_new((const uint8_t*)"",0);
    WsSlotV1* storage=ws_find_v1(storage_token);WsSlotV1* user=ws_find_v1(user_token);
    if(!storage||!user||storage->role!=1||user->role!=2||storage->released||
            storage->busy||user->busy||strcmp(mapping,user->policy)) {
        ws_lock_release_v1();return rt_string_new((const uint8_t*)"",0);
    }
    /* Scoped loans retain both existing slots while hashing without holding
     * the registry mutex. Release/close refuse busy slots; generations cannot
     * be reused. No second registry, journal, or process-control authority. */
    storage->busy=user->busy=1;ws_lock_release_v1();
    WsExecutablePrepFactsV1 facts;memset(&facts,0,sizeof(facts));
    struct timespec mono,wall;int error=0;int64_t deadline=0;
    /* Sample monotonic first: scheduler delay between samples shortens, never
     * extends, the window. Native processing has an additional 60s bound. */
    if(clock_gettime(CLOCK_MONOTONIC,&mono)||clock_gettime(CLOCK_REALTIME,&wall))error=errno;
    else if(mono.tv_sec<0||wall.tv_sec<0||(uint64_t)mono.tv_sec>((uint64_t)INT64_MAX-999)/1000||
            (uint64_t)wall.tv_sec>((uint64_t)INT64_MAX-999)/1000)error=EOVERFLOW;
    else {
        int64_t now_mono=(int64_t)mono.tv_sec*1000+mono.tv_nsec/1000000;
        int64_t now_wall=(int64_t)wall.tv_sec*1000+wall.tv_nsec/1000000;
        if(expires_unix_ms<=now_wall)error=ETIMEDOUT;
        else {
            int64_t remaining=expires_unix_ms-now_wall;if(remaining>60000)remaining=60000;
            if(now_mono>INT64_MAX-remaining)error=EOVERFLOW;else deadline=now_mono+remaining;
        }
    }
    if(!error)error=ws_native_observe_v1(&storage->native,storage->leaf,storage->pool,
        storage->workspace,storage->hard_bytes,&storage->used_bytes,&storage->used_inodes);
    if(!error)error=ws_user_refresh_v1(&user->user,user->parent);
    if(!error)error=ws_prepare_executable_v1(&storage->native,&user->user,input,output,executable,digest,
        deadline,expires_unix_ms,&facts);
    if(!error) {
        error=ws_native_observe_v1(&storage->native,storage->leaf,storage->pool,
            storage->workspace,storage->hard_bytes,&storage->used_bytes,&storage->used_inodes);
        if(error)facts.state=2;
    }
    facts.error=error;
    int count=snprintf(record,sizeof(record),"workspace-executable-prep-native-v1\n%d\n%d\n%s\n%s\n%s\n%s\n%llu\n%u\n%u\n%s\n%s\n%s\n%s\n%s\n%u\n%lld\n%s\n",
        facts.state,facts.error,input,output,executable,facts.digest,(unsigned long long)facts.size_bytes,
        facts.old_mode,facts.new_mode,facts.file_identity,mapping,stage,storage->pool,storage->workspace,
        storage->quota,(long long)storage->hard_bytes,storage->policy);
    if(count<0||(size_t)count>=sizeof(record))record[0]=0;
    if(ws_lock_acquire_v1()){record[0]=0;} /* Retain busy owners on unknown unlock outcome. */
    else {storage->busy=user->busy=0;ws_lock_release_v1();}
#else
    (void)storage_token;(void)user_token;(void)mapping_binding;(void)stage_digest;(void)expires_unix_ms;
    (void)input_relative;(void)output_relative;(void)executable_relative;(void)expected_digest;
#endif
    return rt_string_new((const uint8_t*)record,strlen(record));
}
