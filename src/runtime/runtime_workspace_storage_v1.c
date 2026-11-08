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
#include <stdatomic.h>
/* Stale capabilities use the host errno vocabulary. The Windows CRT has no
 * ESTALE; EBADF reports an invalid handle without inventing a POSIX errno or
 * exposing a Win32 status through this negative-errno ABI. */
#if defined(_WIN32) && !defined(ESTALE)
#define WS_STALE_ERROR_V1 EBADF
#else
#define WS_STALE_ERROR_V1 ESTALE
#endif
#if defined(__linux__)
#include <unistd.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/ioctl.h>
#include <fcntl.h>
#include <linux/magic.h>
#include <linux/nsfs.h>
#include <sched.h>
#elif defined(_WIN32)
#include <windows.h>
#endif

/* Claim before touching inherited locks, text caches, slots or native handles.
 * A virgin registry may initialize its independent copy. A used registry never
 * resets, adopts or closes copied owners. Publication is one-shot: concurrent
 * or forked callers observing an unfinished claim refuse EAGAIN, never spin.
 * Linux additionally pins the native PID namespace identity. This is an origin
 * fence, not namespace-transition authorization or process supervision. */
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "workspace origin requires lock-free unsigned atomics");
#if defined(__linux__)
_Static_assert(sizeof(pid_t)<=sizeof(unsigned int), "workspace origin PID must fit unsigned int");
#elif defined(_WIN32)
_Static_assert(sizeof(DWORD)<=sizeof(unsigned int), "workspace origin PID must fit unsigned int");
#endif
static atomic_uint ws_process_origin_v1=ATOMIC_VAR_INIT(0);
static atomic_uint ws_origin_ready_v1=ATOMIC_VAR_INIT(0);
/* First established observation failure is permanent in this process copy.
 * Retaining an unproven lock must not turn restored procfs into a later wait
 * on that same retained mutex. Neither quarantine nor origin is reset. */
static atomic_int ws_origin_failure_v1=ATOMIC_VAR_INIT(0);
static int ws_origin_quarantine_v1(int error) {
    if(error<=0)error=EIO;
    int expected=0;
    atomic_compare_exchange_strong_explicit(&ws_origin_failure_v1,&expected,error,
        memory_order_acq_rel,memory_order_acquire);
    return atomic_load_explicit(&ws_origin_failure_v1,memory_order_acquire);
}
#if defined(__linux__)
/* Immutable after the single winning claimant release-publishes ready. */
static uint64_t ws_origin_namespace_device_v1,ws_origin_namespace_inode_v1;
static int ws_origin_namespace_current_v1(uint64_t* device,uint64_t* inode,int validate_object) {
    if(!validate_object) {
        /* The published identity was proven nsfs/CLONE_NEWPID at admission.
         * Compare that exact object without consuming an fd while holding an
         * owner mutex. Unavailable procfs refuses; it never resets authority. */
        struct stat value;if(stat("/proc/self/ns/pid",&value))return errno?errno:EIO;
        *device=(uint64_t)value.st_dev;*inode=(uint64_t)value.st_ino;return 0;
    }
    /* Follow only this kernel namespace magic link. A fresh temporary fd is
     * checked and closed here; no inherited capability descriptor is touched. */
    int fd=open("/proc/self/ns/pid",O_RDONLY|O_CLOEXEC);if(fd<0)return errno?errno:EIO;
    struct stat value;struct statfs filesystem;int error=0;
    if(fstat(fd,&value)||fstatfs(fd,&filesystem))error=errno?errno:EIO;
    else {
        int type=ioctl(fd,NS_GET_NSTYPE);
        if(type<0)error=errno?errno:EIO;
        else if(filesystem.f_type!=NSFS_MAGIC||type!=CLONE_NEWPID)error=ENOTSUP;
    }
    if(close(fd)&&!error)error=errno?errno:EIO;
    if(error)return error;
    *device=(uint64_t)value.st_dev;*inode=(uint64_t)value.st_ino;return 0;
}
static int ws_origin_namespace_equal_v1(uint64_t device,uint64_t inode) {
    return device==ws_origin_namespace_device_v1&&inode==ws_origin_namespace_inode_v1;
}
#endif
static int ws_origin_guard_v1(void) {
    int quarantined=atomic_load_explicit(&ws_origin_failure_v1,memory_order_acquire);
    if(quarantined)return quarantined;
    unsigned int pid;
#if defined(__linux__)
    pid_t observed=getpid();if(observed<=0) {
        if(atomic_load_explicit(&ws_origin_ready_v1,memory_order_acquire))return ws_origin_quarantine_v1(ECHILD);
        return ECHILD;
    }pid=(unsigned int)observed;
#elif defined(_WIN32)
    pid=(unsigned int)GetCurrentProcessId();if(!pid) {
        if(atomic_load_explicit(&ws_origin_ready_v1,memory_order_acquire))return ws_origin_quarantine_v1(ECHILD);
        return ECHILD;
    }
#else
    return ENOTSUP;
#endif
    unsigned int origin=atomic_load_explicit(&ws_process_origin_v1,memory_order_acquire);
    if(origin&&!atomic_load_explicit(&ws_origin_ready_v1,memory_order_acquire))return EAGAIN;
#if defined(__linux__)
    uint64_t namespace_device,namespace_inode;
    int namespace_error=ws_origin_namespace_current_v1(&namespace_device,&namespace_inode,!origin);
    if(namespace_error)return origin?ws_origin_quarantine_v1(namespace_error):namespace_error;
#endif
    if(!origin) {
        unsigned int expected=0;
        if(atomic_compare_exchange_strong_explicit(&ws_process_origin_v1,&expected,pid,
                memory_order_acq_rel,memory_order_acquire)) {
#if defined(__linux__)
            ws_origin_namespace_device_v1=namespace_device;
            ws_origin_namespace_inode_v1=namespace_inode;
#endif
            atomic_store_explicit(&ws_origin_ready_v1,1,memory_order_release);
            return 0;
        }
        origin=expected;
    }
    if(!atomic_load_explicit(&ws_origin_ready_v1,memory_order_acquire))return EAGAIN;
    if(origin!=pid)return ws_origin_quarantine_v1(ECHILD);
#if defined(__linux__)
    if(!ws_origin_namespace_equal_v1(namespace_device,namespace_inode))return ws_origin_quarantine_v1(ECHILD);
#endif
    return 0;
}
/* Core-C text ABI accepts immortal raw literals. Offset two avoids heap tag 1
 * and the aligned data-pointer registry probe in rt_string_len; thus even the
 * rejection representation needs no inherited runtime registry/cache gate.
 * rt_string_free rejects this nonheap literal. Current receipt decoders reject
 * its false newline-suffix check before split; this is not general raw-text
 * equality/split compatibility. Do not call rt_string_new here. */
_Alignas(8) static const uint8_t ws_origin_empty_literal_v1[3]={0,0,0};
static int64_t ws_origin_empty_v1(void) {
    return (int64_t)(uintptr_t)(ws_origin_empty_literal_v1+2);
}

#if defined(__linux__)
#include <pthread.h>
#include "runtime_workspace_storage_linux_private.h"
#include "runtime_workspace_user_observation_linux_private.h"
#include "runtime_workspace_executable_prep_linux_private.h"
#include "runtime_workspace_containment_linux_private.h"
#include "runtime_workspace_kernel_observation_linux_private.h"
static pthread_mutex_t ws_lock_v1 = PTHREAD_MUTEX_INITIALIZER;
static int ws_lock_acquire_v1(void) {
    int error=ws_origin_guard_v1();if(error)return error;
    /* Never queue behind an owner which may retain this mutex on quarantine.
     * Contention is an explicit bounded refusal; callers retain their owner. */
    error=pthread_mutex_trylock(&ws_lock_v1);if(error)return error;
    error=ws_origin_guard_v1();
    /* Proof lost after acquisition: leave the mutex and capability state
     * untouched. Later calls see quarantine before attempting the gate. */
    return error;
}
/* If trusted procfs becomes unavailable while this owner holds the mutex,
 * retain the lock rather than silently reset/unlock unproven authority. The
 * permanent error latch makes every later entry refuse before waiting even if
 * procfs recovers. Existing owners stay retained; process-level recovery is
 * required. Established checks use stat, never a fresh descriptor, so ordinary
 * EMFILE after admission cannot cause this condition. */
static void ws_lock_release_v1(void) { if(!ws_origin_guard_v1())(void)pthread_mutex_unlock(&ws_lock_v1); }
#elif defined(_WIN32)
#include "runtime_workspace_storage_windows_private.h"
static SRWLOCK ws_lock_v1 = SRWLOCK_INIT;
static int ws_lock_acquire_v1(void) { int error=ws_origin_guard_v1();if(error)return error;AcquireSRWLockExclusive(&ws_lock_v1); return 0; }
static void ws_lock_release_v1(void) { if(!ws_origin_guard_v1())ReleaseSRWLockExclusive(&ws_lock_v1); }
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
typedef struct { int unavailable; } WsContainNativeV1;
#endif

#define WS_SLOT_COUNT_V1 32
typedef struct {
    int64_t token, hard_bytes, used_bytes, used_inodes;
    uint32_t quota;
    int released, role; /* role1 storage, role2 user observation, role3 containment observation */
    atomic_int busy; /* Registry admits loans; final borrower releases atomically. */
    char kind[64], parent[4096], leaf[128], pool[256], workspace[256], policy[65];
    WsNativeV1 native;
    WsUserNativeV1 user;
    WsContainNativeV1 containment;
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
    if(ws_origin_guard_v1())return NULL;
    if (token <= 0) return NULL;
    for (size_t i=0;i<WS_SLOT_COUNT_V1;i++) if (ws_slots_v1[i].token==token) return &ws_slots_v1[i];
    return NULL;
}
/* Generic loan mechanism; the public caller obtains these pointers under the
 * registry gate. Tokens and every receipt/native field must be consumed before
 * calling. A live loan prevents close/reuse; no registry reacquisition is needed. */
static int ws_release_busy_pair_v1(WsSlotV1* first,int64_t first_token,
        WsSlotV1* second,int64_t second_token) {
    int error=ws_origin_guard_v1();if(error)return error;
    if(!first||!second||first==second||first_token<=0||second_token<=0)return EINVAL;
    atomic_int* first_busy=&first->busy;atomic_int* second_busy=&second->busy;
    if(atomic_load_explicit(first_busy,memory_order_acquire)!=1||
            atomic_load_explicit(second_busy,memory_order_acquire)!=1)return EBUSY;
    if(first->token!=first_token||second->token!=second_token)return WS_STALE_ERROR_V1;
    error=ws_origin_guard_v1();if(error)return error;
    /* After the first store, either slot may immediately close/reuse. Only the
     * precomputed atomic destinations are used below: no slot reads follow. */
    atomic_store_explicit(first_busy,0,memory_order_release);
    atomic_store_explicit(second_busy,0,memory_order_release);
    return 0;
}
static int64_t ws_open_or_recover_v1(int64_t kind,int64_t parent,int64_t leaf,
        int64_t pool,int64_t workspace,int64_t quota,int64_t hard,int64_t policy,int recover) {
    int origin_error=ws_origin_guard_v1();if(origin_error)return -origin_error;
    WsSlotV1 candidate; memset(&candidate,0,sizeof(candidate));atomic_init(&candidate.busy,0);
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
    int origin_error=ws_origin_guard_v1();if(origin_error)return -origin_error;
    return ws_open_or_recover_v1(kind,parent,leaf,pool,workspace,quota,hard,policy,0);
}
int64_t rt_workspace_storage_recover_v1(int64_t kind,int64_t parent,int64_t leaf,
        int64_t pool,int64_t workspace,int64_t quota,int64_t hard,int64_t policy) {
    int origin_error=ws_origin_guard_v1();if(origin_error)return -origin_error;
    return ws_open_or_recover_v1(kind,parent,leaf,pool,workspace,quota,hard,policy,1);
}
int64_t rt_workspace_storage_observe_v1(int64_t token) {
    int origin_error=ws_origin_guard_v1();if(origin_error)return ws_origin_empty_v1();
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
    int origin_error=ws_origin_guard_v1();if(origin_error)return -origin_error;
    int error=ws_lock_acquire_v1();if(error)return -error;
    WsSlotV1* slot=ws_find_v1(token);
    if(!slot||slot->role!=1) {ws_lock_release_v1();return -WS_STALE_ERROR_V1;}
    if(slot->busy){ws_lock_release_v1();return -EBUSY;}
    if(!slot->released) {
        error=ws_native_release_if_absent_v1(&slot->native,slot->leaf,slot->hard_bytes,
            &slot->used_bytes,&slot->used_inodes);
        if(!error)slot->released=1;
    }
    ws_lock_release_v1();return -error;
}
int64_t rt_workspace_storage_forget_released_v1(int64_t token) {
    int origin_error=ws_origin_guard_v1();if(origin_error)return -origin_error;
    int error=ws_lock_acquire_v1();if(error)return -error;
    WsSlotV1* slot=ws_find_v1(token);
    if(!slot||slot->role!=1)error=WS_STALE_ERROR_V1;
    else if(slot->busy||!slot->released)error=EBUSY;
    else {ws_native_close_v1(&slot->native);memset(slot,0,sizeof(*slot));}
    ws_lock_release_v1();return -error;
}

int64_t rt_linux_container_user_open_v1(int64_t pid,int64_t cgroup,int64_t binding) {
    int origin_error=ws_origin_guard_v1();if(origin_error)return -origin_error;
#if defined(__linux__)
    WsSlotV1 candidate;memset(&candidate,0,sizeof(candidate));atomic_init(&candidate.busy,0);candidate.role=2;
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
    int origin_error=ws_origin_guard_v1();if(origin_error)return ws_origin_empty_v1();
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
    int origin_error=ws_origin_guard_v1();if(origin_error)return -origin_error;
#if defined(__linux__)
    char expected[65];
    if(!ws_copy_text_v1(binding,expected,sizeof(expected))||!ws_digest_v1(expected))return -EINVAL;
    int error=ws_lock_acquire_v1();if(error)return -error;
    WsSlotV1* slot=ws_find_v1(token);
    if(!slot||slot->role!=2||strcmp(slot->policy,expected))error=WS_STALE_ERROR_V1;
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
    int origin_error=ws_origin_guard_v1();if(origin_error)return ws_origin_empty_v1();
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
    atomic_store_explicit(&storage->busy,1,memory_order_release);
    atomic_store_explicit(&user->busy,1,memory_order_release);
    ws_lock_release_v1();
    /* A failed proof check during void unlock quarantines the process. Keep
     * both loans and refuse before any clock/native observation/hash/effect. */
    if(ws_origin_guard_v1())return ws_origin_empty_v1();
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
    /* snprintf above completed the LAST receipt/native-field read. Validate both exact
     * generations and release the loans without competing for the registry.
     * Proof loss preserves both loans and suppresses any success receipt. */
    if(ws_release_busy_pair_v1(storage,storage_token,user,user_token))return ws_origin_empty_v1();
#else
    (void)storage_token;(void)user_token;(void)mapping_binding;(void)stage_digest;(void)expires_unix_ms;
    (void)input_relative;(void)output_relative;(void)executable_relative;(void)expected_digest;
#endif
    return rt_string_new((const uint8_t*)record,strlen(record));
}

/* A positive token means an owner exists, including partial capture. The
 * facade must observe it and return it on every failure; never auto-close. */
int64_t rt_linux_container_containment_capture_v1(int64_t pid,int64_t cgroup,int64_t binding) {
    int error=ws_origin_guard_v1();if(error)return -error;
#if defined(__linux__)
    char path[4096],digest[65];
    if(pid<=0||pid>INT_MAX||!ws_copy_text_v1(cgroup,path,sizeof(path))||!ws_cgroup_path_v1(path)||
       !ws_copy_text_v1(binding,digest,sizeof(digest))||!ws_digest_v1(digest))return -EINVAL;
    error=ws_lock_acquire_v1();if(error)return -error;
    size_t index=WS_SLOT_COUNT_V1;
    for(size_t i=0;i<WS_SLOT_COUNT_V1;i++)if(!ws_slots_v1[i].token){index=i;break;}
    if(index==WS_SLOT_COUNT_V1||ws_next_token_v1==INT64_MAX){ws_lock_release_v1();return -ENOSPC;}
    WsSlotV1* slot=&ws_slots_v1[index];memset(slot,0,sizeof(*slot));atomic_init(&slot->busy,0);
    slot->role=3;slot->token=ws_next_token_v1++;strcpy(slot->policy,digest);strcpy(slot->parent,path);
    ws_contain_init_v1(&slot->containment);
    slot->containment.error=ws_contain_open_v1(&slot->containment,(pid_t)pid,path);
    int64_t token=slot->token;ws_lock_release_v1();return token;
#else
    (void)pid;(void)cgroup;(void)binding;return -ENOTSUP;
#endif
}
int64_t rt_linux_container_containment_observe_v1(int64_t token,int64_t binding) {
    if(ws_origin_guard_v1())return ws_origin_empty_v1();
    char output[6144]={0};
#if defined(__linux__)
    char digest[65];
    if(!ws_copy_text_v1(binding,digest,sizeof(digest))||!ws_digest_v1(digest))return rt_string_new((const uint8_t*)"",0);
    if(ws_lock_acquire_v1())return rt_string_new((const uint8_t*)"",0);
    WsSlotV1* slot=ws_find_v1(token);int populated=-1;
    if(slot&&slot->role==3&&!slot->busy&&!strcmp(slot->policy,digest)&&!ws_contain_observe_v1(&slot->containment,&populated)) {
        WsContainNativeV1* n=&slot->containment;struct timespec now;
        if(!clock_gettime(CLOCK_REALTIME,&now)&&now.tv_sec>0&&now.tv_sec<(INT64_MAX-999)/1000) {
            int used=snprintf(output,sizeof(output),"linux-container-containment-native-v1\n%lld\n%s\n%ld\n%llu\n%s\n%llu\n%llu\n%llu\n%llu\n%llu\n",
                (long long)token,digest,(long)n->pid,(unsigned long long)n->start_ticks,n->path,
                (unsigned long long)n->mount_id,(unsigned long long)n->mount_device,(unsigned long long)n->mount_inode,
                (unsigned long long)n->group_device,(unsigned long long)n->group_inode);
            for(size_t i=0;i<5&&used>0&&(size_t)used<sizeof(output);i++) {
                int wrote=snprintf(output+used,sizeof(output)-(size_t)used,"%llu\n%llu\n",
                    (unsigned long long)n->ns_device[i],(unsigned long long)n->ns_inode[i]);
                if(wrote<=0||(size_t)wrote>=sizeof(output)-(size_t)used){used=-1;break;}used+=wrote;
            }
            if(used>0&&(size_t)used<sizeof(output)) {
                int wrote=snprintf(output+used,sizeof(output)-(size_t)used,"%lld\n%d\n",
                    (long long)now.tv_sec*1000+now.tv_nsec/1000000,populated);
                if(wrote<=0||(size_t)wrote>=sizeof(output)-(size_t)used)output[0]=0;
            }else output[0]=0;
        }
    }
    ws_lock_release_v1();if(ws_origin_guard_v1())return ws_origin_empty_v1();
#else
    (void)token;(void)binding;
#endif
    return rt_string_new((const uint8_t*)output,strlen(output));
}
int64_t rt_linux_container_containment_close_v1(int64_t token,int64_t binding) {
    int error=ws_origin_guard_v1();if(error)return -error;
#if defined(__linux__)
    char digest[65];if(!ws_copy_text_v1(binding,digest,sizeof(digest))||!ws_digest_v1(digest))return -EINVAL;
    error=ws_lock_acquire_v1();if(error)return -error;
    WsSlotV1* slot=ws_find_v1(token);
    if(!slot||slot->role!=3||strcmp(slot->policy,digest))error=WS_STALE_ERROR_V1;
    else if(slot->busy)error=EBUSY;
    else if(!(error=ws_contain_close_v1(&slot->containment)))memset(slot,0,sizeof(*slot));
    ws_lock_release_v1();return -error;
#else
    (void)token;(void)binding;return -ENOTSUP;
#endif
}

/* Descriptive running-kernel/context facts. No terminal or eligibility bit. */
int64_t rt_linux_container_containment_kernel_observe_v1(int64_t token,int64_t binding,
        int64_t release,int64_t build,int64_t profile) {
    if(ws_origin_guard_v1())return ws_origin_empty_v1();
    char output[2048]={0};
#if defined(__linux__)
    char expected_binding[65],expected_release[257],expected_build[129],expected_profile[65];
    if(!ws_copy_text_v1(binding,expected_binding,sizeof(expected_binding))||!ws_digest_v1(expected_binding)||
       !ws_copy_text_v1(release,expected_release,sizeof(expected_release))||!ws_kernel_release_v1(expected_release)||
       !ws_copy_text_v1(build,expected_build,sizeof(expected_build))||!ws_kernel_hex_v1(expected_build)||
       !ws_copy_text_v1(profile,expected_profile,sizeof(expected_profile))||!ws_digest_v1(expected_profile))
        return rt_string_new((const uint8_t*)"",0);
    if(ws_lock_acquire_v1())return rt_string_new((const uint8_t*)"",0);
    WsSlotV1* slot=ws_find_v1(token);WsKernelFactsV1 f;
    if(slot&&slot->role==3&&!slot->busy&&!strcmp(slot->policy,expected_binding)&&
       !ws_kernel_observe_v1(&slot->containment,expected_release,expected_build,&f)) {
        WsContainNativeV1* n=&slot->containment;struct timespec now;
        if(!clock_gettime(CLOCK_REALTIME,&now)&&now.tv_sec>0&&now.tv_sec<(INT64_MAX-999)/1000) {
            int used=snprintf(output,sizeof(output),"linux-container-kernel-native-v1\n%lld\n%s\n%s\n%s\n%s\n%s\n%ld\n%ld\n%d\n%d\n%d\n%d\n%d\n%d\n%llu\n%llu\n%llu\n%llu\n%llu\n%llu\n%llu\n%llu\n%llu\n%llu\n%llu\n%llu\n%lld\n",
                (long long)token,expected_binding,expected_profile,f.release,f.build_id,f.notes_digest,(long)f.pid,(long)f.tid,
                f.seccomp,f.status_seccomp,f.tracer,f.dumpable,f.nnp,f.status_nnp,
                (unsigned long long)f.proc_device,(unsigned long long)f.proc_inode,(unsigned long long)f.sysfs_device,
                (unsigned long long)f.sysfs_inode,(unsigned long long)f.notes_device,(unsigned long long)f.notes_inode,
                (unsigned long long)n->ns_device[2],(unsigned long long)n->ns_inode[2],
                (unsigned long long)n->ns_device[3],(unsigned long long)n->ns_inode[3],
                (unsigned long long)n->ns_device[4],(unsigned long long)n->ns_inode[4],
                (long long)now.tv_sec*1000+now.tv_nsec/1000000);
            if(used<=0||(size_t)used>=sizeof(output))output[0]=0;
        }
    }
    ws_lock_release_v1();if(ws_origin_guard_v1())return ws_origin_empty_v1();
#else
    (void)token;(void)binding;(void)release;(void)build;(void)profile;
#endif
    return rt_string_new((const uint8_t*)output,strlen(output));
}
