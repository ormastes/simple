/* AUTHORED_UNRUN: actual shared-owner origin fence, no XFS success injection.
 * Compile this TU against real Core-C with
 * -Wl,--wrap=rt_string_new -Wl,--wrap=stat. The owner
 * source is included verbatim with exported symbol aliases solely to expose its
 * real private mutex to this fixture without duplicate public definitions from
 * the linked runtime. No helper body, registry entry or native result is mocked.
 * No assertion here qualifies Simple lowering, XFS admission or Windows APIs. Namespace clone/transition qualification remains BLOCKED. */
#define _GNU_SOURCE
#include "runtime.h"
#include "runtime_workspace_storage_v1.h"
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(__linux__)
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
#include <poll.h>

#define rt_workspace_storage_open_v1 fork_fixture_storage_open_v1
#define rt_workspace_storage_recover_v1 fork_fixture_storage_recover_v1
#define rt_workspace_storage_observe_v1 fork_fixture_storage_observe_v1
#define rt_workspace_storage_release_if_absent_v1 fork_fixture_storage_release_v1
#define rt_workspace_storage_forget_released_v1 fork_fixture_storage_forget_v1
#define rt_linux_container_user_open_v1 fork_fixture_user_open_v1
#define rt_linux_container_user_observe_v1 fork_fixture_user_observe_v1
#define rt_linux_container_user_close_v1 fork_fixture_user_close_v1
#define rt_workspace_storage_prepare_executable_v1 fork_fixture_prepare_v1
#define rt_linux_container_containment_capture_v1 fork_fixture_containment_capture_v1
#define rt_linux_container_containment_observe_v1 fork_fixture_containment_observe_v1
#define rt_linux_container_containment_close_v1 fork_fixture_containment_close_v1
#include "../runtime_workspace_storage_v1.c"

static volatile sig_atomic_t fork_fixture_in_child;
static volatile sig_atomic_t fork_fixture_no_text_allocation;
static int fork_fixture_fail_stat_once, fork_fixture_stat_faults;
int __real_stat(const char* path,struct stat* value);
int __wrap_stat(const char* path,struct stat* value) {
    if(fork_fixture_fail_stat_once&&!strcmp(path,"/proc/self/ns/pid")) {
        fork_fixture_fail_stat_once=0;fork_fixture_stat_faults++;errno=EIO;return -1;
    }
    return __real_stat(path,value);
}
int64_t __real_rt_string_new(const uint8_t* bytes,uint64_t length);
int64_t __wrap_rt_string_new(const uint8_t* bytes,uint64_t length) {
    /* The mismatch path must not even ENTER the inherited short-string cache.
     * Parent arguments still use the actual allocator through the linker. */
    if(fork_fixture_in_child||fork_fixture_no_text_allocation)_exit(96);
    return __real_rt_string_new(bytes,length);
}
static unsigned checks;
#define CHECK(expression) do { checks++; if(!(expression)) { \
    fprintf(stderr,"FAIL:%d:%s\n",__LINE__,#expression); abort(); } } while(0)
#define CHILD_CHECK(expression) do { checks++; if(!(expression))_exit(97); } while(0)

typedef struct { int ready_read,ready_write,release_read,release_write,error; } LoanGate;
static void* hold_loan_gate(void* pointer) {
    LoanGate* gate=(LoanGate*)pointer;gate->error=ws_lock_acquire_v1();
    if(gate->error){(void)write(gate->ready_write,"E",1);return NULL;}
    if(write(gate->ready_write,"R",1)!=1)gate->error=EIO;
    struct pollfd ready={.fd=gate->release_read,.events=POLLIN};
    if(poll(&ready,1,3000)!=1)gate->error=ETIMEDOUT;
    else {char byte;if(read(gate->release_read,&byte,1)!=1||byte!='X')gate->error=EIO;}
    ws_lock_release_v1();return NULL;
}
static void atomic_loan_mechanism(void) {
    /* MECHANISM ONLY: local scratch objects are never registered, admitted,
     * assigned native handles or given storage/user roles. No quota success. */
    WsSlotV1 first,second;memset(&first,0,sizeof(first));memset(&second,0,sizeof(second));
    atomic_init(&first.busy,1);atomic_init(&second.busy,1);first.token=11;second.token=12;
    CHECK(ws_release_busy_pair_v1(&first,11,&first,11)==EINVAL);
    second.token=13;CHECK(ws_release_busy_pair_v1(&first,11,&second,12)==ESTALE);
    CHECK(atomic_load_explicit(&first.busy,memory_order_acquire)==1);
    CHECK(atomic_load_explicit(&second.busy,memory_order_acquire)==1);second.token=12;
    atomic_store_explicit(&second.busy,0,memory_order_release);
    CHECK(ws_release_busy_pair_v1(&first,11,&second,12)==EBUSY);
    CHECK(atomic_load_explicit(&first.busy,memory_order_acquire)==1);
    atomic_store_explicit(&second.busy,1,memory_order_release);
    int ready[2],release[2];CHECK(pipe(ready)==0);CHECK(pipe(release)==0);
    LoanGate gate={ready[0],ready[1],release[0],release[1],0};pthread_t holder;
    CHECK(pthread_create(&holder,NULL,hold_loan_gate,&gate)==0);
    struct pollfd available={.fd=ready[0],.events=POLLIN};CHECK(poll(&available,1,3000)==1);
    char byte;CHECK(read(ready[0],&byte,1)==1&&byte=='R');
    CHECK(ws_lock_acquire_v1()==EBUSY);
    /* The actual pair-release helper must finish while another thread still
     * holds the real registry gate. A final reacquire would strand the loans. */
    CHECK(ws_release_busy_pair_v1(&first,11,&second,12)==0);
    CHECK(atomic_load_explicit(&first.busy,memory_order_acquire)==0);
    CHECK(atomic_load_explicit(&second.busy,memory_order_acquire)==0);
    CHECK(first.token==11&&second.token==12&&first.role==0&&second.role==0);
    CHECK(write(release[1],"X",1)==1);CHECK(pthread_join(holder,NULL)==0);CHECK(gate.error==0);
    CHECK(close(ready[0])==0);CHECK(close(ready[1])==0);
    CHECK(close(release[0])==0);CHECK(close(release[1])==0);
}
static void child_empty(int64_t value) {
    CHILD_CHECK(value==ws_origin_empty_v1());
    CHILD_CHECK(((uintptr_t)value&7)==2); /* Neither heap tag nor aligned probe. */
    CHILD_CHECK(rt_string_len(value)==0);
    const uint8_t* bytes=rt_string_data(value);
    CHILD_CHECK(bytes!=NULL&&bytes[0]==0);
    CHILD_CHECK(rt_string_free(value)==0);
    /* A nonheap newline literal avoids unrelated generic registry lookups.
     * Existing decoders refuse the empty result at their newline precheck. */
    _Alignas(8) static const char newline[4]={0,0,'\n',0};
    CHILD_CHECK(rt_string_ends_with(value,(int64_t)(uintptr_t)(newline+2))==0);
}
static void child_calls(int64_t text,int64_t digest,int64_t invalid_text) {
    CHILD_CHECK(atomic_load_explicit(&ws_origin_ready_v1,memory_order_acquire)==1);
    struct stat namespace_stat;CHILD_CHECK(stat("/proc/self/ns/pid",&namespace_stat)==0);
    CHILD_CHECK(ws_origin_namespace_equal_v1((uint64_t)namespace_stat.st_dev,(uint64_t)namespace_stat.st_ino));
    CHILD_CHECK(ws_origin_guard_v1()==ECHILD);
    CHILD_CHECK(ws_lock_acquire_v1()==ECHILD); /* Would block on inherited mutex. */
    ws_lock_release_v1(); /* Refusal must not unlock the inherited copy either. */
    CHILD_CHECK(pthread_mutex_trylock(&ws_lock_v1)==EBUSY);
    CHILD_CHECK(ws_find_v1(1)==NULL);
    CHILD_CHECK(rt_workspace_storage_open_v1(text,text,text,text,text,1,4096,digest)==-ECHILD);
    CHILD_CHECK(rt_workspace_storage_recover_v1(text,text,text,text,text,1,4096,digest)==-ECHILD);
    child_empty(rt_workspace_storage_observe_v1(1));
    CHILD_CHECK(rt_workspace_storage_release_if_absent_v1(1)==-ECHILD);
    CHILD_CHECK(rt_workspace_storage_forget_released_v1(1)==-ECHILD);
    CHILD_CHECK(rt_linux_container_user_open_v1(getpid(),text,digest)==-ECHILD);
    child_empty(rt_linux_container_user_observe_v1(1,digest));
    CHILD_CHECK(rt_linux_container_user_close_v1(1,digest)==-ECHILD);
    child_empty(rt_workspace_storage_prepare_executable_v1(1,2,digest,digest,
        INT64_MAX,text,text,text,digest));
    /* Rejection precedes even malformed argument parsing. */
    CHILD_CHECK(rt_workspace_storage_open_v1(invalid_text,invalid_text,invalid_text,
        invalid_text,invalid_text,-1,-1,invalid_text)==-ECHILD);
    CHILD_CHECK(rt_linux_container_user_close_v1(1,invalid_text)==-ECHILD);
    child_empty(rt_linux_container_user_observe_v1(1,invalid_text));
    child_empty(rt_workspace_storage_prepare_executable_v1(-1,-1,invalid_text,invalid_text,
        -1,invalid_text,invalid_text,invalid_text,invalid_text));
}
#endif

int main(void) {
#if defined(__linux__)
    /* Guard claims the still-virgin registry before any owner lock/effect. */
    CHECK(atomic_load_explicit(&ws_process_origin_v1,memory_order_acquire)==0);
    CHECK(atomic_load_explicit(&ws_origin_ready_v1,memory_order_acquire)==0);
    CHECK(atomic_load_explicit(&ws_origin_failure_v1,memory_order_acquire)==0);
    CHECK(ws_origin_guard_v1()==0);
    CHECK(atomic_load_explicit(&ws_origin_ready_v1,memory_order_acquire)==1);
    CHECK(atomic_load_explicit(&ws_process_origin_v1,memory_order_acquire)==(unsigned int)getpid());
    struct stat namespace_stat;CHECK(stat("/proc/self/ns/pid",&namespace_stat)==0);
    CHECK(ws_origin_namespace_equal_v1((uint64_t)namespace_stat.st_dev,(uint64_t)namespace_stat.st_ino));
    /* Pure rejection checks against the actual immutable native pin: these do
     * not mutate the owner or pretend a namespace transition was observed. */
    CHECK(!ws_origin_namespace_equal_v1((uint64_t)namespace_stat.st_dev^UINT64_C(1),(uint64_t)namespace_stat.st_ino));
    CHECK(!ws_origin_namespace_equal_v1((uint64_t)namespace_stat.st_dev,(uint64_t)namespace_stat.st_ino^UINT64_C(1)));
    int64_t text=rt_string_new((const uint8_t*)"fixture",7);
    const char* pin="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
    int64_t digest=rt_string_new((const uint8_t*)pin,64);
    int64_t invalid_text=rt_string_new((const uint8_t*)"bad",3);
    CHECK(rt_string_len(text)==7&&rt_string_len(digest)==64);
    CHECK(ws_next_token_v1==1);
    for(size_t i=0;i<WS_SLOT_COUNT_V1;i++)CHECK(ws_slots_v1[i].token==0);
    int sentinel[2];CHECK(pipe(sentinel)==0);
    struct stat sentinel_before;CHECK(fstat(sentinel[0],&sentinel_before)==0);
    int channel[2];CHECK(pipe(channel)==0);
    CHECK(ws_lock_acquire_v1()==0);
    CHECK(ws_lock_acquire_v1()==EBUSY); /* Same-process contention never queues. */
    /* This is the actual production mutex, deliberately held at fork. */
    pid_t child=fork();CHECK(child>=0);
    if(!child) {
        fork_fixture_in_child=1;
        close(channel[0]);checks=0;
        struct stat before,after;
        CHILD_CHECK(fstat(sentinel[0],&before)==0);
        child_calls(text,digest,invalid_text);
        CHILD_CHECK(fstat(sentinel[0],&after)==0);
        CHILD_CHECK(before.st_dev==after.st_dev&&before.st_ino==after.st_ino&&before.st_mode==after.st_mode);
        CHILD_CHECK(fcntl(sentinel[1],F_GETFD)>=0);
        unsigned completed=checks;
        if(write(channel[1],&completed,sizeof(completed))!=(ssize_t)sizeof(completed))_exit(98);
        close(channel[1]);_exit(0);
    }
    CHECK(close(channel[1])==0);
    struct pollfd ready={.fd=channel[0],.events=POLLIN};int observed;
    /* One absolute harness deadline; signals cannot renew the wait budget. */
    struct timespec start,now;CHECK(clock_gettime(CLOCK_MONOTONIC,&start)==0);
    int64_t deadline=(int64_t)start.tv_sec*1000+start.tv_nsec/1000000+3000;
    for(;;) {
        CHECK(clock_gettime(CLOCK_MONOTONIC,&now)==0);
        int64_t remaining=deadline-((int64_t)now.tv_sec*1000+now.tv_nsec/1000000);
        if(remaining<=0){observed=0;break;}
        observed=poll(&ready,1,(int)remaining);
        if(observed<0&&errno==EINTR)continue;
        break;
    }
    unsigned child_checks=0;ssize_t received=-1;
    if(observed>0&&(ready.revents&POLLIN))received=read(channel[0],&child_checks,sizeof(child_checks));
    CHECK(close(channel[0])==0);
    /* Child must not reset or unlock the inherited mutex; parent still owns it. */
    CHECK(pthread_mutex_trylock(&ws_lock_v1)==EBUSY);
    CHECK(atomic_load_explicit(&ws_process_origin_v1,memory_order_acquire)==(unsigned int)getpid());
    CHECK(ws_next_token_v1==1);
    for(size_t i=0;i<WS_SLOT_COUNT_V1;i++)CHECK(ws_slots_v1[i].token==0);
    ws_lock_release_v1();
    if(received!=(ssize_t)sizeof(child_checks)) {
        /* Harness controls only its exact fork child; production never signals
         * or waits. Bound the deliberate old-source deadlock reproducer. */
        (void)kill(child,SIGKILL);
    }
    int status=0;pid_t reaped;do {reaped=waitpid(child,&status,0);}while(reaped<0&&errno==EINTR);
    CHECK(reaped==child);CHECK(received==(ssize_t)sizeof(child_checks));
    CHECK(WIFEXITED(status)&&WEXITSTATUS(status)==0);CHECK(child_checks>0);
    CHECK(ws_lock_acquire_v1()==0);ws_lock_release_v1();
    CHECK(rt_workspace_storage_release_if_absent_v1(1)==-ESTALE);
    CHECK(rt_workspace_storage_forget_released_v1(1)==-ESTALE);
    CHECK(rt_string_len(rt_workspace_storage_observe_v1(1))==0);
    CHECK(rt_linux_container_user_close_v1(1,digest)==-ESTALE);
    CHECK(rt_string_len(rt_linux_container_user_observe_v1(1,digest))==0);
    CHECK(rt_workspace_storage_open_v1(invalid_text,invalid_text,invalid_text,
        invalid_text,invalid_text,-1,-1,invalid_text)==-EINVAL);
    CHECK(ws_next_token_v1==1);
    struct stat sentinel_after;CHECK(fstat(sentinel[0],&sentinel_after)==0);
    CHECK(sentinel_after.st_dev==sentinel_before.st_dev&&sentinel_after.st_ino==sentinel_before.st_ino);
    CHECK(close(sentinel[0])==0);CHECK(close(sentinel[1])==0);
    atomic_loan_mechanism();
    /* INJECTED SYSCALL FAULT, separate from the naturally observed ordinary
     * fork checks above: lose the established namespace observation exactly
     * while releasing the real mutex. No quota/native owner is fabricated. */
    CHECK(ws_lock_acquire_v1()==0);
    CHECK(atomic_load_explicit(&ws_origin_failure_v1,memory_order_acquire)==0);
    fork_fixture_fail_stat_once=1;fork_fixture_no_text_allocation=1;
    ws_lock_release_v1();
    CHECK(fork_fixture_fail_stat_once==0&&fork_fixture_stat_faults==1);
    CHECK(atomic_load_explicit(&ws_origin_failure_v1,memory_order_acquire)==EIO);
    CHECK(pthread_mutex_trylock(&ws_lock_v1)==EBUSY);
    /* The kernel syscall is restored and really succeeds, but quarantine must
     * remain authoritative and prevent all subsequent waits on the held lock. */
    struct stat restored;CHECK(stat("/proc/self/ns/pid",&restored)==0);
    CHECK(restored.st_dev==namespace_stat.st_dev&&restored.st_ino==namespace_stat.st_ino);
    CHECK(ws_origin_guard_v1()==EIO);CHECK(ws_lock_acquire_v1()==EIO);
    CHECK(rt_workspace_storage_open_v1(text,text,text,text,text,1,4096,digest)==-EIO);
    CHECK(rt_workspace_storage_recover_v1(text,text,text,text,text,1,4096,digest)==-EIO);
    CHECK(rt_workspace_storage_release_if_absent_v1(1)==-EIO);
    CHECK(rt_workspace_storage_forget_released_v1(1)==-EIO);
    CHECK(rt_linux_container_user_open_v1(getpid(),text,digest)==-EIO);
    CHECK(rt_linux_container_user_close_v1(1,digest)==-EIO);
    CHECK(rt_workspace_storage_observe_v1(1)==ws_origin_empty_v1());
    CHECK(rt_linux_container_user_observe_v1(1,digest)==ws_origin_empty_v1());
    CHECK(rt_workspace_storage_prepare_executable_v1(1,2,digest,digest,INT64_MAX,
        text,text,text,digest)==ws_origin_empty_v1());
    ws_lock_release_v1();CHECK(pthread_mutex_trylock(&ws_lock_v1)==EBUSY);
    CHECK(atomic_load_explicit(&ws_process_origin_v1,memory_order_acquire)==(unsigned int)getpid());
    CHECK(atomic_load_explicit(&ws_origin_failure_v1,memory_order_acquire)==EIO);
    CHECK(ws_next_token_v1==1);
    for(size_t i=0;i<WS_SLOT_COUNT_V1;i++)CHECK(ws_slots_v1[i].token==0);
    /* Intentionally do not reset/unlock/destroy the quarantined registry.
     * This disposable fixture process ends with its copied owner retained. */
    printf("PASS scoped workspace fork-origin fence: %u parent checks, %u child checks; held real mutex, all public entries refused without string allocation; separately injected stat EIO remains quarantined after syscall recovery\n",checks,child_checks);
    puts("NOT_QUALIFIED: no admitted XFS storage token, successful preparation, namespace-clone transition, Simple ABI execution or Windows handle qualification");
    return 0;
#else
    fputs("UNSUPPORTED: actual fork-origin fixture requires Linux; no PASS\n",stderr);
    return 77;
#endif
}
