/* Source-only until allocated. Include canonical owner once; link normal CoreC
 * arrays, sealed executable pin and memory owners, never fake support symbols. */
#define _GNU_SOURCE
#define RT_PROCESS_OBSERVATION_V4_TESTING 1
#include <assert.h>
#include <pthread.h>
#include <stdio.h>
#include "../runtime_process_owned.c"

/* Link --wrap=rt_array_new,--wrap=read,--wrap=setpgid. Faults are test-local
 * syscall/result failure only; actual production child/trace/reap facts remain. */
extern SplArray* __real_rt_array_new(int64_t);
extern ssize_t __real_read(int,void*,size_t);
extern int __real_setpgid(pid_t,pid_t);
static int fail_array_once,partial_fd=-1,read_eagain_once,fail_parent_setpgid;
static pid_t harness_pid;
SplArray* __wrap_rt_array_new(int64_t n){if(fail_array_once){fail_array_once=0;return NULL;}return __real_rt_array_new(n);}
ssize_t __wrap_read(int fd,void* p,size_t n){
    if(fd==partial_fd){if(read_eagain_once){read_eagain_once=0;errno=EAGAIN;return -1;}if(n>1)n=1;}
    return __real_read(fd,p,n);
}
int __wrap_setpgid(pid_t p,pid_t g){
    if(fail_parent_setpgid&&getpid()==harness_pid&&p>0){fail_parent_setpgid=0;errno=EIO;return -1;}
    return __real_setpgid(p,g);
}

static void byte(SplArray* a,unsigned v){assert(rt_array_push(a,rt_value_int(v)));}
static void number(SplArray* a,uint64_t v){for(int i=0;i<8;i++)byte(a,(v>>(8*i))&255);}
static void bytes(SplArray* a,const uint8_t* p,size_t n){for(size_t i=0;i<n;i++)byte(a,p[i]);}
static void text(SplArray* a,const char* p){number(a,strlen(p));bytes(a,(const uint8_t*)p,strlen(p));}
static void digest(SplArray* a,SplArray* d){assert(d&&rt_array_len(d)==32);for(int i=0;i<32;i++)byte(a,(unsigned)rt_value_as_int(rt_array_get(d,i)));}
static SplArray* binding(const char* program,int64_t image,int64_t cwd,const char* mode,int64_t wall){
    SplArray* a=rt_array_new(1024);assert(a);
    bytes(a,(const uint8_t*)"POV4REQ\0",8);number(a,1);number(a,1);
    number(a,wall);number(a,10000000);number(a,1000000000);
    number(a,1024);number(a,1024);number(a,0);number(a,1);number(a,1);number(a,1000000);
    number(a,image);SplArray* d=rt_process_pinned_executable_sha256_value(image);digest(a,d);rt_array_free(d);
    text(a,"/");text(a,"/");number(a,cwd);
    d=rt_process_observation_v4_cwd_digest_value(cwd);digest(a,d);rt_array_free(d);
    number(a,2);text(a,program);text(a,mode);number(a,0);return a;
}
static Pov4Reservation* reservation(int64_t token){
    for(int i=0;i<POV4_SLOTS;i++)if(pov4_reservations[i].token==token)return &pov4_reservations[i];
    assert(0);return NULL;
}
static RtOwnedSlot* child(int64_t token){
    Pov4Slot* o=pov4_reservation_owner(reservation(token));assert(o);
    RtOwnedSlot* c=owned_token_acquire(o->core,NULL);assert(c);owned_token_release(c);return c;
}
static int64_t unix_ms(void){struct timespec n;assert(clock_gettime(CLOCK_REALTIME,&n)==0);return (int64_t)n.tv_sec*1000+n.tv_nsec/1000000;}
static void tick(void){struct timespec ts={0,1000000};nanosleep(&ts,NULL);}
static int advance(int64_t token,int retire){
    int64_t deadline=owned_now_ns()+5000000000LL;int result;
    do{result=(int)rt_process_observation_v6_reserved_poll_launch_value(token,retire);assert(result>=0);if(result!=1)return result;tick();}while(owned_now_ns()<deadline);
    assert(!"test deadline: pending owner retained");return -1;
}
static void settle(int64_t token,int retire){
    Pov4Slot* o=pov4_reservation_owner(reservation(token));assert(o);
    int64_t until=owned_now_ns()+5000000000LL;
    while(!o->frozen&&owned_now_ns()<until){
        SplArray* observation=rt_process_observation_v4_reserved_observe_value(token,0,retire);
        assert(observation);pov4_tuple4_free(observation);tick();
    }
    assert(o->frozen);
    if(!retire){
        assert(o->words[POV4_EXIT_CODE]==0);
        assert(o->stdout_count==8&&memcmp(o->stdout_bytes,"exec-v6\n",8)==0);
    }
    SplArray* d=rt_array_new(32);assert(d);bytes(d,o->frozen_digest,32);
    SplArray* ack=rt_process_observation_v4_reserved_ack_value(token,d);assert(ack);
    pov4_tuple4_free(ack);rt_array_free(d);
    assert(rt_process_observation_v4_reserved_confirm_release_value(token)==1);
}
struct WrongThread{int64_t token;};
static void* wrong_thread(void* p){
    int64_t t=((struct WrongThread*)p)->token;
    assert(rt_process_observation_v6_reserved_poll_launch_value(t,0)==-EPERM);
    assert(rt_process_observation_v4_reserved_observe_value(t,0,0)==NULL&&errno==EPERM);
    assert(rt_process_observation_v4_reserved_confirm_release_value(t)==-EPERM);
    return NULL;
}
static int64_t start(const char* program,int64_t image,int64_t cwd,const char* mode,int64_t wall,int64_t expiry){
    int64_t t=rt_process_observation_v4_reserve_value();assert(t>0);
    assert(rt_process_observation_v6_reserved_poll_launch_value(t,0)==-EINVAL);
    SplArray* a=binding(program,image,cwd,mode,wall);
    assert(rt_process_observation_v6_reserved_start_deferred_admitted_value(t,image,cwd,a,expiry)==1);
    assert(reservation(t)->state==6&&child(t)->launch_exec_fd>=0);
    assert(rt_process_observation_v6_reserved_start_deferred_admitted_value(t,image,cwd,a,expiry)==-EALREADY);
    assert(rt_process_observation_v4_reserved_observe_value(t,0,0)==NULL&&errno==EBUSY);
    assert(rt_process_observation_v4_reserved_ack_value(t,NULL)==NULL&&errno==EBUSY);
    assert(rt_process_observation_v4_reserved_confirm_release_value(t)==-EBUSY);
    rt_array_free(a);return t;
}
int main(int argc,char** argv){
    alarm(15);harness_pid=getpid();assert(argc==2); /* argv[1] must be the separately built real static helper. */
    int64_t image=rt_process_pin_executable_owned_value((const uint8_t*)argv[1],strlen(argv[1]));assert(image>0);
    int64_t cwd=rt_process_observation_v4_pin_cwd_value("/",1);assert(cwd>0);
    int64_t expiry=unix_ms()+10000;
    int64_t t=start(argv[1],image,cwd,"exit",2000000000LL,expiry);
    RtOwnedSlot* c=child(t);pthread_mutex_lock(c->state_lock);
    pthread_t thread;struct WrongThread wrong={t};assert(pthread_create(&thread,NULL,wrong_thread,&wrong)==0);
    assert(pthread_join(thread,NULL)==0);pthread_mutex_unlock(c->state_lock);
    /* Parent has not continued the actual ptrace stop: no exec proof exists. */
    assert(c->exec_confirmed_ns<0);assert(advance(t,0)==2);
    assert(c->exec_confirmed_ns>0&&c->launch_exec_fd==-1);
    /* Once materialized, retire here is observational only, not cancellation. */
    assert(rt_process_observation_v6_reserved_poll_launch_value(t,1)==2);
    assert(!c->cancel_requested);
    fail_array_once=1;
    assert(rt_process_observation_v4_reserved_observe_value(t,0,0)==NULL);
    assert(reservation(t)->state==4&&pov4_reservation_owner(reservation(t))!=NULL);
    settle(t,0);
    t=start(argv[1],image,cwd,"hold",2000000000LL,expiry);
    assert(advance(t,1)==2);assert(child(t)->reaped&&child(t)->exec_confirmed_ns<0);settle(t,1);
    t=start(argv[1],image,cwd,"hold",1000000000LL,expiry);
    struct timespec stopped_timeout={1,100000000};nanosleep(&stopped_timeout,NULL);
    assert(advance(t,0)==2);assert(child(t)->timed_out&&child(t)->reaped);settle(t,1);
    /* Let a genuinely admitted grant expire while stopped, before real exec. */
    t=start(argv[1],image,cwd,"exit",3000000000LL,unix_ms()+1000);
    struct timespec admission_delay={1,100000000};nanosleep(&admission_delay,NULL);
    /* Read the actual child's errno through forced partial/EAGAIN provider outcomes. */
    c=child(t);partial_fd=c->launch_exec_fd;read_eagain_once=1;
    assert(advance(t,0)==2);assert(c->reaped&&c->exec_confirmed_ns<0);
    assert(c->launch_error_count==(int)sizeof(int)&&!read_eagain_once);
    partial_fd=-1;assert(c->launch_failure==ETIMEDOUT);settle(t,1);
    int64_t expired=unix_ms();
    t=rt_process_observation_v4_reserve_value();assert(t>0);
    SplArray* a=binding(argv[1],image,cwd,"exit",2000000000LL);
    assert(rt_process_observation_v6_reserved_start_deferred_admitted_value(t,image,cwd,a,expired-1)==-ETIMEDOUT);
    assert(rt_process_observation_v6_reserved_poll_launch_value(t,0)==0);
    assert(rt_process_observation_v4_reserved_confirm_release_value(t)==1);rt_array_free(a);
    /* A real postfork setup failure must never fall into synchronous cleanup.
     * Missing pidfd deliberately leaves production authority uncertain. */
    fail_parent_setpgid=1;
    t=start(argv[1],image,cwd,"hold",2000000000LL,unix_ms()+10000);
    c=child(t);int error_fd=c->launch_exec_fd;pid_t exact_test_child=c->pid;
    assert(c->launch_failure==EIO&&c->pidfd<0);
    assert(rt_process_observation_v6_reserved_poll_launch_value(t,1)<0);
    assert(reservation(t)->state==6&&c->launch_exec_fd==error_fd);
    assert(fcntl(error_fd,F_GETFD)>=0);
    /* TEST HARNESS owns this actual fork result: cleanup is not a production
     * fallback, receipt, release or successful V6 lifecycle assertion. */
    assert(kill(exact_test_child,SIGKILL)==0);
    int status;assert(waitpid(exact_test_child,&status,0)==exact_test_child);
    assert(WIFSIGNALED(status)&&WTERMSIG(status)==SIGKILL);
    errno=0;assert(waitpid(exact_test_child,&status,WNOHANG)==-1&&errno==ECHILD);
    assert(reservation(t)->state==6);
    /* Original pins belong to retained state6 through fixture exit, even after
     * the test harness has reaped its actual child. Never release them early. */
    SplArray* still_pinned=rt_process_pinned_executable_sha256_value(image);
    assert(still_pinned&&rt_array_len(still_pinned)==32);rt_array_free(still_pinned);
    still_pinned=rt_process_observation_v4_cwd_digest_value(cwd);
    assert(still_pinned&&rt_array_len(still_pinned)==32);rt_array_free(still_pinned);
    puts("deferred V6 actual exec/cancel/timeout/TID/legacy-refusal source fixture completed");return 0;
}
