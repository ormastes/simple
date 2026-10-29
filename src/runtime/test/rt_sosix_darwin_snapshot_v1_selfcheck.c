/* Native API test links the production runtime_process_owned.c object.
 * Local array/string stubs isolate the ABI; deployed-language qualification is
 * separate. The copied executable is this locally compiled Mach-O. */
#define _DARWIN_C_SOURCE
#include "../runtime.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef __APPLE__
#include <unistd.h>
#include <signal.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <time.h>
SplArray* rt_array_new(int64_t cap) {
    SplArray* a=calloc(1,sizeof(*a)); assert(a); a->cap=cap; a->items=calloc((size_t)cap+1,sizeof(*a->items)); assert(a->items); return a;
}
int64_t rt_array_len(SplArray* a) { return a ? a->len : -1; }
int64_t rt_array_get(SplArray* a,int64_t i) { return a && i>=0 && i<a->len ? a->items[i].as_int : 0; }
int8_t rt_array_push(SplArray* a,int64_t v) { if(!a || a->len>=a->cap)return 0; a->items[a->len++].as_int=v; return 1; }
int8_t rt_array_set(SplArray* a,int64_t i,int64_t v) { if(!a || i<0 || i>=a->len)return 0; a->items[i].as_int=v; return 1; }
void rt_array_free(SplArray* a) { if(a) { free(a->items);free(a); } }
int64_t rt_value_int(int64_t v) { return v; }
int64_t rt_value_as_int(int64_t v) { return v; }
int8_t rt_value_is_int(int64_t v) { (void)v;return 1; }
int64_t rt_string_len(int64_t v) { return v ? (int64_t)strlen((char*)(uintptr_t)v) : -1; }
const uint8_t* rt_string_data(int64_t v) { return (const uint8_t*)(uintptr_t)v; }
#include <errno.h>
#include <limits.h>
static SplArray* ints(const int64_t* w,int64_t n) {
    SplArray* a=rt_array_new(n); for(int64_t i=0;i<n;i++) assert(rt_array_push(a,w[i])); return a;
}
static SplArray* texts(const char** v,int n) {
    SplArray* a=rt_array_new(n); for(int i=0;i<n;i++) assert(rt_array_push(a,(int64_t)(uintptr_t)v[i])); return a;
}
static void pause_ms(long ms) { struct timespec t={ms/1000,(ms%1000)*1000000}; while(nanosleep(&t,&t) && errno==EINTR){} }
static int64_t launch(const char* executable,const char* mode,int64_t wall) {
    const char* values[]={executable,"/",mode,"argument with spaces"};
    const char* environment[]={"SNAPSHOT_TEST=explicit"};
    int64_t bounds[]={wall,10000000,2000000000,128,128};
    SplArray* in=texts(values,4),*env=texts(environment,1),*limits=ints(bounds,5);
    SplArray* result=rt_sosix_darwin_snapshot_v1_start_value(1,in,env,limits);
    assert(result && rt_array_get(result,1)==0); int64_t handle=rt_array_get(result,2); assert(handle>0);
    rt_array_free(result);rt_array_free(in);rt_array_free(env);rt_array_free(limits);return handle;
}
static SplArray* complete(int64_t handle) {
    for(int i=0;i<600;i++) {
        SplArray* r=rt_sosix_darwin_snapshot_v1_poll_value(handle,10000000); assert(r && rt_array_get(r,1)==0);
        if(rt_array_get(r,3)) { assert(rt_array_get(r,4)==1 && rt_array_get(r,5)==1);return r; }
        rt_array_free(r);
    }
    assert(!"bounded completion failed");return NULL;
}
int main(int argc,char** argv) {
    if(argc>1) {
        if(!strcmp(argv[1],"capture")) {
            assert(argc==3 && !strcmp(argv[2],"argument with spaces"));
            assert(getenv("SNAPSHOT_TEST") && !strcmp(getenv("SNAPSHOT_TEST"),"explicit"));
            assert(!getenv("PATH"));char cwd[32];assert(getcwd(cwd,sizeof(cwd)) && !strcmp(cwd,"/"));
            const unsigned char bytes[]={65,0,66};assert(write(1,bytes,3)==3);assert(write(2,"error",5)==5);return 23;
        }
        if(!strcmp(argv[1],"flood")) { char b[10000];memset(b,'x',sizeof(b));assert(write(1,b,sizeof(b))==sizeof(b));return 0; }
        signal(SIGTERM,SIG_IGN);for(;;) pause_ms(100);
    }
    char executable[PATH_MAX];assert(realpath(argv[0],executable));
    SplArray* caps=rt_sosix_darwin_snapshot_v1_capabilities_value();assert(caps && rt_array_len(caps)==10);
    assert(rt_array_get(caps,1)==1 && rt_array_get(caps,3)==0 && rt_array_get(caps,4)==0);
    assert(rt_array_get(caps,7)==1 && rt_array_get(caps,8)==1 && rt_array_get(caps,9)==0);rt_array_free(caps);
    puts("PASS snapshot API capabilities: cooperative path snapshot group only");
    SplArray* denied=rt_sosix_darwin_snapshot_v1_start_value(4,NULL,NULL,NULL);
    assert(denied && rt_array_get(denied,1)==ENOTSUP && rt_array_get(denied,2)==0);rt_array_free(denied);
    puts("PASS snapshot API admission: strict profile rejected before acquisition");
    int64_t handle=launch(executable,"capture",2000000000);
    assert(rt_sosix_darwin_snapshot_v1_ack_value(handle)==EBUSY);
    SplArray* early=rt_sosix_darwin_snapshot_v1_output_value(handle,1);assert(rt_array_get(early,1)==EBUSY);rt_array_free(early);
    SplArray* r=complete(handle);assert(rt_array_get(r,6)==23 && rt_array_get(r,11)==3 && rt_array_get(r,12)==5);rt_array_free(r);
    for(int replay=0;replay<2;replay++) {
        SplArray* out=rt_sosix_darwin_snapshot_v1_output_value(handle,1);assert(out && rt_array_len(out)==5 && rt_array_get(out,0)==1 && rt_array_get(out,1)==0);
        assert(rt_array_get(out,2)==65 && rt_array_get(out,3)==0 && rt_array_get(out,4)==66);rt_array_free(out);
    }
    assert(rt_sosix_darwin_snapshot_v1_ack_value(handle)==0);
    r=rt_sosix_darwin_snapshot_v1_poll_value(handle,0);assert(rt_array_get(r,1)==ESTALE);rt_array_free(r);
    assert(rt_sosix_darwin_snapshot_v1_ack_value(handle)==ESTALE);
    SplArray* stale=rt_sosix_darwin_snapshot_v1_output_value(handle,1);assert(rt_array_get(stale,1)==ESTALE);rt_array_free(stale);
    puts("PASS snapshot API lifecycle: argv env cwd binary capture replay ack stale handle");
    int64_t second=launch(executable,"flood",2000000000);assert(second!=handle);
    r=complete(second);assert(rt_array_get(r,11)==10000 && rt_array_get(r,13)==128);rt_array_free(r);
    assert(rt_sosix_darwin_snapshot_v1_ack_value(second)==0);
    puts("PASS snapshot API output: bounded retention and complete drain");
    handle=launch(executable,"timeout",150000000);r=complete(handle);
    assert(rt_array_get(r,7)==1 && rt_array_get(r,9)==1 && rt_array_get(r,10)==1);rt_array_free(r);
    assert(rt_sosix_darwin_snapshot_v1_ack_value(handle)==0);
    puts("PASS snapshot API timeout: TERM KILL reap group retirement");
    handle=launch(executable,"cancel",2000000000);pause_ms(50);
    r=rt_sosix_darwin_snapshot_v1_cancel_value(handle);assert(rt_array_get(r,1)==0);rt_array_free(r);
    r=complete(handle);assert(rt_array_get(r,8)==1 && rt_array_get(r,7)==0);rt_array_free(r);
    assert(rt_sosix_darwin_snapshot_v1_ack_value(handle)==0);
    puts("PASS snapshot API cancel: opaque owner retained until completion");
    handle=launch(executable,"fork-owner",2000000000);
    pid_t forked=fork();assert(forked>=0);
    if (!forked) {
        SplArray* inherited=rt_sosix_darwin_snapshot_v1_cancel_value(handle);assert(rt_array_get(inherited,1)==ESTALE);
        assert(rt_sosix_darwin_snapshot_v1_ack_value(handle)==ESTALE);
        inherited=rt_sosix_darwin_snapshot_v1_start_value(1,NULL,NULL,NULL);assert(rt_array_get(inherited,1)==ENOTSUP);
        inherited=rt_sosix_darwin_snapshot_v1_output_value(handle,1);assert(rt_array_get(inherited,1)==ESTALE);
        _exit(0);
    }
    int fork_status;assert(waitpid(forked,&fork_status,0)==forked && WIFEXITED(fork_status) && WEXITSTATUS(fork_status)==0);
    r=rt_sosix_darwin_snapshot_v1_poll_value(handle,0);assert(rt_array_get(r,1)==0 && rt_array_get(r,3)==0);rt_array_free(r);
    r=rt_sosix_darwin_snapshot_v1_cancel_value(handle);assert(rt_array_get(r,1)==0);rt_array_free(r);
    r=complete(handle);rt_array_free(r);assert(rt_sosix_darwin_snapshot_v1_ack_value(handle)==0);
    puts("PASS snapshot API fork: inherited authority rejected before registry lock");

    const char* invocation[]={executable,"/","capture","argument with spaces"};
    const char* duplicate[]={"A=1","A=2"};int64_t bounds[]={1000000000,0,1000000000,128,128};
    SplArray* in=texts(invocation,4),*env=texts(duplicate,2),*limits=ints(bounds,5);
    r=rt_sosix_darwin_snapshot_v1_start_value(1,in,env,limits);assert(rt_array_get(r,1)==EINVAL);rt_array_free(r);rt_array_free(env);
    env=rt_array_new(0);struct sigaction old,ignored;memset(&ignored,0,sizeof(ignored));ignored.sa_handler=SIG_IGN;sigemptyset(&ignored.sa_mask);
    assert(sigaction(SIGCHLD,&ignored,&old)==0);
    r=rt_sosix_darwin_snapshot_v1_start_value(1,in,env,limits);assert(rt_array_get(r,1)==ENOTSUP);rt_array_free(r);
    assert(sigaction(SIGCHLD,&old,NULL)==0);
    char fifo[]="/tmp/snapshot-api-fifo-XXXXXXXX";int fd=mkstemp(fifo);assert(fd>=0);close(fd);assert(unlink(fifo)==0 && mkfifo(fifo,0600)==0);
    assert(rt_array_set(in,0,(int64_t)(uintptr_t)fifo));
    r=rt_sosix_darwin_snapshot_v1_start_value(1,in,env,limits);assert(rt_array_get(r,1)!=0 && rt_array_get(r,2)==0);rt_array_free(r);unlink(fifo);
    rt_array_free(in);rt_array_free(env);rt_array_free(limits);
    puts("PASS snapshot API preflight: duplicate environment SIGCHLD FIFO rejected");
    return 0;
}
#else
int main(void) { puts("UNAVAILABLE snapshot API requires Darwin");return 77; }
#endif
