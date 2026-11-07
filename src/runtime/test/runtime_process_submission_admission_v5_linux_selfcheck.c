/* Linux final-fork and pre-exec controls; authored, NOT_RUN without approval.
 * Native process creation, sealed memfd image, ptrace exec proof, observe,
 * reap and acknowledgement are real. The small value-runtime fixture is not
 * the Simple ABI; its executable-pin bridge duplicates the actual sealed fd.
 * Only test-TU realtime/fork wrappers are substituted; no production fault API.
 * Future admitted build: cc -std=c11 -O0 -Wall -Wextra -pthread this.c
 * src/runtime/runtime_process_tree.c -o probe; run under an external tree watchdog.
 */
#if !defined(__linux__)
int main(void) {return 77;}
#else
#define _GNU_SOURCE
#include "../runtime.h"
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <linux/memfd.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>
static int admission_mode,admission_calls,actual_forks;
static int64_t test_expiry;
static int test_unix_clock(clockid_t id,struct timespec* now) {
    if (clock_gettime(id,now)!=0) return -1;
    assert(id==CLOCK_REALTIME);admission_calls++;
    if (admission_mode==2 && admission_calls>=2) {errno=EIO;return -1;}
    if ((admission_mode==1 && admission_calls>=2) ||
        (admission_mode==3 && admission_calls>=3)) {
        now->tv_sec=test_expiry/1000;now->tv_nsec=(test_expiry%1000)*1000000;
    }
    return 0;
}
static pid_t test_real_fork(void) {
    pid_t pid=fork();if (pid>0) actual_forks++;return pid;
}
SplArray* rt_array_new(int64_t capacity) {
    SplArray* a = calloc(1, sizeof(*a)); assert(a);
    a->cap = capacity > 0 ? capacity : 1;
    a->items = calloc((size_t)a->cap, sizeof(*a->items)); assert(a->items);
    return a;
}
int64_t rt_array_len(SplArray* a) { return a ? a->len : -1; }
int64_t rt_array_get(SplArray* a, int64_t i) {
    return a && i >= 0 && i < a->len ? a->items[i].as_int : 0;
}
int8_t rt_array_push(SplArray* a, int64_t value) {
    if (!a || a->len >= a->cap) return 0;
    a->items[a->len++].as_int = value; return 1;
}
int8_t rt_array_set(SplArray* a, int64_t i, int64_t value) {
    if (!a || i < 0 || i >= a->len) return 0;
    a->items[i].as_int = value; return 1;
}
int64_t rt_value_int(int64_t value) { return value; }
int64_t rt_value_as_int(int64_t value) { return value; }
int8_t rt_value_is_int(int64_t value) { (void)value; return 1; }
void* rt_alloc(int64_t size) { return size > 0 ? calloc(1, (size_t)size) : NULL; }
void rt_free(void* value) { free(value); }
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t* rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_new(const uint8_t* bytes, uint64_t length) { (void)bytes; (void)length; return 1; }
void rt_array_free(SplArray* a) { if (a) { free(a->items); free(a); } }
int64_t rt_tuple_new(int64_t len) {
    SplArray* a = rt_array_new(len);
    for (int64_t i = 0; i < len; i++) assert(rt_array_push(a, 0));
    return (int64_t)(uintptr_t)a;
}
int8_t rt_tuple_set(int64_t tuple, int64_t index, int64_t value) {
    return rt_array_set((SplArray*)(uintptr_t)tuple, index, value);
}
int64_t rt_free_deep(int64_t value) { (void)value; return 1; }
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* a = (SplArray*)(uintptr_t)value;
    if (!a) return -1;
    for (int64_t i = 0; i < a->len; i++)
        if (rt_array_get(a, i) < 0 || rt_array_get(a, i) > 255) return -1;
    return a->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t cap) {
    int64_t n = rt_array_bytes_validate(value); if (n < 0 || n > cap) return -1;
    SplArray* a = (SplArray*)(uintptr_t)value;
    for (int64_t i = 0; i < n; i++) out[i] = (uint8_t)rt_array_get(a, i);
    return n;
}


#define TEST_PIN 77
static int executable_fd=-1;
static uint8_t executable_digest[32];
int64_t rt_process_acquire_pinned_executable(int64_t token) {
    if (token!=TEST_PIN || executable_fd<0) {errno=ESTALE;return -1;}
    return fcntl(executable_fd,F_DUPFD_CLOEXEC,3);
}
int rt_process_close_pinned_executable_owned_value(int64_t token) {(void)token;return 0;}
SplArray* rt_process_pinned_executable_sha256_value(int64_t token) {
    if (token!=TEST_PIN) return NULL;
    SplArray* result=rt_array_new(32);
    for (int i=0;i<32;i++) assert(rt_array_push(result,executable_digest[i]));
    return result;
}
#define POV5_ADMISSION_CLOCK_GETTIME test_unix_clock
#define fork test_real_fork
#include "../runtime_process_owned.c"
#undef fork

static void sealed_self(void) {
    int source=open("/proc/self/exe",O_RDONLY|O_CLOEXEC);struct stat info;
    assert(source>=0 && fstat(source,&info)==0 && info.st_size>0 && info.st_size<=16777216);
    uint8_t* bytes=malloc((size_t)info.st_size);assert(bytes);
    size_t offset=0;
    while (offset<(size_t)info.st_size) {
        ssize_t n=pread(source,bytes+offset,(size_t)info.st_size-offset,(off_t)offset);
        assert(n>0);offset+=(size_t)n;
    }
    assert(close(source)==0);owned_sha256(bytes,(size_t)info.st_size,executable_digest);
    executable_fd=(int)syscall(SYS_memfd_create,"submission-admission-test",MFD_CLOEXEC|MFD_ALLOW_SEALING);
    assert(executable_fd>=0);offset=0;
    while (offset<(size_t)info.st_size) {
        ssize_t n=write(executable_fd,bytes+offset,(size_t)info.st_size-offset);assert(n>0);offset+=(size_t)n;
    }
    free(bytes);assert(fchmod(executable_fd,0500)==0);
    int seals=F_SEAL_SEAL|F_SEAL_SHRINK|F_SEAL_GROW|F_SEAL_WRITE;
    assert(fcntl(executable_fd,F_ADD_SEALS,seals)==0);
    assert((fcntl(executable_fd,F_GET_SEALS)&seals)==seals);
}
static void put_u64(SplArray* array,uint64_t value) {
    for (int i=0;i<8;i++) assert(rt_array_push(array,(value>>(i*8))&255));
}
static void put_bytes(SplArray* array,const uint8_t* bytes,size_t length) {
    for (size_t i=0;i<length;i++) assert(rt_array_push(array,bytes[i]));
}
static void put_text(SplArray* array,const char* text) {
    size_t length=strlen(text);put_u64(array,length);put_bytes(array,(const uint8_t*)text,length);
}
static SplArray* request_bytes(const char* cwd,int64_t pin,const uint8_t digest[32]) {
    SplArray* result=rt_array_new(4096);const uint8_t magic[8]={'P','O','V','4','R','E','Q',0};
    put_bytes(result,magic,8);put_u64(result,1);put_u64(result,POV4_CAPABILITIES);
    put_u64(result,5000000000ULL);put_u64(result,100000000ULL);put_u64(result,2000000000ULL);
    put_u64(result,4096);put_u64(result,4096);put_u64(result,0);
    put_u64(result,POV4_ENFORCEMENT_NONE);put_u64(result,POV4_DESCENDANT_LEADER);put_u64(result,10000000);
    put_u64(result,TEST_PIN);put_bytes(result,executable_digest,32);put_text(result,cwd);put_text(result,cwd);
    put_u64(result,(uint64_t)pin);put_bytes(result,digest,32);
    put_u64(result,2);put_text(result,"submission-admission");put_text(result,"--submission-child");
    put_u64(result,1);put_text(result,"SUBMISSION_TEST");put_text(result,"exact");return result;
}
static SplArray* item(SplArray* tuple,int index) {return (SplArray*)(uintptr_t)rt_array_get(tuple,index);}
static int64_t field(SplArray* tuple,int index) {return rt_array_get(item(tuple,3),index);}
static void control(const char* cwd,int64_t pin,const uint8_t digest[32],int mode) {
    struct timespec now;assert(clock_gettime(CLOCK_REALTIME,&now)==0);
    test_expiry=(int64_t)now.tv_sec*1000+now.tv_nsec/1000000+10000;
    admission_mode=mode;admission_calls=0;actual_forks=0;
    int64_t token=rt_process_observation_v4_reserve_value();assert(token>0);
    SplArray* request=request_bytes(cwd,pin,digest);
    int64_t started=rt_process_observation_v5_reserved_start_admitted_value(token,TEST_PIN,pin,request,test_expiry);
    if (mode==1 || mode==2) {
        assert(started==-(mode==1?ETIMEDOUT:EIO) && actual_forks==0);
        assert(rt_process_observation_v4_reserved_state_value(token)==3);
        assert(rt_process_observation_v5_reserved_start_admitted_value(token,TEST_PIN,pin,request,INT64_MAX)==-EALREADY);
    } else {
        assert(started==1 && actual_forks==1);
        assert(rt_process_observation_v4_reserved_state_value(token)==4);
        assert(rt_process_observation_v4_reserved_confirm_release_value(token)==-EBUSY);
        SplArray* frozen=NULL;
        for (int turn=0;turn<400;turn++) {
            SplArray* observed=rt_process_observation_v4_reserved_observe_value(token,10000000,mode==3);
            if (!observed) continue;
            int64_t kind=field(observed,POV4_PACKET_KIND);
            if (kind==POV4_KIND_FROZEN || kind==POV4_KIND_CLEANUP_FROZEN) {frozen=observed;break;}
            pov4_tuple4_free(observed);
        }
        assert(frozen && field(frozen,POV4_PID)>0 && field(frozen,POV4_LEADER_REAPED)==1);
        int status=0;errno=0;
        assert(waitpid((pid_t)field(frozen,POV4_PID),&status,WNOHANG)==-1 && errno==ECHILD);
        if (mode==3) {
            assert(field(frozen,POV4_EXEC_STATE)!=POV4_EXEC_CONFIRMED);
            assert(field(frozen,POV4_ERRNO)==ETIMEDOUT && field(frozen,POV4_EXEC_ERRNO)==ETIMEDOUT);
            assert(field(frozen,POV4_TREE_CONTROL_AVAILABLE)==0 && field(frozen,POV4_TREE_EMPTY)==0);
            assert(rt_array_len(item(frozen,0))==0);
        } else {
            const char expected[]="admitted\n";
            assert(field(frozen,POV4_EXEC_STATE)==POV4_EXEC_CONFIRMED);
            assert(rt_array_len(item(frozen,0))==(int64_t)sizeof(expected)-1);
            for (size_t i=0;i<sizeof(expected)-1;i++) assert(rt_array_get(item(frozen,0),(int64_t)i)==expected[i]);
        }
        SplArray* ack=rt_process_observation_v4_reserved_ack_value(token,item(frozen,2));assert(ack);
        pov4_tuple4_free(ack);pov4_tuple4_free(frozen);
    }
    assert(rt_process_observation_v4_reserved_confirm_release_value(token)==1);
    rt_array_free(request);admission_mode=0;
}
int main(int argc,char** argv) {
    if (argc==2 && !strcmp(argv[1],"--submission-child")) {
        const char marker[]="admitted\n";return write(STDOUT_FILENO,marker,sizeof(marker)-1)==(ssize_t)sizeof(marker)-1?0:90;
    }
    sealed_self();char cwd[PATH_MAX];assert(realpath(".",cwd));
    int64_t pin=rt_process_observation_v4_pin_cwd_value(cwd,strlen(cwd));assert(pin>0);
    SplArray* value=rt_process_observation_v4_cwd_digest_value(pin);uint8_t digest[32];
    assert(rt_array_bytes_copy_checked((int64_t)(uintptr_t)value,digest,32)==32);
    control(cwd,pin,digest,1);control(cwd,pin,digest,2);control(cwd,pin,digest,3);control(cwd,pin,digest,0);
    assert(rt_process_observation_v4_close_cwd_value(pin)==1);rt_array_free(value);
    assert(close(executable_fd)==0);return 0;
}
#endif
