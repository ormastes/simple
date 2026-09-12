/* Linux live contract check for the exact pinned Process Observation V4 host.
 * This is host evidence only; Simple admission still requires the self-hosted
 * compiler/runtime lane. */
#if !defined(__linux__)
int main(void) { return 0; }
#else
#define _GNU_SOURCE
#define RT_PROCESS_OBSERVATION_V4_TESTING 1
#include "../runtime.h"

#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

SplArray* rt_array_new(int64_t capacity) {
    SplArray* a = (SplArray*)calloc(1, sizeof(*a)); assert(a);
    a->cap = capacity > 0 ? capacity : 1;
    a->items = (SplValue*)calloc((size_t)a->cap, sizeof(*a->items)); assert(a->items);
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
int8_t rt_array_set(SplArray* a, int64_t index, int64_t value) {
    if (!a || index < 0 || index >= a->len) return 0;
    a->items[index].as_int=value; return 1;
}
int64_t rt_value_int(int64_t value) { return value; }
int64_t rt_value_as_int(int64_t value) { return value; }
void* rt_alloc(int64_t size) { return size > 0 ? calloc(1, (size_t)size) : NULL; }
void rt_free(void* value) { free(value); }
int64_t rt_string_len(int64_t value) { (void)value; return -1; }
const uint8_t* rt_string_data(int64_t value) { (void)value; return NULL; }
int64_t rt_string_new(const uint8_t* bytes, uint64_t length) {
    (void)bytes; (void)length; return 1;
}
void rt_array_free(SplArray* a) { if (a) { free(a->items); free(a); } }
int64_t rt_free_deep(int64_t value) { (void)value; return 1; }
int64_t rt_array_bytes_validate(int64_t value) {
    SplArray* a = (SplArray*)(uintptr_t)value;
    if (!a) return -1;
    for (int64_t i=0;i<a->len;i++) if (rt_array_get(a,i)<0 || rt_array_get(a,i)>255) return -1;
    return a->len;
}
int64_t rt_array_bytes_copy_checked(int64_t value, uint8_t* out, int64_t cap) {
    int64_t n=rt_array_bytes_validate(value); if (n<0 || n>cap) return -1;
    SplArray* a=(SplArray*)(uintptr_t)value;
    for (int64_t i=0;i<n;i++) out[i]=(uint8_t)rt_array_get(a,i);
    return n;
}
static const char* test_exec_path = "/proc/self/exe";
int64_t rt_process_acquire_pinned_executable(int64_t handle) {
    if (handle != 77) { errno = ESTALE; return -1; }
    int fd=open(test_exec_path, O_RDONLY|O_CLOEXEC);
    return fd;
}
int rt_process_close_pinned_executable_owned_value(int64_t handle) { (void)handle; return 0; }

static uint8_t test_exec_digest[32];
SplArray* rt_process_pinned_executable_sha256_value(int64_t handle) {
    if (handle != 77) return rt_array_new(0);
    SplArray* a=rt_array_new(32);
    for (int i=0;i<32;i++) assert(rt_array_push(a, test_exec_digest[i]));
    return a;
}

#include "../runtime_process_owned.c"

static void put_u64(SplArray* a, uint64_t value) {
    for (int i=0;i<8;i++) assert(rt_array_push(a, (int64_t)((value>>(8*i))&255)));
}
static void set_u64_at(SplArray* a, int64_t offset, uint64_t value) {
    for (int i=0;i<8;i++)
        assert(rt_array_set(a,offset+i,(int64_t)((value>>(8*i))&255)));
}
static void put_bytes(SplArray* a, const uint8_t* bytes, size_t count) {
    for (size_t i=0;i<count;i++) assert(rt_array_push(a, bytes[i]));
}
static void put_text(SplArray* a, const char* text) {
    size_t n=strlen(text); put_u64(a,n); put_bytes(a,(const uint8_t*)text,n);
}
static SplArray* request_bytes(const char* cwd, int64_t cwd_pin, const uint8_t cwd_digest[32]) {
    SplArray* a=rt_array_new(1024);
    const uint8_t magic[8]={'P','O','V','4','R','E','Q',0}; put_bytes(a,magic,8);
    put_u64(a,1); put_u64(a,1); put_u64(a,2000000000ULL);
    put_u64(a,100000000ULL); put_u64(a,500000000ULL);
    put_u64(a,1024); put_u64(a,1024); put_u64(a,0);
    put_u64(a,1); put_u64(a,1); put_u64(a,1000000); put_u64(a,77);
    put_bytes(a,test_exec_digest,32); put_text(a,cwd); put_text(a,cwd);
    put_u64(a,(uint64_t)cwd_pin); put_bytes(a,cwd_digest,32);
    put_u64(a,2); put_text(a,"pov4-selfcheck"); put_text(a,"--pov4-child");
    put_u64(a,1); put_text(a,"POV4_TEST"); put_text(a,"exact");
    return a;
}
static SplArray* tuple_item(SplArray* tuple, int index) {
    return (SplArray*)(uintptr_t)rt_array_get(tuple,index);
}
static SplArray* ticket_from(const SplArray* words) {
    SplArray* t=rt_array_new(5);
    assert(rt_array_push(t,4));
    for (int i=4;i<=7;i++) assert(rt_array_push(t,rt_array_get((SplArray*)words,i)));
    return t;
}

int main(int argc, char** argv) {
    if (argc==2 && strcmp(argv[1],"--pov4-child")==0) {
        char cwd[4096]; const char* exact=getenv("POV4_TEST");
        if (!exact || strcmp(exact,"exact")!=0 || !getcwd(cwd,sizeof(cwd))) return 90;
        if (write(STDOUT_FILENO,cwd,strlen(cwd))!=(ssize_t)strlen(cwd)) return 91;
        if (write(STDERR_FILENO,"fair",4)!=4) return 92;
        return 0;
    }
    for (int i=0;i<32;i++) test_exec_digest[i]=(uint8_t)(i+1);
    char cwd[4096]; assert(realpath(".",cwd));
    int64_t cwd_pin=rt_process_observation_v4_pin_cwd_value(cwd,strlen(cwd));
    assert(cwd_pin>0);
    SplArray* cwd_digest_value=rt_process_observation_v4_cwd_digest_value(cwd_pin);
    uint8_t cwd_digest[32]; assert(rt_array_bytes_copy_checked(
        (int64_t)(uintptr_t)cwd_digest_value,cwd_digest,32)==32);
    SplArray* request=request_bytes(cwd,cwd_pin,cwd_digest);
    SplArray* unavailable=rt_process_observation_v4_start_value(request);
    assert(rt_array_get(tuple_item(unavailable,3),3)==POV4_STATUS_REJECTED);
    SplArray* started=rt_process_observation_v4_start_pinned_value(77,cwd_pin,request);
    SplArray* words=tuple_item(started,3);
    assert(rt_array_get(words,3)==POV4_STATUS_RUNNING);
    assert(rt_array_get(words,13)==POV4_EXEC_CONFIRMED);
    assert(rt_array_get(words,22)>=rt_array_get(words,21));
    SplArray* ticket=ticket_from(words); SplArray* frozen=NULL;
    for (int i=0;i<100;i++) {
        frozen=rt_process_observation_v4_collect_value(ticket,50000000);
        words=tuple_item(frozen,3);
        if (rt_array_get(words,1)==POV4_KIND_FROZEN) break;
    }
    assert(frozen && rt_array_get(words,1)==POV4_KIND_FROZEN);
    assert(rt_array_get(words,3)==POV4_STATUS_TERMINAL);
    assert(rt_array_get(words,47)==1 && rt_array_get(words,13)==POV4_EXEC_CONFIRMED);
    SplArray* out=tuple_item(frozen,0), *err=tuple_item(frozen,1), *digest=tuple_item(frozen,2);
    assert(out->len==(int64_t)strlen(cwd) && err->len==4 && digest->len==32);
    for (size_t i=0;i<strlen(cwd);i++) assert(rt_array_get(out,(int64_t)i)==(uint8_t)cwd[i]);
    assert(rt_array_get(err,0)=='f' && rt_array_get(err,3)=='r');
    SplArray* ack=rt_process_observation_v4_ack_collect_value(ticket,digest);
    assert(rt_array_get(tuple_item(ack,3),1)==POV4_KIND_ACK);
    SplArray* duplicate=rt_process_observation_v4_ack_collect_value(ticket,digest);
    assert(rt_array_get(tuple_item(duplicate,3),3)==POV4_STATUS_REJECTED);

    /* A forced post-fork/pre-exec failure returns retained cleanup authority,
     * never a false pre-spawn Rejected receipt. */
    rt_process_observation_v4_test_force_exec_failure(EACCES,1);
    rt_process_observation_v4_test_force_signal_gone(1);
    rt_process_observation_v4_test_force_reconcile_eintr(2);
    SplArray* cleanup_start=rt_process_observation_v4_start_pinned_value(77,cwd_pin,request);
    SplArray* cleanup_words=tuple_item(cleanup_start,3);
    assert(rt_array_get(cleanup_words,3)==POV4_STATUS_CLEANUP_PENDING);
    assert(rt_array_get(cleanup_words,13)==POV4_EXEC_PENDING);
    assert(rt_array_get(cleanup_words,14)==0);
    assert(rt_array_get(cleanup_words,11)==POV4_REASON_PROVIDER);
    assert(rt_array_get(cleanup_words,29)==0);
    assert(rt_array_get(cleanup_words,59)>=2);
    assert((rt_array_get(cleanup_words,9)&POV4_VALID_EXEC)==0);
    SplArray* cleanup_ticket=ticket_from(cleanup_words), *cleanup_frozen=NULL;
    for(int i=0;i<100;i++){
        cleanup_frozen=rt_process_observation_v4_collect_value(cleanup_ticket,50000000);
        cleanup_words=tuple_item(cleanup_frozen,3);
        if(rt_array_get(cleanup_words,1)==POV4_KIND_CLEANUP_FROZEN) break;
    }
    assert(cleanup_frozen && rt_array_get(cleanup_words,1)==POV4_KIND_CLEANUP_FROZEN);
    assert(rt_array_get(cleanup_words,3)==POV4_STATUS_PROVIDER_FAILED);
    assert(rt_array_get(cleanup_words,47)==1);
    SplArray* cleanup_digest=tuple_item(cleanup_frozen,2);
    SplArray* cleanup_replay=rt_process_observation_v4_collect_value(
        cleanup_ticket,0);
    SplArray* replay_words=tuple_item(cleanup_replay,3);
    SplArray* replay_digest=tuple_item(cleanup_replay,2);
    assert(rt_array_get(replay_words,1)==POV4_KIND_CLEANUP_FROZEN);
    assert(replay_digest->len==cleanup_digest->len);
    for(int64_t i=0;i<cleanup_digest->len;i++)
        assert(rt_array_get(replay_digest,i)==rt_array_get(cleanup_digest,i));
    SplArray* wrong_digest=rt_array_new(32);
    for(int64_t i=0;i<cleanup_digest->len;i++)
        assert(rt_array_push(wrong_digest,
            rt_array_get(cleanup_digest,i) ^ (i==0 ? 1 : 0)));
    SplArray* refused=rt_process_observation_v4_ack_collect_value(
        cleanup_ticket,wrong_digest);
    assert(rt_array_get(tuple_item(refused,3),3)==POV4_STATUS_REJECTED);
    cleanup_replay=rt_process_observation_v4_collect_value(cleanup_ticket,0);
    assert(rt_array_get(tuple_item(cleanup_replay,3),1)==POV4_KIND_CLEANUP_FROZEN);
    SplArray* cleanup_ack=rt_process_observation_v4_ack_collect_value(
        cleanup_ticket,cleanup_digest);
    assert(rt_array_get(tuple_item(cleanup_ack,3),1)==POV4_KIND_CLEANUP_ACK);

    /* Use the existing component pin seam to supply a non-executable file.
     * fexecve must return an errno here. RLIMIT_AS=1 is not deterministic:
     * Linux can instead kill the child after exec's point of no return.
     * This is child-error classification evidence, not real pin admission. */
    test_exec_path = "/dev/null";
    set_u64_at(request,64,0);
    set_u64_at(request,72,POV4_ENFORCEMENT_NONE);
    SplArray* child_failed=rt_process_observation_v4_start_pinned_value(
        77,cwd_pin,request);
    SplArray* child_failed_words=tuple_item(child_failed,3);
    assert(rt_array_get(child_failed_words,3)==POV4_STATUS_CLEANUP_PENDING);
    assert(rt_array_get(child_failed_words,13)==POV4_EXEC_FAILED);
    assert(rt_array_get(child_failed_words,14)>0);
    assert(rt_array_get(child_failed_words,11)==POV4_REASON_EXEC);
    SplArray* child_failed_ticket=ticket_from(child_failed_words);
    SplArray* child_failed_frozen=NULL;
    for(int i=0;i<100;i++){
        child_failed_frozen=rt_process_observation_v4_collect_value(
            child_failed_ticket,50000000);
        child_failed_words=tuple_item(child_failed_frozen,3);
        if(rt_array_get(child_failed_words,1)==POV4_KIND_CLEANUP_FROZEN) break;
    }
    assert(child_failed_frozen &&
        rt_array_get(child_failed_words,1)==POV4_KIND_CLEANUP_FROZEN);
    SplArray* child_failed_digest=tuple_item(child_failed_frozen,2);
    SplArray* child_failed_ack=rt_process_observation_v4_ack_collect_value(
        child_failed_ticket,child_failed_digest);
    assert(rt_array_get(tuple_item(child_failed_ack,3),1)==POV4_KIND_CLEANUP_ACK);
    assert(rt_process_observation_v4_close_cwd_value(cwd_pin)==1);
    puts("runtime_process_observation_v4_selfcheck: PASS");
    return 0;
}
#endif
