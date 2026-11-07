/* AUTHORED_UNRUN. Actual private files/kernel no-replace, no socket claims.
 * Requires isolated privileged Linux fixture for the actual foreign-UID case.
 * close fault injection consumes the REAL fd, then returns EINTR once. */
#define _GNU_SOURCE
#include <unistd.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <fcntl.h>
#include <assert.h>
static int fail_consumed_close_once=0;
static int credential_test_close(int fd) {
    int result=close(fd);
    if (fail_consumed_close_once && result==0) {
        fail_consumed_close_once=0; errno=EINTR; return -1;
    }
    return result;
}
#define close credential_test_close
#define SIMPLE_RETAINED_PRIVATE_CREDENTIAL_IMPLEMENTATION
#include "../../../src/runtime/runtime_retained_private_credential_v1.h"
#undef close

static const char initial[]="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb\n";
static const char incarnation[]="cccccccccccccccccccccccccccccccc";
static int64_t ptr(const void *p) { return (int64_t)(intptr_t)p; }
static void put(const char *path,const char *bytes) {
    int fd=open(path,O_WRONLY|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC,0600); assert(fd>=0);
    assert(fchmod(fd,0600)==0); assert(write(fd,bytes,strlen(bytes))==(ssize_t)strlen(bytes));
    assert(fsync(fd)==0); assert(close(fd)==0);
}
static void same_file(const char *path,const char *expected) {
    char bytes[513]={0}; struct stat s;
    int fd=open(path,O_RDONLY|O_NOFOLLOW|O_CLOEXEC); assert(fd>=0);
    assert(fstat(fd,&s)==0 && S_ISREG(s.st_mode) && s.st_uid==geteuid() && (s.st_mode&07777)==0600 && s.st_nlink==1);
    assert(read(fd,bytes,sizeof(bytes))==(ssize_t)strlen(expected)); assert(!memcmp(bytes,expected,strlen(expected)));
    assert(close(fd)==0);
}
static int64_t acquire(const char *path) { return rt_retained_private_credential_open_v1(ptr(path),(int64_t)strlen(path)); }
static void ready_bytes(char *out,size_t size,pid_t pid) {
    snprintf(out,size,"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa 127.0.0.1:1 bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb %ld %s\n",(long)pid,incarnation);
}
static int64_t publish(int64_t token,const char *ready) {
    return rt_retained_private_credential_publish_v1(token,ptr(initial),sizeof(initial)-1,ptr(ready),(int64_t)strlen(ready));
}
int main(int argc,char **argv) {
#if !defined(__linux__)
    (void)argc;(void)argv; fprintf(stderr,"precondition: actual Linux owner required\n"); return 1;
#else
    alarm(20);
    if (argc==3 && !strcmp(argv[1],"--race")) {
        char ready[512]; ready_bytes(ready,sizeof(ready),getpid());
        int64_t token=acquire(argv[2]); assert(token>0);
        assert(rt_retained_private_credential_state_v1(token)==RPC_OPEN);
        int64_t result=publish(token,ready);
        assert(result==0 || result==RPC_CONFLICT);
        assert(rt_retained_private_credential_close_v1(token)==0);
        return result==0?0:2;
    }
    if (geteuid()!=0) { fprintf(stderr,"precondition: isolated privileged UID-mismatch fixture required\n"); return 1; }
    char root[]="/tmp/simple-private-credential-XXXXXX"; assert(mkdtemp(root)); assert(chmod(root,0700)==0);
    char path[512],ready_path[520],ready[512];
    snprintf(path,sizeof(path),"%s/owner",root); snprintf(ready_path,sizeof(ready_path),"%s.ready",path);
    ready_bytes(ready,sizeof(ready),getpid()); put(path,initial);
    int64_t first=acquire(path); assert(first>0 && rt_retained_private_credential_state_v1(first)==RPC_OPEN);
    int64_t copied=first; assert(rt_retained_private_credential_close_v1(first)==0);
    int64_t successor=acquire(path); assert(successor>first);
    assert(rt_retained_private_credential_close_v1(copied)==RPC_STALE);
    uint8_t readback[512]; assert(rt_retained_private_credential_read_v1(successor,ptr(readback),512)==(int64_t)strlen(initial));
    pid_t child=fork(); assert(child>=0);
    if (!child) _exit(rt_retained_private_credential_close_v1(successor)==RPC_FORK?0:1);
    int status=0; assert(waitpid(child,&status,0)==child && WIFEXITED(status) && WEXITSTATUS(status)==0);
    assert(publish(successor,ready)==0); assert(publish(successor,ready)==RPC_STATE);
    assert(rt_retained_private_credential_close_v1(successor)==0); same_file(path,initial); same_file(ready_path,ready);
    int64_t conflict=acquire(path); assert(conflict>0 && publish(conflict,ready)==RPC_CONFLICT);
    assert(rt_retained_private_credential_state_v1(conflict)==RPC_UNCERTAIN);
    assert(rt_retained_private_credential_close_v1(conflict)==0); same_file(ready_path,ready);
    /* A failed close consumes the real descriptor; stale copies cannot retry. */
    int64_t consumed=acquire(path); fail_consumed_close_once=1;
    assert(rt_retained_private_credential_close_v1(consumed)==RPC_CONSUMED);
    assert(rt_retained_private_credential_state_v1(consumed)==RPC_UNCERTAIN);
    int unrelated=open(path,O_RDONLY|O_CLOEXEC); assert(unrelated>=0);
    assert(rt_retained_private_credential_close_v1(consumed)==RPC_STATE);
    struct stat live; assert(fstat(unrelated,&live)==0); assert(close(unrelated)==0);
    /* Exact final mode, foreign UID and symlink rejection use real metadata. */
    assert(chmod(path,0640)==0); int64_t denied=acquire(path); assert(denied>0 && rt_retained_private_credential_state_v1(denied)==RPC_UNCERTAIN); assert(rt_retained_private_credential_close_v1(denied)==0);
    assert(chmod(path,0600)==0); assert(chown(path,1,1)==0); denied=acquire(path); assert(denied>0 && rt_retained_private_credential_state_v1(denied)==RPC_UNCERTAIN); assert(rt_retained_private_credential_close_v1(denied)==0); assert(chown(path,0,0)==0);
    char alias[512]; snprintf(alias,sizeof(alias),"%s/alias",root); assert(symlink("owner",alias)==0);
    denied=acquire(alias); assert(denied>0 && rt_retained_private_credential_state_v1(denied)==RPC_UNCERTAIN); assert(rt_retained_private_credential_close_v1(denied)==0); assert(unlink(alias)==0);
    /* No writer exists: a blocking leaf open would hit the global watchdog. */
    char fifo[512]; snprintf(fifo,sizeof(fifo),"%s/fifo",root); assert(mkfifo(fifo,0600)==0);
    denied=acquire(fifo); assert(denied>0 && rt_retained_private_credential_state_v1(denied)==RPC_UNCERTAIN); assert(rt_retained_private_credential_close_v1(denied)==0); assert(unlink(fifo)==0);
    char unsafe[512],nested[512],unsafe_owner[512]; snprintf(unsafe,sizeof(unsafe),"%s/unsafe",root); assert(mkdir(unsafe,0777)==0); assert(chmod(unsafe,0777)==0);
    snprintf(nested,sizeof(nested),"%s/private",unsafe); assert(mkdir(nested,0700)==0); snprintf(unsafe_owner,sizeof(unsafe_owner),"%s/owner",nested); put(unsafe_owner,initial);
    denied=acquire(unsafe_owner); assert(denied>0 && rt_retained_private_credential_state_v1(denied)==RPC_UNCERTAIN); assert(rt_retained_private_credential_close_v1(denied)==0);
    assert(unlink(unsafe_owner)==0 && rmdir(nested)==0 && rmdir(unsafe)==0);
    /* Anchored directory remains authoritative after path replacement. */
    char held[512],moved[512],held_owner[520],moved_owner[520],moved_ready[530];
    snprintf(held,sizeof(held),"%s/held",root); snprintf(moved,sizeof(moved),"%s/moved",root); assert(mkdir(held,0700)==0);
    snprintf(held_owner,sizeof(held_owner),"%s/owner",held); put(held_owner,initial); int64_t anchored=acquire(held_owner); assert(anchored>0);
    assert(rename(held,moved)==0 && mkdir(held,0700)==0); put(held_owner,initial);
    assert(publish(anchored,ready)==0 && rt_retained_private_credential_close_v1(anchored)==0);
    snprintf(moved_owner,sizeof(moved_owner),"%s/owner",moved); snprintf(moved_ready,sizeof(moved_ready),"%s/owner.ready",moved); same_file(moved_ready,ready);
    char absent[530]; snprintf(absent,sizeof(absent),"%s/owner.ready",held); assert(access(absent,F_OK)!=0);
    assert(unlink(held_owner)==0 && rmdir(held)==0 && unlink(moved_owner)==0 && unlink(moved_ready)==0 && rmdir(moved)==0);
    /* Separate exec processes prove no-replace is kernel-wide, not our mutex. */
    assert(unlink(ready_path)==0);
    pid_t racers[2]; for (int i=0;i<2;i++) { racers[i]=fork(); assert(racers[i]>=0); if (!racers[i]) { execl(argv[0],argv[0],"--race",path,(char *)NULL); _exit(99); } }
    int results[2]; for (int i=0;i<2;i++) { assert(waitpid(racers[i],&status,0)==racers[i] && WIFEXITED(status)); results[i]=WEXITSTATUS(status); }
    assert((results[0]==0 && results[1]==2)||(results[0]==2 && results[1]==0)); ready_bytes(ready,sizeof(ready),racers[results[0]==0?0:1]); same_file(ready_path,ready);
    same_file(path,initial); assert(unlink(path)==0 && unlink(ready_path)==0 && rmdir(root)==0);
    return 0;
#endif
}
