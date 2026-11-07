/* NEW fork-origin witness. Normal CoreC providers only. No old green fixture
 * rerun. Test harness owns the raw listener and observes inherited fd state. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_native.c" /* actual allocator owner exactly once */
#include "../runtime_socket_nonblock.c"
#include <assert.h>
#if !defined(__linux__)
int main(void){return 77;}
#else
#include <sys/wait.h>
static int64_t fork_word_v1(SplArray* a,int index) {
    assert(a&&rt_array_len(a)>index);return rt_value_as_int(rt_array_get(a,index));
}
static void foreign(SplArray* receipt) {
    /* No runtime array read/free/length operation on an absent receipt. */
    assert(receipt==NULL);
}
int main(void) {
    alarm(12);
    /* No registry/FD/owner has existed: first-use child may independently bind
     * its zero-initialized origin. It cannot reconstruct any parent owner. */
    assert(atomic_load_explicit(&lu_process_origin_v1,memory_order_acquire)==0);
    pid_t first=fork();assert(first>=0);
    if(first==0) {
        alarm(2);SplArray* a=rt_local_unix_close_v1(0);
        assert(fork_word_v1(a,0)==-1&&!fork_word_v1(a,1));rt_array_free(a);
        assert(atomic_load_explicit(&lu_process_origin_v1,memory_order_acquire)==(unsigned int)getpid());
        struct stat child_namespace;assert(lu_namespace_v1(&child_namespace));
        assert(atomic_load_explicit(&lu_process_origin_ready_v1,memory_order_acquire)==1);
        assert(lu_origin_namespace_device_v1==child_namespace.st_dev&&lu_origin_namespace_inode_v1==child_namespace.st_ino);
        _exit(0);
    }
    int status=0;assert(waitpid(first,&status,0)==first&&WIFEXITED(status)&&WEXITSTATUS(status)==0);
    assert(atomic_load_explicit(&lu_process_origin_v1,memory_order_acquire)==0);
    char root[]="/tmp/simple-unix-fork-v1-XXXXXX";assert(mkdtemp(root));assert(chmod(root,0700)==0);
    char path[108];assert(snprintf(path,sizeof(path),"%s/socket",root)>0);
    int server=socket(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC|SOCK_NONBLOCK,0);assert(server>=0);
    struct sockaddr_un address={0};address.sun_family=AF_UNIX;strcpy(address.sun_path,path);
    assert(bind(server,(struct sockaddr*)&address,sizeof(address))==0&&listen(server,8)==0);
    SplArray* receipt=rt_local_unix_connect_v1(path,strlen(path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+500);
    assert(fork_word_v1(receipt,0)==0);int64_t token=fork_word_v1(receipt,1);assert(token>0);rt_array_free(receipt);
    int peer=accept4(server,NULL,NULL,SOCK_CLOEXEC|SOCK_NONBLOCK);assert(peer>=0);
    /* Actual unprivileged namespace observation only. No namespace-changing
     * or PID-collision scenario is manufactured or claimed by this fixture. */
    struct stat parent_namespace;assert(lu_namespace_v1(&parent_namespace));
    assert(atomic_load_explicit(&lu_process_origin_ready_v1,memory_order_acquire)==1);
    assert(lu_origin_namespace_device_v1==parent_namespace.st_dev&&lu_origin_namespace_inode_v1==parent_namespace.st_ino);
    SplArray* bytes=lu_receipt_v1(1);assert(bytes);lu_word_v1(bytes,0,'X');
    assert(send(peer,"P",1,MSG_NOSIGNAL)==1);
    int lock_status;LuSlotV1* slot=lu_lock_v1(token,&lock_status);assert(slot&&lock_status==0);
    int inherited_fd=slot->fd;
    assert(pthread_mutex_lock(&lu_registry_v1)==0);
    assert(!atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock,memory_order_acquire));
    /* All three inherited gates are held, including the REAL generic allocator
     * registry spinlock. Even allocating an error array here would deadlock. */
    pid_t child=fork();assert(child>=0);
    if(child==0) {
        alarm(3);int64_t deadline=lu_clock_v1(CLOCK_MONOTONIC)+500;
        foreign(rt_local_unix_connect_v1(path,strlen(path),geteuid(),deadline));
        foreign(rt_local_unix_read_v1(token,1,deadline));
        foreign(rt_local_unix_write_some_v1(token,bytes,0,1,deadline));
        foreign(rt_local_unix_write_some_admitted_v1(token,bytes,0,1,deadline,lu_clock_v1(CLOCK_REALTIME)+1000));
        foreign(rt_local_unix_close_v1(token));
        assert(fcntl(inherited_fd,F_GETFD)>=0); /* rejected close did not act */
        char c=0;assert(recv(inherited_fd,&c,1,MSG_PEEK|MSG_DONTWAIT)==1&&c=='P');
        assert(recv(peer,&c,1,MSG_DONTWAIT)<0&&(errno==EAGAIN||errno==EWOULDBLOCK));
        int extra=accept4(server,NULL,NULL,SOCK_CLOEXEC|SOCK_NONBLOCK);
        assert(extra<0&&(errno==EAGAIN||errno==EWOULDBLOCK)); /* connect had no effect */
        _exit(0);
    }
    assert(waitpid(child,&status,0)==child&&WIFEXITED(status)&&WEXITSTATUS(status)==0);
    atomic_flag_clear_explicit(&rt_core_immortal_registry_lock,memory_order_release);
    assert(pthread_mutex_unlock(&lu_registry_v1)==0);
    assert(pthread_mutex_unlock(&slot->operation)==0);
    receipt=rt_local_unix_read_v1(token,1,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(fork_word_v1(receipt,0)==0&&fork_word_v1(receipt,2)==1&&fork_word_v1(receipt,3)=='P');rt_array_free(receipt);
    receipt=rt_local_unix_write_some_v1(token,bytes,0,1,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(fork_word_v1(receipt,0)==0&&fork_word_v1(receipt,1)==1);rt_array_free(receipt);
    char c=0;assert(recv(peer,&c,1,MSG_DONTWAIT)==1&&c=='X');
    receipt=rt_local_unix_close_v1(token);assert(fork_word_v1(receipt,0)==0&&fork_word_v1(receipt,1)==1);rt_array_free(receipt);
    rt_array_free(bytes);close(peer);close(server);assert(unlink(path)==0&&rmdir(root)==0);
    puts("PASS fork-origin: five inherited-owner operations return NULL before owner/actual allocator held gates; parent bytes/FD preserved; pre-first-use child independent");
    return 0;
}
#endif
