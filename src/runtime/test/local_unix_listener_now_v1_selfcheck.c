/* NEW listener/zero-wait contract fixture. Raw peers and filesystem mutation
 * are TEST harness ownership only. Actual runtime allocator included once. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_native.c"
#include "../runtime_socket_nonblock.c"
#include <assert.h>
#if !defined(__linux__)
int main(void){return 77;}
#else
#include <sys/wait.h>
static int64_t lword(SplArray* a,int i){assert(a&&rt_array_len(a)>i);return rt_value_as_int(rt_array_get(a,i));}
static int64_t listener_owner(const char* path) {
    SplArray* a=rt_local_unix_listen_v1(path,strlen(path),geteuid(),8);
    assert(lword(a,0)==0&&lword(a,1)>0);int64_t t=lword(a,1);rt_array_free(a);return t;
}
static void rejected(SplArray* a,int expected){assert(lword(a,0)==expected);rt_array_free(a);}
int main(void) {
    alarm(15);char root[]="/tmp/simple-unix-listener-v1-XXXXXX";assert(mkdtemp(root));assert(chmod(root,0755)==0);
    char path[108],existing[108],raw_path[108],aside[108],child_path[108];
    snprintf(path,sizeof(path),"%s/service",root);snprintf(existing,sizeof(existing),"%s/existing",root);
    snprintf(raw_path,sizeof(raw_path),"%s/raw",root);snprintf(aside,sizeof(aside),"%s/aside",root);snprintf(child_path,sizeof(child_path),"%s/child",root);
    int f=open(existing,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC,0600);assert(f>=0&&write(f,"keep",4)==4);close(f);
    SplArray* a=rt_local_unix_listen_v1(existing,strlen(existing),geteuid(),8);assert(lword(a,0)!=0&&lword(a,1)>0);
    int64_t rejected_owner=lword(a,1);rt_array_free(a);
    a=rt_local_unix_listener_close_v1(rejected_owner);assert(lword(a,1)==1);rt_array_free(a);
    f=open(existing,O_RDONLY|O_CLOEXEC);char keep[4];assert(f>=0&&read(f,keep,4)==4&&!memcmp(keep,"keep",4));close(f);
    int64_t listener=listener_owner(path);struct stat node;assert(lstat(path,&node)==0&&S_ISSOCK(node.st_mode)&&(node.st_mode&0777)==0666);
    rejected(rt_local_unix_accept_v1(listener,geteuid()),-1);
    rejected(rt_local_unix_accept_v1(listener,(int64_t)geteuid()+1),-11);
    rejected(rt_local_unix_close_v1(listener),-1);rejected(rt_local_unix_read_now_v1(listener,1),-1);
    rejected(rt_local_unix_poll_v1(listener,1,0),-1);rejected(rt_local_unix_peer_v1(listener),-1);
    a=rt_local_unix_connect_v1(path,strlen(path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+500);assert(lword(a,0)==0);
    int64_t refused_client=lword(a,1);rt_array_free(a);
    rejected(rt_local_unix_accept_v1(listener,(int64_t)geteuid()+1),-3); /* actual same-UID client denied */
    a=rt_local_unix_read_now_v1(refused_client,1);assert(lword(a,0)==0&&lword(a,1)==1);rt_array_free(a);
    a=rt_local_unix_close_v1(refused_client);assert(lword(a,1)==1);rt_array_free(a);
    puts("BLOCKED distinct-UID accepted/one-use claim positive: separately provisioned external peer required");
    int raw=socket(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC,0);assert(raw>=0);
    struct sockaddr_un address={0};address.sun_family=AF_UNIX;strcpy(address.sun_path,raw_path);
    assert(bind(raw,(struct sockaddr*)&address,sizeof(address))==0&&listen(raw,8)==0);
    a=rt_local_unix_connect_v1(raw_path,strlen(raw_path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+500);assert(lword(a,0)==0);
    int64_t connection=lword(a,1);rt_array_free(a);int peer=accept4(raw,NULL,NULL,SOCK_CLOEXEC|SOCK_NONBLOCK);assert(peer>=0);
    rejected(rt_local_unix_listener_close_v1(connection),-1);
    a=rt_local_unix_peer_v1(connection);assert(lword(a,0)==0&&lword(a,1)==geteuid()&&lword(a,3)==getpid());rt_array_free(a);
    a=rt_local_unix_poll_v1(connection,1,1);assert(lword(a,0)==0&&!lword(a,1)&&lword(a,2));rt_array_free(a);
    rejected(rt_local_unix_read_now_v1(connection,1),-11);
    SplArray* bytes=lu_receipt_v1(1);assert(bytes);lu_word_v1(bytes,0,'W');
    a=rt_local_unix_write_some_now_v1(connection,bytes,0,1);assert(lword(a,0)==0&&lword(a,1)==1);rt_array_free(a);
    char byte;assert(recv(peer,&byte,1,MSG_DONTWAIT)==1&&byte=='W');assert(send(peer,"Z",1,MSG_NOSIGNAL)==1);
    a=rt_local_unix_poll_v1(connection,1,0);assert(lword(a,0)==0&&lword(a,1));rt_array_free(a);
    a=rt_local_unix_read_now_v1(connection,1);assert(lword(a,0)==0&&lword(a,2)==1&&lword(a,3)=='Z');rt_array_free(a);
    /* Every NEW export rejects inherited owners before actual allocator/owner
     * locks. No old green native fixture is rerun by this witness. */
    int status;LuSlotV1* ls=lu_lock_v1(listener,&status);assert(ls&&status==0);
    LuSlotV1* cs=lu_lock_v1(connection,&status);assert(cs&&status==0);
    assert(pthread_mutex_lock(&lu_registry_v1)==0);
    assert(!atomic_flag_test_and_set_explicit(&rt_core_immortal_registry_lock,memory_order_acquire));
    pid_t child=fork();assert(child>=0);
    if(child==0) {
        alarm(3);
        assert(rt_local_unix_listen_v1(child_path,strlen(child_path),geteuid(),8)==NULL);
        assert(rt_local_unix_accept_v1(listener,(int64_t)geteuid()+1)==NULL);
        assert(rt_local_unix_poll_v1(connection,1,1)==NULL);
        assert(rt_local_unix_read_now_v1(connection,1)==NULL);
        assert(rt_local_unix_write_some_now_v1(connection,bytes,0,1)==NULL);
        assert(rt_local_unix_listener_close_v1(listener)==NULL);
        assert(rt_local_unix_peer_v1(connection)==NULL);
        assert(rt_local_unix_shutdown_write_v1(connection)==NULL);
        assert(rt_local_unix_claim_request_v1(connection,"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",64)==NULL);
        assert(rt_local_unix_stage_stdout_v1(connection,getpid(),1,"/unused",7,"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",64,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",64)==NULL);
        assert(rt_local_unix_read_handoff_now_v1(connection,1)==NULL);
        assert(rt_local_unix_adopt_byte_endpoint_v1(connection,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",64)==NULL);
        assert(rt_local_unix_handoff_state_v1(connection)==NULL);
        _exit(0);
    }
    assert(waitpid(child,&status,0)==child&&WIFEXITED(status)&&WEXITSTATUS(status)==0);
    atomic_flag_clear_explicit(&rt_core_immortal_registry_lock,memory_order_release);
    pthread_mutex_unlock(&lu_registry_v1);pthread_mutex_unlock(&cs->operation);pthread_mutex_unlock(&ls->operation);
    assert(lstat(child_path,&node)<0&&errno==ENOENT);
    a=rt_local_unix_shutdown_write_v1(connection);assert(lword(a,0)==0&&lword(a,1)==1);rt_array_free(a);
    a=rt_local_unix_shutdown_write_v1(connection);assert(lword(a,0)==0&&lword(a,1)==1);rt_array_free(a);
    rejected(rt_local_unix_write_some_now_v1(connection,bytes,0,1),-12);
    assert(recv(peer,&byte,1,MSG_DONTWAIT)==0);assert(send(peer,"T",1,MSG_NOSIGNAL)==1);
    a=rt_local_unix_read_now_v1(connection,1);assert(lword(a,0)==0&&lword(a,3)=='T');rt_array_free(a);
    rejected(rt_local_unix_claim_request_v1(connection,"aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",64),-13);
    a=rt_local_unix_close_v1(connection);assert(lword(a,1)==1);rt_array_free(a);rt_array_free(bytes);close(peer);close(raw);
    ls=lu_lock_v1(listener,&status);assert(ls);int old_fd=ls->fd;pthread_mutex_unlock(&ls->operation);
    assert(rename(path,aside)==0);f=open(path,O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC,0600);assert(f>=0);close(f);
    a=rt_local_unix_listener_close_v1(listener);assert(lword(a,0)==-3&&!lword(a,1));rt_array_free(a);
    ls=lu_lock_v1(listener,&status);assert(ls&&ls->fd==-1&&ls->parent_fd>=0);pthread_mutex_unlock(&ls->operation);
    f=open("/dev/null",O_RDONLY|O_CLOEXEC);assert(f>=0);if(f!=old_fd){assert(dup3(f,old_fd,O_CLOEXEC)==old_fd);close(f);f=old_fd;}
    a=rt_local_unix_listener_close_v1(listener);assert(lword(a,0)==-3&&!lword(a,1));rt_array_free(a);assert(fcntl(f,F_GETFD)>=0);
    assert(unlink(path)==0&&rename(aside,path)==0);
    a=rt_local_unix_listener_close_v1(listener);assert(lword(a,0)==0&&lword(a,1)==1);rt_array_free(a);assert(fcntl(f,F_GETFD)>=0);close(f);
    rejected(rt_local_unix_listener_close_v1(listener),-2);
    assert(unlink(existing)==0&&unlink(raw_path)==0&&rmdir(root)==0);
    puts("PASS new listener roles/cleanup, zero-wait bytes/peer/half-close, new-port fork refusal; SCM frame transport NOT_RUN");
    return 0;
}
#endif
