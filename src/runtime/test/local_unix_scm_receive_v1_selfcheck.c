/* NEW real SCM receive/adopt mechanism witness. Raw service peers and pipe
 * producers are TEST owned; no peer auth/grant or helper lifecycle is faked.
 * Link actual runtime_process.c and other normal CoreC owners. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_socket_nonblock.c"
#include <assert.h>
#if !defined(__linux__)
int main(void){return 77;}
#else
#include <dirent.h>
static const char* binding="aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa";
static int64_t sw(SplArray* a,int i){assert(a&&rt_array_len(a)>i);return rt_value_as_int(rt_array_get(a,i));}
static int fd_count(void){DIR* d=opendir("/proc/self/fd");assert(d);int n=0;while(readdir(d))n++;assert(closedir(d)==0);return n;}
static void send_fd(int peer,int fd,int number,char byte) {
    union{struct cmsghdr align;unsigned char bytes[CMSG_SPACE(32*sizeof(int))];} control;
    memset(&control,0,sizeof(control));struct iovec io={&byte,1};struct msghdr message={0};
    message.msg_iov=&io;message.msg_iovlen=1;message.msg_control=control.bytes;message.msg_controllen=CMSG_SPACE(number*sizeof(int));
    struct cmsghdr* c=CMSG_FIRSTHDR(&message);c->cmsg_level=SOL_SOCKET;c->cmsg_type=SCM_RIGHTS;c->cmsg_len=CMSG_LEN(number*sizeof(int));
    for(int i=0;i<number;i++)((int*)CMSG_DATA(c))[i]=fd;
    assert(sendmsg(peer,&message,MSG_NOSIGNAL)==1);
}
static int64_t client_owner(const char* path,int listener,int* peer) {
    SplArray* a=rt_local_unix_connect_v1(path,strlen(path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+500);
    assert(sw(a,0)==0);int64_t t=sw(a,1);rt_array_free(a);assert(t>0);
    *peer=accept4(listener,NULL,NULL,SOCK_CLOEXEC|SOCK_NONBLOCK);assert(*peer>=0);
    a=rt_local_unix_shutdown_write_v1(t);assert(sw(a,0)==0&&sw(a,1)==1);rt_array_free(a);
    return t;
}
static void state(int64_t token,int expected){SplArray* a=rt_local_unix_handoff_state_v1(token);assert(sw(a,0)==0&&sw(a,1)==expected);rt_array_free(a);}
int main(void) {
    alarm(15);char root[]="/tmp/simple-unix-scm-v1-XXXXXX";assert(mkdtemp(root));assert(chmod(root,0700)==0);
    char path[108];snprintf(path,sizeof(path),"%s/socket",root);
    int listener=socket(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC,0);assert(listener>=0);
    struct sockaddr_un address={0};address.sun_family=AF_UNIX;strcpy(address.sun_path,path);
    assert(bind(listener,(struct sockaddr*)&address,sizeof(address))==0&&listen(listener,8)==0);
    int peer;int64_t token=client_owner(path,listener,&peer);state(token,0);
    SplArray* a=rt_local_unix_read_handoff_now_v1(token,16);assert(sw(a,0)==-11&&!sw(a,1));rt_array_free(a);
    int source[2];assert(pipe2(source,O_NONBLOCK|O_CLOEXEC)==0);
    send_fd(peer,source[0],1,'M');close(source[0]);
    a=rt_local_unix_read_handoff_now_v1(token,16);assert(sw(a,0)==0&&sw(a,2)==1&&sw(a,3)=='M');rt_array_free(a);state(token,3);
    int status;LuSlotV1* slot=lu_lock_v1(token,&status);assert(slot);int original_pending=slot->pending_fd;assert(original_pending>=0);pthread_mutex_unlock(&slot->operation);
    a=rt_local_unix_read_handoff_now_v1(token,16);assert(sw(a,0)==-11&&sw(a,2)==0);rt_array_free(a);state(token,3);
    slot=lu_lock_v1(token,&status);assert(slot&&slot->pending_fd==original_pending);pthread_mutex_unlock(&slot->operation);
    int extra[2];assert(pipe2(extra,O_NONBLOCK|O_CLOEXEC)==0);
    for(int number=1;number<=32;number+=31) {
        int before=fd_count();send_fd(peer,extra[0],number,'X');
        a=rt_local_unix_read_handoff_now_v1(token,16);assert(sw(a,0)==-9&&sw(a,2)==1&&sw(a,3)=='X');rt_array_free(a);
        assert(fd_count()==before);state(token,3);
        slot=lu_lock_v1(token,&status);assert(slot&&slot->pending_fd==original_pending);pthread_mutex_unlock(&slot->operation);
    }
    close(extra[0]);close(extra[1]);
    a=rt_local_unix_adopt_byte_endpoint_v1(token,binding,64);assert(sw(a,0)==-15&&!sw(a,1));rt_array_free(a);
    assert(shutdown(peer,SHUT_WR)==0);
    a=rt_local_unix_read_handoff_now_v1(token,16);assert(sw(a,0)==0&&sw(a,1)==1&&sw(a,2)==0);rt_array_free(a);state(token,3);
    /* Exhaust the SAME actual pipe registry with descriptor-only owners. No
     * process/PID, accepted flag or helper cleanup proof is manufactured. */
    int64_t generations[16];int writers[16],count=0;
    for(;count<16;count++) {
        int endpoints[2];assert(pipe2(endpoints,O_NONBLOCK|O_CLOEXEC)==0);int64_t generation=0;
        int64_t rc=simple_process_byte_adopt_v1(endpoints[0],binding,64,&generation);
        if(rc==-5){close(endpoints[0]);close(endpoints[1]);break;}
        assert(rc==0&&generation>0);generations[count]=generation;writers[count]=endpoints[1];
    }
    assert(count>0);
    a=rt_local_unix_adopt_byte_endpoint_v1(token,binding,64);assert(sw(a,0)==-5&&!sw(a,1));rt_array_free(a);state(token,3);
    a=rt_local_unix_adopt_byte_endpoint_v1(token,"bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb",64);assert(sw(a,0)==-16&&!sw(a,1));rt_array_free(a);state(token,3);
    slot=lu_lock_v1(token,&status);assert(slot&&slot->pending_fd==original_pending);pthread_mutex_unlock(&slot->operation);
    a=rt_process_close_byte_endpoint_v1(generations[0],binding,64);assert(sw(a,0)==0&&sw(a,1)==1);rt_array_free(a);close(writers[0]);
    a=rt_local_unix_adopt_byte_endpoint_v1(token,binding,64);assert(sw(a,0)==0&&sw(a,1)>0);int64_t adopted=sw(a,1);rt_array_free(a);state(token,4);
    a=rt_local_unix_adopt_byte_endpoint_v1(token,binding,64);assert(sw(a,0)==-16&&!sw(a,1));rt_array_free(a);
    assert(write(source[1],"Q",1)==1);close(source[1]);
    a=rt_process_read_byte_endpoint_v1(adopted,binding,64);assert(sw(a,0)==0&&sw(a,2)==1&&sw(a,3)=='Q');rt_array_free(a);
    a=rt_process_read_byte_endpoint_v1(adopted,binding,64);assert(sw(a,0)==0&&sw(a,1)==1&&sw(a,2)==0);rt_array_free(a);
    a=rt_process_close_byte_endpoint_v1(adopted,binding,64);assert(sw(a,0)==0&&sw(a,1)==1);rt_array_free(a);
    assert(rt_process_validate_byte_endpoint_v1(adopted,binding,64)==-2);
    for(int i=1;i<count;i++){a=rt_process_close_byte_endpoint_v1(generations[i],binding,64);assert(sw(a,1)==1);rt_array_free(a);close(writers[i]);}
    a=rt_local_unix_close_v1(token);assert(sw(a,1)==1);rt_array_free(a);close(peer);
    /* A queued but unadopted received descriptor is disposed on socket close. */
    token=client_owner(path,listener,&peer);assert(pipe2(source,O_NONBLOCK|O_CLOEXEC)==0);send_fd(peer,source[0],1,'D');close(source[0]);
    a=rt_local_unix_read_handoff_now_v1(token,16);assert(sw(a,0)==0);rt_array_free(a);
    slot=lu_lock_v1(token,&status);assert(slot);int pending=slot->pending_fd;pthread_mutex_unlock(&slot->operation);assert(pending>=0);
    a=rt_local_unix_close_v1(token);assert(sw(a,1)==1);rt_array_free(a);
    assert(fcntl(pending,F_GETFD)<0&&errno==EBADF);close(source[1]);close(peer);
    close(listener);assert(unlink(path)==0&&rmdir(root)==0);
    puts("PASS SCM receive ownership/extra+truncated disposal/EOF/capacity retention/adopt replay/byte EOF; authenticated stage/send integration NOT_RUN");return 0;
}
#endif
