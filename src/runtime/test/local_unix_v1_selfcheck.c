/* Non-Windows test: the POSIX/Linux/macOS APIs it uses have no Windows build here. */
#if defined(_WIN32)
#include <stdio.h>
int main(void) { puts("SKIP: local_unix_v1_selfcheck is POSIX-only; no Windows build"); return 77; }
#else
/* Actual Linux (and, under __APPLE__, Darwin) local-socket contract witness. Raw listeners, descriptor
 * inspection and teardown belong ONLY to this test harness. Link normal CoreC
 * providers; do not compile runtime_socket_nonblock.c separately as included. */
#if defined(__linux__) && !defined(_GNU_SOURCE)
#define _GNU_SOURCE
#endif
#include "../runtime_socket_nonblock.c"
#include <assert.h>
#if defined(__APPLE__)
/* Darwin witness (C7). Runs on a Mac only; on every other host this branch is
 * not compiled. Paths use /private/tmp because /tmp is a symlink on macOS and
 * the owner deliberately refuses symlinked ancestors. */
#include <dirent.h>
#include <sys/un.h>
static int64_t dword(SplArray* a,int index){assert(a&&rt_array_len(a)>index);return rt_value_as_int(rt_array_get(a,index));}
static int ddescriptors(void) {
    DIR* d=opendir("/dev/fd");assert(d);int count=0;
    while(readdir(d))count++;assert(closedir(d)==0);return count;
}
static int raw_accept(int listener) {
    int fd=accept(listener,NULL,NULL);assert(fd>=0);int on=1;
    assert(setsockopt(fd,SOL_SOCKET,SO_NOSIGPIPE,&on,sizeof(on))==0);return fd;
}
int main(void) {
    alarm(15);char root[]="/private/tmp/simple-unix-v1-XXXXXX";assert(mkdtemp(root));assert(chmod(root,0700)==0);
    char path[104];assert(snprintf(path,sizeof(path),"%s/socket",root)>0);
    int listener=socket(AF_UNIX,SOCK_STREAM,0);assert(listener>=0);
    struct sockaddr_un address={0};address.sun_family=AF_UNIX;strcpy(address.sun_path,path);
    assert(bind(listener,(struct sockaddr*)&address,sizeof(address))==0&&listen(listener,8)==0);
    SplArray* a=rt_local_unix_connect_v1(path,strlen(path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+500);
    /* Peer identity: getpeereid uid/gid + audit-token PID, both this process. */
    assert(dword(a,0)==0&&dword(a,1)>0&&dword(a,2)==geteuid()&&dword(a,3)==getegid()&&dword(a,4)==getpid());
    int64_t token=dword(a,1);rt_array_free(a);int peer=raw_accept(listener);
    int status;LuSlotV1* locked=lu_lock_v1(token,&status);assert(locked&&status==0);
    int on=0;socklen_t on_size=sizeof(on);
    assert((fcntl(locked->fd,F_GETFD)&FD_CLOEXEC)!=0&&(fcntl(locked->fd,F_GETFL)&O_NONBLOCK)!=0);
    assert(getsockopt(locked->fd,SOL_SOCKET,SO_NOSIGPIPE,&on,&on_size)==0&&on);
    pthread_mutex_unlock(&locked->operation);
    a=rt_local_unix_peer_v1(token);assert(dword(a,0)==0&&dword(a,1)==geteuid()&&dword(a,3)==getpid());rt_array_free(a);
    SplArray* data=lu_receipt_v1(16);assert(data);lu_word_v1(data,0,'A');
    a=rt_local_unix_write_some_v1(token,data,0,1,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(dword(a,0)==0&&dword(a,1)==1);rt_array_free(a);char b=0;assert(recv(peer,&b,1,0)==1&&b=='A');
    assert(send(peer,"BC",2,0)==2);
    a=rt_local_unix_read_v1(token,16,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(dword(a,0)==0&&!dword(a,1)&&dword(a,2)==2&&dword(a,3)=='B'&&dword(a,4)=='C');rt_array_free(a);
    a=rt_local_unix_read_now_v1(token,1);assert(dword(a,0)==-11);rt_array_free(a);
    /* Unrequested SCM_RIGHTS is rejected and every received FD is disposed. */
    int before=ddescriptors(),p[2];assert(pipe(p)==0);
    union {struct cmsghdr align;unsigned char bytes[CMSG_SPACE(sizeof(int))];} control;memset(&control,0,sizeof(control));
    char x='X';struct iovec io={&x,1};struct msghdr msg={0};msg.msg_iov=&io;msg.msg_iovlen=1;
    msg.msg_control=control.bytes;msg.msg_controllen=sizeof(control.bytes);
    struct cmsghdr* c=CMSG_FIRSTHDR(&msg);c->cmsg_level=SOL_SOCKET;c->cmsg_type=SCM_RIGHTS;c->cmsg_len=CMSG_LEN(sizeof(int));
    memcpy(CMSG_DATA(c),&p[0],sizeof(int));assert(sendmsg(peer,&msg,0)==1);close(p[0]);close(p[1]);
    a=rt_local_unix_read_v1(token,16,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(dword(a,0)==-9&&dword(a,2)==1&&dword(a,3)=='X');rt_array_free(a);assert(ddescriptors()==before);
    /* A rejected ancillary never starts a handoff. */
    a=rt_local_unix_handoff_state_v1(token);assert(dword(a,0)==0&&dword(a,1)==0);rt_array_free(a);
    a=rt_local_unix_shutdown_write_v1(token);assert(dword(a,0)==0&&dword(a,1)==1);rt_array_free(a);
    assert(recv(peer,&b,1,0)==0);
    close(peer);
    a=rt_local_unix_poll_v1(token,1,0);assert(dword(a,0)==0&&dword(a,1)==1);rt_array_free(a);
    a=rt_local_unix_close_v1(token);assert(dword(a,0)==0&&dword(a,1)==1);rt_array_free(a);
    a=rt_local_unix_close_v1(token);assert(dword(a,0)==-2&&!dword(a,1));rt_array_free(a);
    /* Path policy: symlinked ancestor, long sun_path, writable parent, wrong UID. */
    char alias[104],alias_socket[104];snprintf(alias,sizeof(alias),"%s/alias",root);assert(symlink(".",alias)==0);
    snprintf(alias_socket,sizeof(alias_socket),"%s/alias/socket",root);
    a=rt_local_unix_connect_v1(alias_socket,strlen(alias_socket),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+100);assert(dword(a,0)!=0&&!dword(a,1));rt_array_free(a);assert(unlink(alias)==0);
    a=rt_local_unix_connect_v1("/tmp/simple-unix-v1-socket",26,geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+100);assert(dword(a,0)==-1);rt_array_free(a);
    /* A real socket whose absolute path cannot fit Darwin's 104-byte sun_path
     * (bound relative to the root) is refused rather than truncated. */
    char leaf[81];memset(leaf,'a',80);leaf[80]=0;char longer[200];
    assert(snprintf(longer,sizeof(longer),"%s/%s",root,leaf)>=104);
    int far=socket(AF_UNIX,SOCK_STREAM,0);assert(far>=0&&chdir(root)==0);
    struct sockaddr_un relative={0};relative.sun_family=AF_UNIX;strcpy(relative.sun_path,leaf);
    assert(bind(far,(struct sockaddr*)&relative,sizeof(relative))==0&&listen(far,1)==0&&chdir("/")==0);
    a=rt_local_unix_connect_v1(longer,strlen(longer),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+100);assert(dword(a,0)==-1&&!dword(a,1));rt_array_free(a);
    close(far);assert(unlink(longer)==0);
    a=rt_local_unix_connect_v1(path,strlen(path),(int64_t)geteuid()+1,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(dword(a,0)!=0&&!dword(a,1));rt_array_free(a);
    assert(chmod(root,0777)==0);a=rt_local_unix_connect_v1(path,strlen(path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+100);assert(dword(a,0)==-1);rt_array_free(a);assert(chmod(root,0700)==0);
    close(listener);assert(unlink(path)==0);
    /* Owned listener: bind, explicit 0666 mode, same-UID accept refused by the
     * distinct-UID invariant, exact unlink on close. */
    a=rt_local_unix_listen_v1(path,strlen(path),geteuid(),4);assert(dword(a,0)==0&&dword(a,1)>0);
    int64_t owned=dword(a,1);rt_array_free(a);struct stat node;
    assert(lstat(path,&node)==0&&S_ISSOCK(node.st_mode)&&(node.st_mode&0777)==0666);
    a=rt_local_unix_accept_v1(owned,geteuid());assert(dword(a,0)==-1);rt_array_free(a);
    a=rt_local_unix_listener_close_v1(owned);assert(dword(a,0)==0&&dword(a,1)==1);rt_array_free(a);
    assert(lstat(path,&node)!=0&&errno==ENOENT);
    rt_array_free(data);assert(rmdir(root)==0);
    puts("PASS Darwin local Unix bytes/peer(getpeereid+audit token)/path/ancillary/shutdown/close/listener contract; separate-UID accept NOT_RUN");
    return 0;
}
#elif !defined(__linux__)
int main(void){return 77;}
#else
#include <dirent.h>
static int64_t word(SplArray* a,int index){assert(a&&rt_array_len(a)>index);return rt_value_as_int(rt_array_get(a,index));}
static int descriptors(void) {
    DIR* d=opendir("/proc/self/fd");assert(d);int count=0;
    while(readdir(d))count++;assert(closedir(d)==0);return count;
}
static int64_t connect_owner(const char* path,int server,int* peer) {
    SplArray* a=rt_local_unix_connect_v1(path,strlen(path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+500);
    assert(word(a,0)==0&&word(a,1)>0&&word(a,2)==geteuid()&&word(a,4)==getpid());
    int64_t token=word(a,1);rt_array_free(a);*peer=accept4(server,NULL,NULL,SOCK_CLOEXEC|SOCK_NONBLOCK);assert(*peer>=0);return token;
}
static void rights(int peer,int number) {
    int p[2];assert(pipe2(p,O_CLOEXEC)==0);
    union {struct cmsghdr align;unsigned char bytes[CMSG_SPACE(32*sizeof(int))];} control;
    memset(&control,0,sizeof(control));char byte='X';struct iovec io={&byte,1};
    struct msghdr msg={0};msg.msg_iov=&io;msg.msg_iovlen=1;msg.msg_control=control.bytes;msg.msg_controllen=CMSG_SPACE(number*sizeof(int));
    struct cmsghdr* c=CMSG_FIRSTHDR(&msg);c->cmsg_level=SOL_SOCKET;c->cmsg_type=SCM_RIGHTS;c->cmsg_len=CMSG_LEN(number*sizeof(int));
    for(int i=0;i<number;i++)((int*)CMSG_DATA(c))[i]=p[0];
    assert(sendmsg(peer,&msg,MSG_NOSIGNAL)==1);
    /* Receiver measured by caller; originals remain test-owned until afterward. */
    close(p[0]);close(p[1]);
}
static void* drain_after_expiry(void* value) {
    int fd=*(int*)value;struct timespec delay={0,50000000};nanosleep(&delay,NULL);
    unsigned char bytes[65536];
    while(recv(fd,bytes,sizeof(bytes),MSG_DONTWAIT)>0){}
    return NULL;
}
int main(void) {
    alarm(15);char root[]="/tmp/simple-unix-v1-XXXXXX";assert(mkdtemp(root));assert(chmod(root,0700)==0);
    char path[108];assert(snprintf(path,sizeof(path),"%s/socket",root)>0);
    int listener=socket(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC,0);assert(listener>=0);
    struct sockaddr_un address={0};address.sun_family=AF_UNIX;strcpy(address.sun_path,path);
    assert(bind(listener,(struct sockaddr*)&address,sizeof(address))==0&&listen(listener,8)==0);
    int peer=-1;int64_t token=connect_owner(path,listener,&peer);
    SplArray* data=lu_receipt_v1(65536);assert(data);lu_word_v1(data,0,'A');
    SplArray* a=rt_local_unix_write_some_v1(token,data,0,1,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(word(a,0)==0&&word(a,1)==1);rt_array_free(a);char b=0;assert(recv(peer,&b,1,0)==1&&b=='A');
    assert(send(peer,"BC",2,MSG_NOSIGNAL)==2);
    a=rt_local_unix_read_v1(token,16,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(word(a,0)==0&&!word(a,1)&&word(a,2)==2&&word(a,3)=='B'&&word(a,4)=='C');rt_array_free(a);
    a=rt_local_unix_read_v1(token,1,lu_clock_v1(CLOCK_MONOTONIC)+15);assert(word(a,0)==1&&!word(a,1)&&word(a,2)==0);rt_array_free(a);
    a=rt_local_unix_write_some_v1(token,data,-1,1,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==-1);rt_array_free(a);
    a=rt_local_unix_write_some_v1(token,data,65536,1,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==-1);rt_array_free(a);
    a=rt_local_unix_read_v1(token,65537,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==-1);rt_array_free(a);
    a=rt_local_unix_read_v1(token,1,lu_clock_v1(CLOCK_MONOTONIC)+31000);assert(word(a,0)==-1);rt_array_free(a);
    a=rt_local_unix_write_some_admitted_v1(token,data,0,1,lu_clock_v1(CLOCK_MONOTONIC)+100,lu_clock_v1(CLOCK_REALTIME)-1);
    assert(word(a,0)==-8&&word(a,1)==0);rt_array_free(a);
    assert(recv(peer,&b,1,MSG_DONTWAIT)<0&&(errno==EAGAIN||errno==EWOULDBLOCK));
    for(int count=1;count<=32;count+=31) {
        int before=descriptors();rights(peer,count);
        a=rt_local_unix_read_v1(token,16,lu_clock_v1(CLOCK_MONOTONIC)+100);
        assert(word(a,0)==-9&&word(a,2)==1&&word(a,3)=='X');rt_array_free(a);
        assert(descriptors()==before); /* including MSG_CTRUNC, no received FD leaks */
    }
    int status;LuSlotV1* locked=lu_lock_v1(token,&status);assert(locked&&status==0);
    int original_fd=locked->fd;
    assert((fcntl(original_fd,F_GETFD)&FD_CLOEXEC)!=0);
    assert((fcntl(original_fd,F_GETFL)&O_NONBLOCK)!=0);
    int buffer=4096;assert(setsockopt(original_fd,SOL_SOCKET,SO_SNDBUF,&buffer,sizeof(buffer))==0);
    int64_t start=lu_clock_v1(CLOCK_MONOTONIC);
    a=rt_local_unix_close_v1(token);assert(word(a,0)==-7&&!word(a,1));rt_array_free(a);
    a=rt_local_unix_write_some_v1(token,data,0,1,start+100);assert(word(a,0)==-7&&!word(a,1));rt_array_free(a);
    assert(lu_clock_v1(CLOCK_MONOTONIC)-start<100);pthread_mutex_unlock(&locked->operation);
    a=rt_local_unix_write_some_v1(token,data,0,65536,lu_clock_v1(CLOCK_MONOTONIC)+100);
    assert(word(a,0)==0&&word(a,1)>0&&word(a,1)<65536);rt_array_free(a);
    int saturated=0;
    for(int i=0;i<64;i++) {
        a=rt_local_unix_write_some_v1(token,data,0,65536,lu_clock_v1(CLOCK_MONOTONIC)+10);
        if(word(a,0)==1){assert(word(a,1)==0);saturated=1;rt_array_free(a);break;}
        assert(word(a,0)==0&&word(a,1)>0);rt_array_free(a);
    }
    assert(saturated);pthread_t drainer;assert(pthread_create(&drainer,NULL,drain_after_expiry,&peer)==0);
    a=rt_local_unix_write_some_admitted_v1(token,data,0,1,lu_clock_v1(CLOCK_MONOTONIC)+500,lu_clock_v1(CLOCK_REALTIME)+15);
    assert(word(a,0)==-8&&word(a,1)==0);rt_array_free(a);assert(pthread_join(drainer,NULL)==0);
    assert(recv(peer,&b,1,MSG_DONTWAIT)<0&&(errno==EAGAIN||errno==EWOULDBLOCK));
    assert(shutdown(peer,SHUT_WR)==0);
    a=rt_local_unix_read_v1(token,16,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==0&&word(a,1)==1&&word(a,2)==0);rt_array_free(a);
    a=rt_local_unix_close_v1(token);assert(word(a,0)==0&&word(a,1)==1);rt_array_free(a);
    int replacement=open("/dev/null",O_RDONLY|O_CLOEXEC);assert(replacement>=0);
    if(replacement!=original_fd) {
        assert(dup3(replacement,original_fd,O_CLOEXEC)==original_fd);
        close(replacement);replacement=original_fd;
    }
    a=rt_local_unix_close_v1(token);assert(word(a,0)==-2&&!word(a,1));rt_array_free(a);
    assert(fcntl(replacement,F_GETFD)>=0);close(replacement);close(peer);
    int64_t next=connect_owner(path,listener,&peer);assert(next!=token);
    locked=lu_lock_v1(next,&status);assert(locked==&lu_slots_v1[0]);pthread_mutex_unlock(&locked->operation);
    a=rt_local_unix_read_v1(token,1,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==-2);rt_array_free(a);
    a=rt_local_unix_write_some_v1(token,data,0,1,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==-2);rt_array_free(a);
    a=rt_local_unix_close_v1(token);assert(word(a,0)==-2);rt_array_free(a);
    a=rt_local_unix_write_some_v1(next,data,0,1,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==0&&word(a,1)==1);rt_array_free(a);
    assert(recv(peer,&b,1,0)==1&&b=='A');
    a=rt_local_unix_close_v1(next);assert(word(a,1)==1);rt_array_free(a);close(peer);
    char alias[108],alias_socket[108];snprintf(alias,sizeof(alias),"%s/alias",root);assert(symlink(".",alias)==0);
    snprintf(alias_socket,sizeof(alias_socket),"%s/alias/socket",root);
    a=rt_local_unix_connect_v1(alias_socket,strlen(alias_socket),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)!=0&&!word(a,1));rt_array_free(a);assert(unlink(alias)==0);
    char nul[120];size_t size=strlen(path);memcpy(nul,path,size);memcpy(nul+size,"\0suffix",7);
    a=rt_local_unix_connect_v1(nul,(int64_t)size+7,geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==-1);rt_array_free(a);
    a=rt_local_unix_connect_v1(path,strlen(path),(int64_t)geteuid()+1,lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)!=0&&!word(a,1));rt_array_free(a);
    assert(chmod(root,0777)==0);a=rt_local_unix_connect_v1(path,strlen(path),geteuid(),lu_clock_v1(CLOCK_MONOTONIC)+100);assert(word(a,0)==-1);rt_array_free(a);assert(chmod(root,0700)==0);
    /* Saturate the SAME production registry; socketpairs are explicit test
     * ownership, not separately authenticated production connections. */
    int fd_baseline=descriptors(),partners[LUV1_SLOTS];int64_t tokens[LUV1_SLOTS];
    for(int i=0;i<LUV1_SLOTS;i++) {
        int endpoints[2];assert(socketpair(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC|SOCK_NONBLOCK,0,endpoints)==0);
        tokens[i]=lu_install_v1(endpoints[0]);assert(tokens[i]>0);partners[i]=endpoints[1];
    }
    int overflow[2];assert(socketpair(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC,0,overflow)==0);
    assert(lu_install_v1(overflow[0])==-5);close(overflow[0]);close(overflow[1]);
    for(int i=0;i<LUV1_SLOTS;i++) {
        a=rt_local_unix_close_v1(tokens[i]);assert(word(a,0)==0&&word(a,1)==1);rt_array_free(a);close(partners[i]);
    }
    assert(descriptors()==fd_baseline);
    int pair[2];assert(socketpair(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC,0,pair)==0);
    int64_t generation=lu_generation_v1;lu_generation_v1=LUV1_INTEGER_MAX;assert(lu_install_v1(pair[0])==-5);lu_generation_v1=generation;close(pair[0]);close(pair[1]);
    rt_array_free(data);close(listener);assert(unlink(path)==0&&rmdir(root)==0);
    puts("PASS local Unix real socket bytes/peer/path/deadline/ancillary/partial/stale/close contract; separate-UID isolation NOT_RUN");
    return 0;
}
#endif

#endif /* !_WIN32 */
