/* Canonical local Unix byte connection owner. Included by the existing native
 * socket leaf; no raw descriptors cross the public ABI. Linux only. */
#include "runtime.h"
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#if defined(__linux__)
#include <unistd.h>
#include <pthread.h>
#include <poll.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/stat.h>
#include <time.h>
#include <stdatomic.h>

_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "local Unix origin guard requires lock-free unsigned int atomics");
_Static_assert(sizeof(pid_t) <= sizeof(unsigned int), "local Unix origin PID must fit unsigned int");
static atomic_uint lu_process_origin_v1;
static atomic_uint lu_process_origin_ready_v1;
/* Immutable after release publication; ready acquire protects both plain fields. */
static dev_t lu_origin_namespace_device_v1;
static ino_t lu_origin_namespace_inode_v1;
static int lu_namespace_v1(struct stat* observed) {
    return stat("/proc/self/ns/pid",observed)==0;
}
/* Observe real PID+namespace before any owner lock/allocation. A virgin winner
 * publishes an immutable pair. Other threads/processes never wait for an
 * incomplete publication and never reset/reconstruct inherited registry state. */
static int lu_origin_v1(void) {
    struct stat namespace_identity;
    pid_t observed=getpid();
    if(observed<=0||!lu_namespace_v1(&namespace_identity))return 0;
    unsigned int pid=(unsigned int)observed;
    unsigned int origin=atomic_load_explicit(&lu_process_origin_v1,memory_order_acquire);
    if(origin==0) {
        unsigned int expected=0;
        if(atomic_compare_exchange_strong_explicit(&lu_process_origin_v1,&expected,pid,
                memory_order_acq_rel,memory_order_acquire)) {
            lu_origin_namespace_device_v1=namespace_identity.st_dev;
            lu_origin_namespace_inode_v1=namespace_identity.st_ino;
            atomic_store_explicit(&lu_process_origin_ready_v1,1,memory_order_release);
        }
    }
    if(atomic_load_explicit(&lu_process_origin_ready_v1,memory_order_acquire)!=1)return 0;
    origin=atomic_load_explicit(&lu_process_origin_v1,memory_order_acquire);
    return origin==pid&&lu_origin_namespace_device_v1==namespace_identity.st_dev&&
        lu_origin_namespace_inode_v1==namespace_identity.st_ino;
}

#define LUV1_SLOTS 64
/* CoreC signed immediate range: receipt words must never allocate after I/O. */
#define LUV1_INTEGER_MAX INT64_C(1152921504606846975)
#define LUV1_BYTES 65536
#define LUV1_HORIZON 30000
/* status: 0 success,1 timeout,-1 invalid,-2 stale,-3 syscall,-4 unsupported,
 * -5 capacity,-6 allocation,-7 concurrent operation busy,-8 admission expired,
 * -9 ancillary rejected. Private gates use -10 for foreign origin; public
 * array-returning entries refuse foreign origin with allocation-free NULL. */
typedef struct LuSlotV1 { pthread_mutex_t operation; int64_t token; int fd; int active; } LuSlotV1;
static LuSlotV1 lu_slots_v1[LUV1_SLOTS];
static pthread_mutex_t lu_registry_v1=PTHREAD_MUTEX_INITIALIZER;
static pthread_once_t lu_once_v1=PTHREAD_ONCE_INIT;
static int64_t lu_generation_v1=0;
static int lu_initialized_v1=0;
static void lu_init_v1(void) {
    if(!lu_origin_v1())return;
    for(int i=0;i<LUV1_SLOTS;i++) {
        lu_slots_v1[i].fd=-1;
        if(pthread_mutex_init(&lu_slots_v1[i].operation,NULL)!=0)return;
    }
    lu_initialized_v1=1;
}
static int64_t lu_clock_v1(clockid_t clock) {
    struct timespec t;
    if(clock_gettime(clock,&t)||t.tv_sec<0||t.tv_nsec<0||t.tv_nsec>=1000000000L||
       (uint64_t)t.tv_sec>((uint64_t)INT64_MAX-999U)/1000U)return -1;
    return (int64_t)t.tv_sec*1000+t.tv_nsec/1000000;
}
static int lu_deadline_v1(int64_t deadline) {
    int64_t now=lu_clock_v1(CLOCK_MONOTONIC);
    if(now<0)return -3;
    if(deadline<=now)return 1;
    return deadline-now>LUV1_HORIZON?-1:0;
}
static int lu_poll_v1(int fd,short events,int64_t deadline) {
    for(;;) {
        int64_t now=lu_clock_v1(CLOCK_MONOTONIC);
        if(now<0)return -3;
        if(now>=deadline)return 1;
        struct pollfd p={.fd=fd,.events=events};
        int rc=poll(&p,1,(int)(deadline-now));
        if(rc>0)return p.revents&POLLNVAL?-3:0;
        if(rc==0)return 1;
        if(errno!=EINTR)return -3;
    }
}
static LuSlotV1* lu_lock_v1(int64_t token,int* status) {
    *status=-2;
    if(!lu_origin_v1()){*status=-10;return NULL;}
    if(token<=0){*status=-1;return NULL;}
    if(pthread_once(&lu_once_v1,lu_init_v1)||!lu_initialized_v1){*status=-3;return NULL;}
    if(pthread_mutex_lock(&lu_registry_v1)){*status=-3;return NULL;}
    LuSlotV1* result=NULL;
    for(int i=0;i<LUV1_SLOTS;i++)if(lu_slots_v1[i].active&&lu_slots_v1[i].token==token) {
        int rc=pthread_mutex_trylock(&lu_slots_v1[i].operation);
        if(rc==0){result=&lu_slots_v1[i];*status=0;}else *status=rc==EBUSY?-7:-3;
        break;
    }
    pthread_mutex_unlock(&lu_registry_v1);return result;
}
static int64_t lu_install_v1(int fd) {
    if(!lu_origin_v1())return -10;
    if(pthread_once(&lu_once_v1,lu_init_v1)||!lu_initialized_v1)return -3;
    if(pthread_mutex_lock(&lu_registry_v1))return -3;
    int64_t token=-5;
    if(lu_generation_v1<LUV1_INTEGER_MAX)for(int i=0;i<LUV1_SLOTS;i++) {
        LuSlotV1* s=&lu_slots_v1[i];
        if(!s->active&&pthread_mutex_trylock(&s->operation)==0) {
            s->token=++lu_generation_v1;s->fd=fd;s->active=1;token=s->token;
            pthread_mutex_unlock(&s->operation);break;
        }
    }
    pthread_mutex_unlock(&lu_registry_v1);return token;
}
static int lu_directory_v1(int fd,uid_t expected,int final) {
    struct stat s;
    if(fstat(fd,&s)||!S_ISDIR(s.st_mode)||(s.st_uid!=0&&s.st_uid!=expected))return 0;
    if(!(s.st_mode&0022))return 1;
    return !final&&s.st_uid==0&&(s.st_mode&S_ISVTX);
}
/* Counted bytes, real no-follow ancestors, retained final parent. No mkdir or
 * mode change. Root-sticky ancestors are allowed only before final parent. */
static int lu_parent_v1(const char* input,int64_t bytes,uid_t expected,char leaf[108]) {
    if(!input||bytes<2||bytes>4095||input[0]!='/'||memchr(input,0,(size_t)bytes))return -1;
    char path[4096];memcpy(path,input,(size_t)bytes);path[bytes]=0;
    int fd=open("/",O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);
    if(fd<0)return -1;
    const char* at=path+1;
    while(*at) {
        const char* slash=strchr(at,'/');size_t n=slash?(size_t)(slash-at):strlen(at);
        if(!n||n>255||(!slash&&n>=108)||(n==1&&at[0]=='.')||(n==2&&at[0]=='.'&&at[1]=='.'))goto bad;
        if(!lu_directory_v1(fd,expected,slash==NULL))goto bad;
        char part[256];memcpy(part,at,n);part[n]=0;
        if(!slash){memcpy(leaf,part,n+1);return fd;}
        int next=openat(fd,part,O_RDONLY|O_DIRECTORY|O_CLOEXEC|O_NOFOLLOW);
        if(next<0)goto bad;
        close(fd);fd=next;at=slash+1;
    }
bad: close(fd);return -1;
}
#endif

static SplArray* lu_receipt_v1(int64_t count) {
    SplArray* a=rt_array_new(count);
    if(!a)return NULL;
    for(int64_t i=0;i<count;i++)if(!rt_array_push(a,rt_value_int(0))){rt_array_free(a);return NULL;}
    return a;
}
static void lu_word_v1(SplArray* a,int64_t index,int64_t value) {
    (void)rt_array_set(a,index,rt_value_int(value)); /* existing reserved index */
}
/* Foreign-process refusal is NULL before ANY generic runtime allocation,
 * receipt decoding or owner gate. Caller must use a nullable-array ABI. */
static SplArray* lu_connect_impl_v1(const char* path,int64_t bytes,int64_t expected_uid,int64_t deadline) {
#if defined(__linux__)
    if(!lu_origin_v1())return NULL;
#endif
    SplArray* answer=lu_receipt_v1(7);if(!answer)return NULL;
#if defined(__linux__)
    int status=expected_uid<0||expected_uid>UINT32_MAX?-1:lu_deadline_v1(deadline);
    int directory=-1,fd=-1;char leaf[108];struct stat before,after;
    if(status)goto done;
    directory=lu_parent_v1(path,bytes,(uid_t)expected_uid,leaf);
    if(directory<0){status=-1;goto done;}
    if(fstatat(directory,leaf,&before,AT_SYMLINK_NOFOLLOW)||!S_ISSOCK(before.st_mode)||
       before.st_uid!=(uid_t)expected_uid||(uint64_t)before.st_dev>LUV1_INTEGER_MAX||(uint64_t)before.st_ino>LUV1_INTEGER_MAX){status=-1;goto done;}
    struct sockaddr_un address;memset(&address,0,sizeof(address));address.sun_family=AF_UNIX;
    int n=snprintf(address.sun_path,sizeof(address.sun_path),"/proc/self/fd/%d/%s",directory,leaf);
    if(n<0||(size_t)n>=sizeof(address.sun_path)){status=-1;goto done;}
    fd=socket(AF_UNIX,SOCK_STREAM|SOCK_CLOEXEC|SOCK_NONBLOCK,0);
    if(fd<0){status=-3;goto done;}
    for(;;) {
        status=lu_deadline_v1(deadline);if(status)goto done;
        int rc=connect(fd,(struct sockaddr*)&address,sizeof(address));
        if(rc==0)break;
        if(errno==EISCONN)break;
        if(errno==EINTR)continue;
        /* AF_UNIX EAGAIN is backlog saturation, not an in-progress connect.
         * Do not treat SO_ERROR==0 on that unconnected fd as success or spin. */
        if(errno==EAGAIN){status=-7;goto done;}
        if(errno!=EINPROGRESS&&errno!=EALREADY){status=-3;goto done;}
        status=lu_poll_v1(fd,POLLOUT,deadline);if(status)goto done;
        int error=0;socklen_t size=sizeof(error);
        if(getsockopt(fd,SOL_SOCKET,SO_ERROR,&error,&size)||size!=sizeof(error)||error){status=-3;goto done;}
        break;
    }
    struct ucred peer;socklen_t peer_size=sizeof(peer);memset(&peer,0,sizeof(peer));
    if(getsockopt(fd,SOL_SOCKET,SO_PEERCRED,&peer,&peer_size)||peer_size!=sizeof(peer)||peer.uid!=(uid_t)expected_uid||peer.pid<=0||
       fstatat(directory,leaf,&after,AT_SYMLINK_NOFOLLOW)||!S_ISSOCK(after.st_mode)||after.st_uid!=(uid_t)expected_uid||
       before.st_dev!=after.st_dev||before.st_ino!=after.st_ino){status=-3;goto done;}
    int64_t token=lu_install_v1(fd);
    if(token<=0){status=(int)token;goto done;}
    fd=-1;lu_word_v1(answer,1,token);lu_word_v1(answer,2,peer.uid);lu_word_v1(answer,3,peer.gid);
    lu_word_v1(answer,4,peer.pid);lu_word_v1(answer,5,(int64_t)before.st_dev);lu_word_v1(answer,6,(int64_t)before.st_ino);
done:
    if(fd>=0)(void)close(fd);
    if(directory>=0)(void)close(directory);
    lu_word_v1(answer,0,status);
#else
    (void)path;(void)bytes;(void)expected_uid;(void)deadline;lu_word_v1(answer,0,-4);
#endif
    return answer;
}
static SplArray* lu_read_impl_v1(int64_t token,int64_t maximum,int64_t deadline) {
#if defined(__linux__)
    if(!lu_origin_v1())return NULL;
#endif
    int valid=maximum>0&&maximum<=65536;
    SplArray* answer=lu_receipt_v1(valid?maximum+3:3);if(!answer)return NULL;
#if defined(__linux__)
    int status=valid?lu_deadline_v1(deadline):-1;LuSlotV1* slot=NULL;unsigned char* data=NULL;
    if(status)goto done;
    data=malloc((size_t)maximum);if(!data){status=-6;goto done;}
    slot=lu_lock_v1(token,&status);if(!slot)goto done;
    for(;;) {
        status=lu_deadline_v1(deadline);if(status)break;
        union { struct cmsghdr alignment; unsigned char bytes[CMSG_SPACE(16*sizeof(int))]; } control;
        struct iovec io={.iov_base=data,.iov_len=(size_t)maximum};
        struct msghdr message;memset(&message,0,sizeof(message));
        memset(&control,0,sizeof(control));message.msg_iov=&io;message.msg_iovlen=1;
        message.msg_control=control.bytes;message.msg_controllen=sizeof(control.bytes);
        ssize_t n=recvmsg(slot->fd,&message,MSG_CMSG_CLOEXEC);
        if(n>=0) {
            int ancillary=message.msg_controllen>0||(message.msg_flags&(MSG_CTRUNC|MSG_TRUNC));
            /* Generic bytes never import rights. Close every delivered fd even
             * on control truncation; Linux closes excess undisclosed rights. */
            for(struct cmsghdr* c=CMSG_FIRSTHDR(&message);c;c=CMSG_NXTHDR(&message,c)) {
                if(c->cmsg_len<CMSG_LEN(0)){ancillary=1;break;}
                if(c->cmsg_level==SOL_SOCKET&&c->cmsg_type==SCM_RIGHTS) {
                    size_t count=(c->cmsg_len-CMSG_LEN(0))/sizeof(int);
                    int* descriptors=(int*)CMSG_DATA(c);
                    for(size_t i=0;i<count;i++)if(descriptors[i]>=0)(void)close(descriptors[i]);
                }
            }
            lu_word_v1(answer,1,n==0);lu_word_v1(answer,2,n);
            for(ssize_t i=0;i<n;i++)lu_word_v1(answer,i+3,data[i]);
            if(ancillary)status=-9; /* payload remains reported, no retry */
            break;
        }
        if(errno==EINTR)continue;
        if(errno!=EAGAIN&&errno!=EWOULDBLOCK){status=-3;break;}
        status=lu_poll_v1(slot->fd,POLLIN,deadline);if(status)break;
    }
done:
    if(slot)pthread_mutex_unlock(&slot->operation);
    free(data);lu_word_v1(answer,0,status);
#else
    (void)token;(void)deadline;lu_word_v1(answer,0,valid?-4:-1);
#endif
    return answer;
}
static SplArray* lu_write_v1(int64_t token,SplArray* bytes,int64_t offset,int64_t maximum,
        int64_t deadline,int admitted,int64_t expiry) {
#if defined(__linux__)
    if(!lu_origin_v1())return NULL;
#endif
    SplArray* answer=lu_receipt_v1(2);if(!answer)return NULL;
#if defined(__linux__)
    int64_t length=bytes?rt_array_len(bytes):-1;
    int status=length<0||offset<0||offset>length||maximum<=0||maximum>LUV1_BYTES||maximum>length-offset||
        (admitted&&expiry<=0)?-1:lu_deadline_v1(deadline);
    unsigned char* data=NULL;LuSlotV1* slot=NULL;
    if(status)goto done;
    data=malloc((size_t)maximum);if(!data){status=-6;goto done;}
    for(int64_t i=0;i<maximum;i++) {
        int64_t value=rt_array_get(bytes,offset+i);
        if(!rt_value_is_int(value)||rt_value_as_int(value)<0||rt_value_as_int(value)>255){status=-1;goto done;}
        data[i]=(unsigned char)rt_value_as_int(value);
    }
    slot=lu_lock_v1(token,&status);if(!slot)goto done;
    for(;;) {
        status=lu_deadline_v1(deadline);if(status)break;
        if(admitted) {
            int64_t now=lu_clock_v1(CLOCK_REALTIME);
            if(now<0){status=-3;break;}
            if(now>=expiry){status=-8;break;}
        }
        /* MSG_NOSIGNAL: a closed peer returns an error, never process SIGPIPE. */
        ssize_t n=send(slot->fd,data,(size_t)maximum,MSG_NOSIGNAL);
        if(n>=0){lu_word_v1(answer,1,n);break;}
        if(errno==EINTR)continue;
        if(errno!=EAGAIN&&errno!=EWOULDBLOCK){status=-3;break;}
        status=lu_poll_v1(slot->fd,POLLOUT,deadline);if(status)break;
    }
done:
    if(slot)pthread_mutex_unlock(&slot->operation);
    free(data);lu_word_v1(answer,0,status);
#else
    (void)token;(void)bytes;(void)offset;(void)maximum;(void)deadline;(void)admitted;(void)expiry;
    lu_word_v1(answer,0,-4);
#endif
    return answer;
}
static SplArray* lu_close_impl_v1(int64_t token) {
#if defined(__linux__)
    if(!lu_origin_v1())return NULL;
#endif
    SplArray* answer=lu_receipt_v1(2);if(!answer)return NULL;
#if defined(__linux__)
    int status;LuSlotV1* slot=lu_lock_v1(token,&status);
    if(slot) {
        int fd=slot->fd;
        /* On Linux close consumes the fd even when reporting an error. Retire
         * exact generation and NEVER retry that integer after kernel reuse. */
        int rc=close(fd);status=rc==0?0:-3;
        pthread_mutex_lock(&lu_registry_v1);
        slot->active=0;slot->fd=-1;
        pthread_mutex_unlock(&lu_registry_v1);
        lu_word_v1(answer,1,1);pthread_mutex_unlock(&slot->operation);
    }
    lu_word_v1(answer,0,status);
#else
    (void)token;lu_word_v1(answer,0,-4);
#endif
    return answer;
}
