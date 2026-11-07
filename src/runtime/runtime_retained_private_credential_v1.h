#ifndef SIMPLE_RETAINED_PRIVATE_CREDENTIAL_V1_H
#define SIMPLE_RETAINED_PRIVATE_CREDENTIAL_V1_H
/* Opaque process-local tokens, never descriptors. No path-write fallback. */
#include <stdint.h>
int64_t rt_retained_private_credential_open_v1(int64_t, int64_t);
int64_t rt_retained_private_credential_state_v1(int64_t);
int64_t rt_retained_private_credential_error_v1(int64_t);
int64_t rt_retained_private_credential_read_v1(int64_t, int64_t, int64_t);
int64_t rt_retained_private_credential_publish_v1(int64_t, int64_t, int64_t, int64_t, int64_t);
int64_t rt_retained_private_credential_close_v1(int64_t);
#ifdef SIMPLE_RETAINED_PRIVATE_CREDENTIAL_IMPLEMENTATION
#if defined(__linux__)
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/syscall.h>
#include <sys/random.h>
#include <unistd.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdatomic.h>
#include <errno.h>
#include <string.h>
#include <limits.h>
#ifndef RENAME_NOREPLACE
#define RENAME_NOREPLACE 1
#endif
enum { RPC_OPEN=1, RPC_PUBLISHED=2, RPC_UNCERTAIN=3, RPC_CLOSED=4 };
enum { RPC_ARGUMENT=-2, RPC_FULL=-3, RPC_EXHAUSTED=-4, RPC_STALE=-5,
    RPC_FORK=-6, RPC_PATH=-7, RPC_METADATA=-8, RPC_IO=-9, RPC_CHANGED=-10,
    RPC_CONFLICT=-11, RPC_STATE=-12, RPC_PUBLICATION=-13, RPC_CONSUMED=-14,
    RPC_ENTROPY=-15, RPC_NOREPLACE=-16, RPC_READY=-17 };
typedef struct {
    int64_t token, phase, error;
    int directory, initial, temporary, close_attempted;
    char leaf[250], ready[256], temporary_name[64];
    struct stat identity, temporary_identity;
    uint8_t bytes[512];
    size_t length;
} SimplePrivateCredentialV1;
static SimplePrivateCredentialV1 simple_private_credentials_v1[32];
static pthread_mutex_t simple_private_credentials_lock_v1=PTHREAD_MUTEX_INITIALIZER;
/* Publication must not inherit a hidden atomic-library mutex after fork. */
_Static_assert(ATOMIC_INT_LOCK_FREE==2,"private credential origin phase must be lock-free");
static atomic_int simple_private_credentials_origin_phase_v1=0;
static pid_t simple_private_credentials_origin_pid_v1;
static dev_t simple_private_credentials_origin_device_v1;
static ino_t simple_private_credentials_origin_inode_v1;
static int64_t simple_private_credentials_next_v1=1;
static int rpc_lock_v1(void) {
    int phase=atomic_load_explicit(&simple_private_credentials_origin_phase_v1,memory_order_acquire);
    if (phase==0) {
        int expected=0;
        if (atomic_compare_exchange_strong_explicit(&simple_private_credentials_origin_phase_v1,
                &expected,1,memory_order_acq_rel,memory_order_acquire)) {
            struct stat origin;
            /* Failure leaves Initializing permanently: never reset/adopt. */
            if (stat("/proc/self/ns/pid",&origin)!=0) return RPC_IO;
            simple_private_credentials_origin_pid_v1=getpid();
            simple_private_credentials_origin_device_v1=origin.st_dev;
            simple_private_credentials_origin_inode_v1=origin.st_ino;
            atomic_store_explicit(&simple_private_credentials_origin_phase_v1,2,memory_order_release);
            phase=2;
        } else phase=expected;
    }
    /* Transient initialization, including an inherited Initializing snapshot,
     * refuses without spinning, touching registry state or locking a mutex. */
    if (phase!=2) return RPC_STATE;
    struct stat current;
    if (stat("/proc/self/ns/pid",&current)!=0) {
        atomic_store_explicit(&simple_private_credentials_origin_phase_v1,3,memory_order_release);
        return RPC_IO;
    }
    if (getpid()!=simple_private_credentials_origin_pid_v1 ||
        current.st_dev!=simple_private_credentials_origin_device_v1 ||
        current.st_ino!=simple_private_credentials_origin_inode_v1) {
        atomic_store_explicit(&simple_private_credentials_origin_phase_v1,3,memory_order_release);
        return RPC_FORK;
    }
    if (atomic_load_explicit(&simple_private_credentials_origin_phase_v1,memory_order_acquire)!=2) return RPC_STATE;
    if (pthread_mutex_lock(&simple_private_credentials_lock_v1)!=0) return RPC_IO;
    if (atomic_load_explicit(&simple_private_credentials_origin_phase_v1,memory_order_acquire)!=2) {
        /* This invocation acquired the mutex: use only its ordinary matched
         * unlock, with no new origin syscall/recheck, before refusing access. */
        pthread_mutex_unlock(&simple_private_credentials_lock_v1);
        return RPC_STATE;
    }
    return 0;
}
static SimplePrivateCredentialV1 *rpc_find_v1(int64_t token) {
    if (token<=0) return NULL;
    for (int i=0;i<32;i++) if (simple_private_credentials_v1[i].token==token) return &simple_private_credentials_v1[i];
    return NULL;
}
static int rpc_component_v1(const char *name,size_t n) {
    if (!n || n>249 || (n==1 && name[0]=='.') || (n==2 && name[0]=='.' && name[1]=='.')) return 0;
    for (size_t i=0;i<n;i++) {
        unsigned char c=(unsigned char)name[i];
        if (!((c>='a'&&c<='z')||(c>='A'&&c<='Z')||(c>='0'&&c<='9')||c=='_'||c=='-'||c=='.')) return 0;
    }
    return 1;
}
static int rpc_directory_v1(int fd,int final) {
    struct stat s;
    if (fstat(fd,&s)!=0 || !S_ISDIR(s.st_mode)) return 0;
    uid_t uid=geteuid();
    if (final) return s.st_uid==uid && (s.st_mode&07777)==0700;
    if (s.st_uid!=0 && s.st_uid!=uid) return 0;
    return !(s.st_mode&0022) || (s.st_uid==0 && (s.st_mode&S_ISVTX));
}
static int rpc_regular_v1(const struct stat *s) {
    return S_ISREG(s->st_mode) && s->st_uid==geteuid() && (s->st_mode&07777)==0600 &&
        s->st_nlink==1 && s->st_size>0 && s->st_size<=512;
}
static int rpc_same_v1(const struct stat *a,const struct stat *b) {
    return a->st_dev==b->st_dev && a->st_ino==b->st_ino && a->st_size==b->st_size &&
        a->st_uid==b->st_uid && a->st_mode==b->st_mode && a->st_nlink==b->st_nlink &&
        a->st_mtim.tv_sec==b->st_mtim.tv_sec && a->st_mtim.tv_nsec==b->st_mtim.tv_nsec &&
        a->st_ctim.tv_sec==b->st_ctim.tv_sec && a->st_ctim.tv_nsec==b->st_ctim.tv_nsec;
}
static int rpc_read_v1(int fd,uint8_t *bytes,size_t n) {
    size_t at=0; int interrupted=0;
    while (at<n) {
        ssize_t got=pread(fd,bytes+at,n-at,(off_t)at);
        if (got<0 && errno==EINTR && interrupted++<8) continue;
        if (got<=0) return 0;
        at+=(size_t)got;
    }
    return 1;
}
static int rpc_initial_v1(SimplePrivateCredentialV1 *o) {
    struct stat fd,path,after; uint8_t bytes[512];
    if (fstat(o->initial,&fd)!=0 || !rpc_regular_v1(&fd) || !rpc_same_v1(&fd,&o->identity) ||
        fstatat(o->directory,o->leaf,&path,AT_SYMLINK_NOFOLLOW)!=0 || !rpc_same_v1(&fd,&path) ||
        !rpc_read_v1(o->initial,bytes,o->length) || memcmp(bytes,o->bytes,o->length)!=0 ||
        fstat(o->initial,&after)!=0 || !rpc_same_v1(&fd,&after)) return 0;
    return rpc_directory_v1(o->directory,1);
}
static int rpc_hex_v1(const uint8_t *s,size_t n) {
    for (size_t i=0;i<n;i++) if (!((s[i]>='0'&&s[i]<='9')||(s[i]>='a'&&s[i]<='f'))) return 0;
    return 1;
}
static int rpc_initial_layout_v1(const uint8_t *s,size_t n,size_t *token_length) {
    if (n && s[n-1]=='\n') n--;
    if (n<34 || n>161 || s[32]!=' ' || !rpc_hex_v1(s,32)) return 0;
    for (size_t i=33;i<n;i++) if (s[i]<33 || s[i]>126) return 0;
    *token_length=n-33; return 1;
}
static int rpc_ready_layout_v1(SimplePrivateCredentialV1 *o,const uint8_t *s,size_t n) {
    size_t initial_token=0,begin[5],length[5],field=0,start=0;
    if (!rpc_initial_layout_v1(o->bytes,o->length,&initial_token) || n<1 || n>512 || s[n-1]!='\n') return 0;
    for (size_t i=0;i<n-1;i++) {
        if (s[i]<32 || s[i]>126) return 0;
        if (s[i]==' ') {
            if (field>=4 || i==start) return 0;
            begin[field]=start; length[field++]=i-start; start=i+1;
        }
    }
    if (field!=4 || start==n-1) return 0;
    begin[4]=start; length[4]=n-1-start;
    if (length[0]!=32 || memcmp(s,o->bytes,32)!=0 || length[2]!=initial_token ||
        memcmp(s+begin[2],o->bytes+33,initial_token)!=0 || length[4]!=32 || !rpc_hex_v1(s+begin[4],32)) return 0;
    if (length[1]<11 || length[1]>15 || memcmp(s+begin[1],"127.0.0.1:",10)!=0) return 0;
    uint64_t port=0,pid=0;
    for (size_t i=10;i<length[1];i++) {
        uint8_t c=s[begin[1]+i]; if (c<'0'||c>'9'||(i==10&&c=='0')) return 0;
        port=port*10+(c-'0');
    }
    if (!port || port>65535 || !length[3] || length[3]>19) return 0;
    for (size_t i=0;i<length[3];i++) {
        uint8_t c=s[begin[3]+i]; if (c<'0'||c>'9'||(i==0&&c=='0')) return 0;
        if (pid>((uint64_t)INT64_MAX-(c-'0'))/10) return 0;
        pid=pid*10+(c-'0');
    }
    return pid>0;
}
static int rpc_random_v1(uint8_t *bytes,size_t n) {
#ifdef SYS_getrandom
    size_t at=0; int turns=0;
    while (at<n && turns++<16) {
        ssize_t count=(ssize_t)syscall(SYS_getrandom,bytes+at,n-at,GRND_NONBLOCK);
        if (count<0 && errno==EINTR) continue;
        if (count<=0) return 0;
        at+=(size_t)count;
    }
    return at==n;
#else
    (void)bytes; (void)n; return 0;
#endif
}
int64_t rt_retained_private_credential_open_v1(int64_t address,int64_t length) {
    if (!address || length<2 || length>4095) return RPC_ARGUMENT;
    char path[4096]; memcpy(path,(const void *)(intptr_t)address,(size_t)length); path[length]=0;
    if (path[0]!='/' || memchr(path,0,(size_t)length)) return RPC_PATH;
    char *leaf=path+1; int components=0;
    for (char *p=path+1;;p++) if (*p=='/' || !*p) {
        if (!rpc_component_v1(leaf,(size_t)(p-leaf)) || ++components>128) return RPC_PATH;
        if (!*p) break;
        leaf=p+1;
    }
    size_t leaf_length=strlen(leaf);
    if (leaf_length>=6 && !strcmp(leaf+leaf_length-6,".ready")) return RPC_PATH;
    int locked=rpc_lock_v1(); if (locked) return locked;
    SimplePrivateCredentialV1 *o=NULL;
    for (int i=0;i<32;i++) if (!simple_private_credentials_v1[i].token || simple_private_credentials_v1[i].phase==RPC_CLOSED) { o=&simple_private_credentials_v1[i]; break; }
    if (!o) { pthread_mutex_unlock(&simple_private_credentials_lock_v1); return RPC_FULL; }
    if (simple_private_credentials_next_v1==INT64_MAX) { pthread_mutex_unlock(&simple_private_credentials_lock_v1); return RPC_EXHAUSTED; }
    memset(o,0,sizeof(*o)); o->token=simple_private_credentials_next_v1++; o->phase=RPC_UNCERTAIN;
    o->directory=o->initial=o->temporary=-1; o->error=RPC_IO;
    memcpy(o->leaf,leaf,leaf_length+1); memcpy(o->ready,leaf,leaf_length); memcpy(o->ready+leaf_length,".ready",7);
    o->directory=open("/",O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
    if (o->directory<0 || !rpc_directory_v1(o->directory,0)) goto done;
    char *component=path+1;
    while (component!=leaf) {
        char *slash=strchr(component,'/'); *slash=0;
        int next=openat(o->directory,component,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);
        if (next<0) { o->error=RPC_PATH; goto done; }
        int old=o->directory; o->directory=next;
        if (close(old)!=0) { o->error=RPC_CONSUMED; goto done; }
        if (!rpc_directory_v1(next,0)) { o->error=RPC_METADATA; goto done; }
        component=slash+1;
    }
    if (!rpc_directory_v1(o->directory,1)) { o->error=RPC_METADATA; goto done; }
    o->initial=openat(o->directory,o->leaf,O_RDONLY|O_NONBLOCK|O_NOFOLLOW|O_CLOEXEC);
    if (o->initial<0) { o->error=RPC_PATH; goto done; }
    if (fstat(o->initial,&o->identity)!=0 || !rpc_regular_v1(&o->identity)) { o->error=RPC_METADATA; goto done; }
    o->length=(size_t)o->identity.st_size;
    size_t token_length=0;
    if (!rpc_read_v1(o->initial,o->bytes,o->length) || !rpc_initial_layout_v1(o->bytes,o->length,&token_length) || !rpc_initial_v1(o)) { o->error=RPC_CHANGED; goto done; }
    o->phase=RPC_OPEN; o->error=0;
done:;
    int64_t token=o->token; pthread_mutex_unlock(&simple_private_credentials_lock_v1); return token;
}
int64_t rt_retained_private_credential_state_v1(int64_t token) {
    int locked=rpc_lock_v1(); if (locked) return locked;
    SimplePrivateCredentialV1 *o=rpc_find_v1(token); int64_t result=o?o->phase:RPC_STALE;
    pthread_mutex_unlock(&simple_private_credentials_lock_v1); return result;
}
int64_t rt_retained_private_credential_error_v1(int64_t token) {
    int locked=rpc_lock_v1(); if (locked) return locked;
    SimplePrivateCredentialV1 *o=rpc_find_v1(token); int64_t result=o?o->error:RPC_STALE;
    pthread_mutex_unlock(&simple_private_credentials_lock_v1); return result;
}
int64_t rt_retained_private_credential_read_v1(int64_t token,int64_t address,int64_t capacity) {
    if (!address || capacity<512) return RPC_ARGUMENT;
    int locked=rpc_lock_v1(); if (locked) return locked;
    SimplePrivateCredentialV1 *o=rpc_find_v1(token); int64_t result=RPC_STALE;
    if (o) {
        if (o->phase!=RPC_OPEN && o->phase!=RPC_PUBLISHED) result=RPC_STATE;
        else if (!rpc_initial_v1(o)) { o->phase=RPC_UNCERTAIN; o->error=RPC_CHANGED; result=RPC_CHANGED; }
        else { memcpy((void *)(intptr_t)address,o->bytes,o->length); result=(int64_t)o->length; }
    }
    pthread_mutex_unlock(&simple_private_credentials_lock_v1); return result;
}
int64_t rt_retained_private_credential_publish_v1(int64_t token,int64_t initial,int64_t initial_length,int64_t ready,int64_t ready_length) {
    int locked=rpc_lock_v1(); if (locked) return locked;
    SimplePrivateCredentialV1 *o=rpc_find_v1(token); int64_t result=RPC_STALE;
    if (!o) goto end;
    if (o->phase!=RPC_OPEN) { result=RPC_STATE; goto end; }
    o->phase=RPC_UNCERTAIN;
    if (!initial || !ready || initial_length<1 || initial_length>512 || ready_length<1 || ready_length>512) { result=RPC_ARGUMENT; goto failed; }
    uint8_t expected_bytes[512],ready_bytes[512];
    memcpy(expected_bytes,(const void *)(intptr_t)initial,(size_t)initial_length);
    memcpy(ready_bytes,(const void *)(intptr_t)ready,(size_t)ready_length);
    if ((size_t)initial_length!=o->length || memcmp(o->bytes,expected_bytes,o->length)!=0 || !rpc_initial_v1(o)) { result=RPC_CHANGED; goto failed; }
    const uint8_t *bytes=ready_bytes;
    if (!rpc_ready_layout_v1(o,bytes,(size_t)ready_length)) { result=RPC_READY; goto failed; }
    uint8_t random[16]; const char hex[]="0123456789abcdef";
    if (!rpc_random_v1(random,sizeof(random))) { result=RPC_ENTROPY; goto failed; }
    memcpy(o->temporary_name,".credential-",12);
    for (int i=0;i<16;i++) { o->temporary_name[12+i*2]=hex[random[i]>>4]; o->temporary_name[13+i*2]=hex[random[i]&15]; }
    o->temporary_name[44]=0;
    o->temporary=openat(o->directory,o->temporary_name,O_RDWR|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC,0600);
    if (o->temporary<0) { o->temporary_name[0]=0; result=RPC_IO; goto failed; }
    if (fchmod(o->temporary,0600)!=0 || fstat(o->temporary,&o->temporary_identity)!=0) { result=RPC_IO; goto failed; }
    size_t at=0; int interrupted=0;
    while (at<(size_t)ready_length) {
        ssize_t count=write(o->temporary,bytes+at,(size_t)ready_length-at);
        if (count<0 && errno==EINTR && interrupted++<8) continue;
        if (count<=0) { result=RPC_IO; goto failed; }
        at+=(size_t)count;
    }
    if (fsync(o->temporary)!=0 || fstat(o->temporary,&o->temporary_identity)!=0 || !rpc_regular_v1(&o->temporary_identity)) { result=RPC_IO; goto failed; }
#ifdef SYS_renameat2
    if (syscall(SYS_renameat2,o->directory,o->temporary_name,o->directory,o->ready,RENAME_NOREPLACE)!=0) {
        result=errno==EEXIST?RPC_CONFLICT:((errno==ENOSYS||errno==EINVAL)?RPC_NOREPLACE:RPC_PUBLICATION); goto failed;
    }
#else
    result=RPC_NOREPLACE; goto failed;
#endif
    o->temporary_name[0]=0;
    if (fsync(o->directory)!=0 || fstat(o->temporary,&o->temporary_identity)!=0) { result=RPC_PUBLICATION; goto failed; }
    struct stat final,after,named; uint8_t final_bytes[512];
    int fd=openat(o->directory,o->ready,O_RDONLY|O_NONBLOCK|O_NOFOLLOW|O_CLOEXEC);
    if (fd<0) { result=RPC_PUBLICATION; goto failed; }
    int valid=fstat(fd,&final)==0 && rpc_regular_v1(&final) && rpc_same_v1(&final,&o->temporary_identity) &&
        final.st_size==ready_length && rpc_read_v1(fd,final_bytes,(size_t)ready_length) && memcmp(final_bytes,bytes,(size_t)ready_length)==0 &&
        fstat(fd,&after)==0 && rpc_same_v1(&final,&after) &&
        fstatat(o->directory,o->ready,&named,AT_SYMLINK_NOFOLLOW)==0 && rpc_same_v1(&final,&named);
    if (close(fd)!=0) { result=RPC_CONSUMED; goto failed; }
    if (!valid || !rpc_initial_v1(o)) { result=RPC_PUBLICATION; goto failed; }
    o->phase=RPC_PUBLISHED; o->error=0; result=0; goto end;
failed: o->error=result;
end: pthread_mutex_unlock(&simple_private_credentials_lock_v1); return result;
}
int64_t rt_retained_private_credential_close_v1(int64_t token) {
    int locked=rpc_lock_v1(); if (locked) return locked;
    SimplePrivateCredentialV1 *o=rpc_find_v1(token); int64_t result=RPC_STALE;
    if (!o) goto end;
    if (o->phase==RPC_CLOSED || o->close_attempted) { result=RPC_STATE; goto end; }
    int failed=0;
    if (o->temporary_name[0]) {
        struct stat current;
        if (fstatat(o->directory,o->temporary_name,&current,AT_SYMLINK_NOFOLLOW)!=0 ||
            current.st_dev!=o->temporary_identity.st_dev || current.st_ino!=o->temporary_identity.st_ino ||
            unlinkat(o->directory,o->temporary_name,0)!=0 || fsync(o->directory)!=0) failed=1;
    }
    int fds[3]={o->temporary,o->initial,o->directory};
    o->temporary=o->initial=o->directory=-1; o->close_attempted=1;
    for (int i=0;i<3;i++) if (fds[i]>=0 && close(fds[i])!=0) failed=1;
    o->phase=failed?RPC_UNCERTAIN:RPC_CLOSED; o->error=failed?RPC_CONSUMED:0; result=o->error;
end: pthread_mutex_unlock(&simple_private_credentials_lock_v1); return result;
}
#else
int64_t rt_retained_private_credential_open_v1(int64_t a,int64_t b) { (void)a;(void)b;return -1; }
int64_t rt_retained_private_credential_state_v1(int64_t a) { (void)a;return -1; }
int64_t rt_retained_private_credential_error_v1(int64_t a) { (void)a;return -1; }
int64_t rt_retained_private_credential_read_v1(int64_t a,int64_t b,int64_t c) { (void)a;(void)b;(void)c;return -1; }
int64_t rt_retained_private_credential_publish_v1(int64_t a,int64_t b,int64_t c,int64_t d,int64_t e) { (void)a;(void)b;(void)c;(void)d;(void)e;return -1; }
int64_t rt_retained_private_credential_close_v1(int64_t a) { (void)a;return -1; }
#endif
#endif
#endif
