/* Native-C parity provider for common.cache_host_authority_v1.
 * Unix is descriptor anchored. Windows is deliberately release-blocking until
 * the CreateFileW/GetFinalPathNameByHandleW provider is admitted. */
#ifndef _WIN32
#define _GNU_SOURCE
#endif

#include <stdint.h>
#include <stddef.h>

/* Native-C daemon authority remains fail-closed until its canonical byte
 * records and cryptographic corruption checks exactly match the Rust provider. */
int64_t rt_cache_host_authenticate_peer_v1(int64_t root, int64_t peer) {(void)root;(void)peer;return -1;}
int64_t rt_cache_host_acquire_exclusive_lock_v1(int64_t root, int64_t peer) {(void)root;(void)peer;return -1;}
int64_t rt_cache_host_boot_identity_v1(int64_t lock) {(void)lock;return -1;}
int64_t rt_cache_host_advance_writer_epoch_v1(int64_t lock, int64_t boot) {(void)lock;(void)boot;return -1;}
int64_t rt_cache_host_publish_readiness_v1(int64_t lock,int64_t epoch,const uint8_t*nonce,int64_t len){(void)lock;(void)epoch;(void)nonce;(void)len;return -1;}
int64_t rt_cache_host_validate_readiness_v1(int64_t peer,int64_t ready,const uint8_t*nonce,int64_t len,int64_t epoch){(void)peer;(void)ready;(void)nonce;(void)len;(void)epoch;return -1;}
int64_t rt_cache_host_release_daemon_receipt_v1(int64_t handle){(void)handle;return -1;}

#ifdef _WIN32
#define UNSUPPORTED(name, args) int64_t name args { return -1; }
UNSUPPORTED(rt_cache_host_open_root_v1, (const uint8_t *p, int64_t n))
UNSUPPORTED(rt_cache_host_open_read_v1, (int64_t h, const uint8_t *p, int64_t n))
UNSUPPORTED(rt_cache_host_open_child_v1, (int64_t h, const uint8_t *p, int64_t n, int64_t c))
UNSUPPORTED(rt_cache_host_open_cas_kind_v1, (int64_t h, const uint8_t *p, int64_t n, int64_t c))
UNSUPPORTED(rt_cache_host_open_cas_shard_v1, (int64_t h, const uint8_t *p, int64_t n, int64_t l, int64_t c))
UNSUPPORTED(rt_cache_host_open_cas_leaf_v1, (int64_t h, const uint8_t *p, int64_t n))
UNSUPPORTED(rt_cache_host_begin_reader_pin_v1, (int64_t r,int64_t e,int64_t g,const uint8_t*m,int64_t ml,const uint8_t*p,int64_t pl,const uint8_t*b,int64_t bl,const uint8_t*ns,int64_t nl,int64_t now,int64_t ttl))
UNSUPPORTED(rt_cache_host_validate_reader_pin_v1, (int64_t h,int64_t e,int64_t g,const uint8_t*m,int64_t ml,const uint8_t*p,int64_t pl,const uint8_t*b,int64_t bl,const uint8_t*ns,int64_t nl,int64_t now))
UNSUPPORTED(rt_cache_host_renew_reader_pin_v1, (int64_t h,int64_t now,int64_t ttl))
UNSUPPORTED(rt_cache_host_release_reader_pin_v1, (int64_t h,int64_t e,int64_t g,const uint8_t*m,int64_t ml,const uint8_t*p,int64_t pl,const uint8_t*b,int64_t bl,const uint8_t*ns,int64_t nl))
UNSUPPORTED(rt_cache_host_open_pinned_cas_v1, (int64_t h,const uint8_t*k,int64_t kl,const uint8_t*d,int64_t dl,int64_t now))
UNSUPPORTED(rt_cache_host_reader_gc_begin_v1, (int64_t r,int64_t e))
UNSUPPORTED(rt_cache_host_reader_gc_end_v1, (int64_t r,int64_t e,int64_t g))
UNSUPPORTED(rt_cache_host_size_v1, (int64_t h, int64_t m))
UNSUPPORTED(rt_cache_host_pread_receipt_v1, (int64_t h, int64_t o, uint8_t *p, int64_t n))
UNSUPPORTED(rt_cache_host_secure_temp_v1, (int64_t h))
UNSUPPORTED(rt_cache_host_write_temp_v1, (int64_t h, int64_t o, const uint8_t *p, int64_t n))
UNSUPPORTED(rt_cache_host_publish_noreplace_v1, (int64_t h, const uint8_t *p, int64_t n))
UNSUPPORTED(rt_cache_host_quarantine_v1, (int64_t r, int64_t o, const uint8_t *p, int64_t n))
UNSUPPORTED(rt_cache_host_fsync_v1, (int64_t h))
UNSUPPORTED(rt_cache_host_close_v1, (int64_t h))
#else
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

enum cache_cap_kind { CAP_ROOT=1, CAP_DIR=2, CAP_READ=3, CAP_TEMP=4, CAP_CAS_ROOT=5, CAP_CAS_KIND=6, CAP_CAS_SHARD1=7, CAP_CAS_SHARD2=8, CAP_TEMP_CAS=9 };
struct cache_cap { int64_t token; int fd; int parent_fd; enum cache_cap_kind kind; char temp_name[96]; struct cache_cap *next; };
static struct cache_cap *caps;
static pthread_mutex_t caps_lock = PTHREAD_MUTEX_INITIALIZER;

static int64_t random_token(void) {
    uint64_t value = 0;
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC | O_NOFOLLOW);
    if (fd < 0 || read(fd, &value, sizeof value) != sizeof value) { if (fd >= 0) close(fd); return -1; }
    close(fd); value &= INT64_MAX; return value ? (int64_t)value : 1;
}
static struct cache_cap *find_cap(int64_t token) {
    struct cache_cap *p; for (p = caps; p; p = p->next) if (p->token == token) return p; return NULL;
}
static int64_t add_cap(enum cache_cap_kind kind, int fd, int parent_fd, const char *temp) {
    struct cache_cap *cap = calloc(1, sizeof *cap); if (!cap) return -1;
    cap->kind = kind; cap->fd = fd; cap->parent_fd = parent_fd;
    if (temp) snprintf(cap->temp_name, sizeof cap->temp_name, "%s", temp);
    pthread_mutex_lock(&caps_lock);
    do cap->token = random_token(); while (cap->token < 0 || find_cap(cap->token));
    cap->next = caps; caps = cap; pthread_mutex_unlock(&caps_lock); return cap->token;
}
static int copy_name(const uint8_t *p, int64_t n, char out[32769]) {
    if (!p || n <= 0 || n > 32768 || memchr(p, 0, (size_t)n)) return 0;
    memcpy(out, p, (size_t)n); out[n] = 0; return 1;
}
static int valid_relative(const char *p) {
    if (!*p || *p == '/') return 0;
    for (;;) { const char *slash = strchr(p, '/'); size_t n = slash ? (size_t)(slash-p) : strlen(p);
        if (!n || (n == 1 && p[0] == '.') || (n == 2 && p[0] == '.' && p[1] == '.')) return 0;
        if (!slash) return 1; p = slash + 1;
    }
}
static int lower_hex_n(const char *p,size_t n){if(strlen(p)!=n)return 0;for(size_t i=0;i<n;i++)if(!((p[i]>='0'&&p[i]<='9')||(p[i]>='a'&&p[i]<='f')))return 0;return 1;}
static int cas_kind_name(const char*p){return !strcmp(p,"source_blob")||!strcmp(p,"compile_snapshot")||!strcmp(p,"public_summary")||!strcmp(p,"file_ast")||!strcmp(p,"semantic_read_set");}
static int open_dir_child(int fd,const char*name,int create){if(create&&mkdirat(fd,name,0700)&&errno!=EEXIST)return-1;return openat(fd,name,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC);}
static int open_beneath(int root, const char *path, int flags, mode_t mode) {
    if (!valid_relative(path)) return -1;
    int parent = fcntl(root, F_DUPFD_CLOEXEC, 3); if (parent < 0) return -1;
    char copy[32769]; snprintf(copy, sizeof copy, "%s", path); char *save = NULL, *part = strtok_r(copy, "/", &save), *next;
    while (part && (next = strtok_r(NULL, "/", &save))) { int nfd = openat(parent, part, O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC); close(parent); if (nfd < 0) return -1; parent=nfd; part=next; }
    int fd = openat(parent, part, flags|O_NOFOLLOW|O_CLOEXEC, mode); close(parent); return fd;
}
static int open_absolute_root(const char *path) {
    if (*path != '/' || !valid_relative(path + 1)) return -1; int fd = open("/", O_RDONLY|O_DIRECTORY|O_CLOEXEC); if (fd < 0) return -1;
    char copy[32769]; snprintf(copy, sizeof copy, "%s", path+1); char *save=NULL, *part=strtok_r(copy,"/",&save);
    while (part) { int next=openat(fd,part,O_RDONLY|O_DIRECTORY|O_NOFOLLOW|O_CLOEXEC); close(fd); if(next<0)return -1; fd=next; part=strtok_r(NULL,"/",&save); } return fd;
}
int64_t rt_cache_host_open_root_v1(const uint8_t *p, int64_t n) {
    char path[32769]; if(!copy_name(p,n,path))return -1; int fd=open_absolute_root(path); return fd<0?-1:add_cap(CAP_ROOT,fd,-1,NULL);
}
int64_t rt_cache_host_open_read_v1(int64_t h,const uint8_t*p,int64_t n){char path[32769];if(!copy_name(p,n,path))return -1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);int root=(c&&(c->kind==CAP_ROOT||c->kind==CAP_DIR))?c->fd:-1;int fd=root<0?-1:open_beneath(root,path,O_RDONLY,0);pthread_mutex_unlock(&caps_lock);return fd<0?-1:add_cap(CAP_READ,fd,-1,NULL);}
int64_t rt_cache_host_open_child_v1(int64_t h,const uint8_t*p,int64_t n,int64_t create){char name[32769];if(!copy_name(p,n,name)||!valid_relative(name)||strchr(name,'/'))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);if(!c||(c->kind!=CAP_ROOT&&c->kind!=CAP_DIR)){pthread_mutex_unlock(&caps_lock);return-1;}if(c->kind==CAP_ROOT&&strcmp(name,"db")&&strcmp(name,"cas")&&strcmp(name,"journal")&&strcmp(name,"spool")&&strcmp(name,"quarantine")){pthread_mutex_unlock(&caps_lock);return-1;}int kind=(c->kind==CAP_ROOT&&!strcmp(name,"cas"))?CAP_CAS_ROOT:CAP_DIR;int fd=open_dir_child(c->fd,name,(int)create);pthread_mutex_unlock(&caps_lock);return fd<0?-1:add_cap((enum cache_cap_kind)kind,fd,-1,NULL);}
int64_t rt_cache_host_open_cas_kind_v1(int64_t h,const uint8_t*p,int64_t n,int64_t create){char name[32769];if(!copy_name(p,n,name)||!cas_kind_name(name))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);int fd=(!c||c->kind!=CAP_CAS_ROOT)?-1:open_dir_child(c->fd,name,(int)create);pthread_mutex_unlock(&caps_lock);return fd<0?-1:add_cap(CAP_CAS_KIND,fd,-1,NULL);}
int64_t rt_cache_host_open_cas_shard_v1(int64_t h,const uint8_t*p,int64_t n,int64_t level,int64_t create){char name[32769];if(!copy_name(p,n,name)||!lower_hex_n(name,2))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);int good=c&&((level==1&&c->kind==CAP_CAS_KIND)||(level==2&&c->kind==CAP_CAS_SHARD1));int fd=!good?-1:open_dir_child(c->fd,name,(int)create);pthread_mutex_unlock(&caps_lock);return fd<0?-1:add_cap(level==1?CAP_CAS_SHARD1:CAP_CAS_SHARD2,fd,-1,NULL);}
int64_t rt_cache_host_open_cas_leaf_v1(int64_t h,const uint8_t*p,int64_t n){char name[32769];if(!copy_name(p,n,name)||!lower_hex_n(name,60))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);int fd=(!c||c->kind!=CAP_CAS_SHARD2)?-1:openat(c->fd,name,O_RDONLY|O_NOFOLLOW|O_CLOEXEC);pthread_mutex_unlock(&caps_lock);return fd<0?-1:add_cap(CAP_READ,fd,-1,NULL);}
/* Reader admission is fail-closed in the native-C provider until its opaque
 * generation registry has parity with the Rust runtime. */
int64_t rt_cache_host_begin_reader_pin_v1(int64_t r,int64_t e,int64_t g,const uint8_t*m,int64_t ml,const uint8_t*p,int64_t pl,const uint8_t*b,int64_t bl,const uint8_t*ns,int64_t nl,int64_t now,int64_t ttl){(void)r;(void)e;(void)g;(void)m;(void)ml;(void)p;(void)pl;(void)b;(void)bl;(void)ns;(void)nl;(void)now;(void)ttl;return-1;}
int64_t rt_cache_host_validate_reader_pin_v1(int64_t h,int64_t e,int64_t g,const uint8_t*m,int64_t ml,const uint8_t*p,int64_t pl,const uint8_t*b,int64_t bl,const uint8_t*ns,int64_t nl,int64_t now){(void)h;(void)e;(void)g;(void)m;(void)ml;(void)p;(void)pl;(void)b;(void)bl;(void)ns;(void)nl;(void)now;return-1;}
int64_t rt_cache_host_renew_reader_pin_v1(int64_t h,int64_t now,int64_t ttl){(void)h;(void)now;(void)ttl;return-1;}
int64_t rt_cache_host_release_reader_pin_v1(int64_t h,int64_t e,int64_t g,const uint8_t*m,int64_t ml,const uint8_t*p,int64_t pl,const uint8_t*b,int64_t bl,const uint8_t*ns,int64_t nl){(void)h;(void)e;(void)g;(void)m;(void)ml;(void)p;(void)pl;(void)b;(void)bl;(void)ns;(void)nl;return-1;}
int64_t rt_cache_host_open_pinned_cas_v1(int64_t h,const uint8_t*k,int64_t kl,const uint8_t*d,int64_t dl,int64_t now){(void)h;(void)k;(void)kl;(void)d;(void)dl;(void)now;return-1;}
int64_t rt_cache_host_reader_gc_begin_v1(int64_t r,int64_t e){(void)r;(void)e;return-1;}
int64_t rt_cache_host_reader_gc_end_v1(int64_t r,int64_t e,int64_t g){(void)r;(void)e;(void)g;return-1;}
int64_t rt_cache_host_size_v1(int64_t h,int64_t maximum){if(maximum<0||maximum>67108864)return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);struct stat s;int64_t result=(!c||c->kind!=CAP_READ||fstat(c->fd,&s)||(s.st_mode&S_IFMT)!=S_IFREG||s.st_size<0||s.st_size>maximum)?-1:(int64_t)s.st_size;pthread_mutex_unlock(&caps_lock);return result;}
int64_t rt_cache_host_pread_receipt_v1(int64_t h,int64_t off,uint8_t*out,int64_t cap){if(!out||off||cap<0||cap>67108864)return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);if(!c||c->kind!=CAP_READ){pthread_mutex_unlock(&caps_lock);return-1;}struct stat a,b;if(fstat(c->fd,&a)||(a.st_mode&S_IFMT)!=S_IFREG||a.st_size<0||a.st_size>cap){pthread_mutex_unlock(&caps_lock);return-1;}size_t got=0,want=(size_t)a.st_size;while(got<want){ssize_t n=pread(c->fd,out+got,want-got,(off_t)got);if(n<=0){pthread_mutex_unlock(&caps_lock);return-1;}got+=(size_t)n;}uint8_t verify[4096];size_t checked=0;while(checked<want){size_t n=want-checked<sizeof verify?want-checked:sizeof verify;if(pread(c->fd,verify,n,(off_t)checked)!=(ssize_t)n||memcmp(out+checked,verify,n)){pthread_mutex_unlock(&caps_lock);return-2;}checked+=n;}int bad=fstat(c->fd,&b)||a.st_dev!=b.st_dev||a.st_ino!=b.st_ino||a.st_size!=b.st_size||a.st_mtim.tv_nsec!=b.st_mtim.tv_nsec||a.st_ctim.tv_nsec!=b.st_ctim.tv_nsec||a.st_mtime!=b.st_mtime||a.st_ctime!=b.st_ctime;pthread_mutex_unlock(&caps_lock);return bad?-2:(int64_t)want;}
int64_t rt_cache_host_secure_temp_v1(int64_t h){pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);if(!c||(c->kind!=CAP_ROOT&&c->kind!=CAP_DIR&&c->kind!=CAP_CAS_SHARD2)){pthread_mutex_unlock(&caps_lock);return-1;}int temp_kind=c->kind==CAP_CAS_SHARD2?CAP_TEMP_CAS:CAP_TEMP;int parent=fcntl(c->fd,F_DUPFD_CLOEXEC,3);pthread_mutex_unlock(&caps_lock);if(parent<0)return-1;for(int i=0;i<128;i++){char name[96];snprintf(name,sizeof name,".simple-cache-tmp-%ld-%lld",(long)getpid(),(long long)random_token());int fd=openat(parent,name,O_RDWR|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC,0600);if(fd>=0)return add_cap((enum cache_cap_kind)temp_kind,fd,parent,name);if(errno!=EEXIST)break;}close(parent);return-1;}
int64_t rt_cache_host_write_temp_v1(int64_t h,int64_t off,const uint8_t*p,int64_t n){if(!p||off<0||n<0||n>67108864)return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);ssize_t rc=(!c||(c->kind!=CAP_TEMP&&c->kind!=CAP_TEMP_CAS))?-1:pwrite(c->fd,p,(size_t)n,(off_t)off);pthread_mutex_unlock(&caps_lock);return rc;}
int64_t rt_cache_host_publish_noreplace_v1(int64_t h,const uint8_t*p,int64_t n){char dest[32769];if(!copy_name(p,n,dest)||!valid_relative(dest)||strchr(dest,'/'))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);if(!c||(c->kind!=CAP_TEMP&&c->kind!=CAP_TEMP_CAS)||(c->kind==CAP_TEMP_CAS&&!lower_hex_n(dest,60))||fsync(c->fd)||fchmod(c->fd,0444)){pthread_mutex_unlock(&caps_lock);return-1;}
#ifdef __linux__
int rc=(int)syscall(SYS_renameat2,c->parent_fd,c->temp_name,c->parent_fd,dest,RENAME_NOREPLACE);
#else
int rc=linkat(c->parent_fd,c->temp_name,c->parent_fd,dest,0);if(!rc)unlinkat(c->parent_fd,c->temp_name,0);
#endif
if(rc){int e=errno;pthread_mutex_unlock(&caps_lock);return e==EEXIST?0:-1;}fsync(c->parent_fd);struct cache_cap**slot=&caps;while(*slot&&*slot!=c)slot=&(*slot)->next;if(*slot)*slot=c->next;close(c->fd);close(c->parent_fd);free(c);pthread_mutex_unlock(&caps_lock);return 1;}
int64_t rt_cache_host_quarantine_v1(int64_t r,int64_t o,const uint8_t*p,int64_t n){
#ifndef __linux__
(void)r;(void)o;(void)p;(void)n;return-1;
#else
char dest[32769];if(!copy_name(p,n,dest)||!valid_relative(dest)||strchr(dest,'/'))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*root=find_cap(r),*obj=find_cap(o);if(!root||!obj||(root->kind!=CAP_ROOT&&root->kind!=CAP_DIR)||obj->kind!=CAP_READ){pthread_mutex_unlock(&caps_lock);return-1;}int rc=linkat(obj->fd,"",root->fd,dest,AT_EMPTY_PATH);int e=errno;if(!rc)fsync(root->fd);pthread_mutex_unlock(&caps_lock);return rc?(e==EEXIST?0:-1):1;
#endif
}
int64_t rt_cache_host_fsync_v1(int64_t h){pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);int rc=c?fsync(c->fd):-1;pthread_mutex_unlock(&caps_lock);return rc?-1:1;}
int64_t rt_cache_host_close_v1(int64_t h){pthread_mutex_lock(&caps_lock);struct cache_cap**p=&caps,*c=NULL;while(*p){if((*p)->token==h){c=*p;*p=c->next;break;}p=&(*p)->next;}pthread_mutex_unlock(&caps_lock);if(!c)return-1;if(c->kind==CAP_TEMP||c->kind==CAP_TEMP_CAS){unlinkat(c->parent_fd,c->temp_name,0);close(c->parent_fd);}int rc=close(c->fd);free(c);return rc;}
#endif
