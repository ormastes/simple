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

/* ===========================================================================
 * Native-C lane for the bounded cache-daemon transport.
 *
 * The Rust lane is src/compiler_rust/runtime/src/cache_daemon_process_v1.rs.
 * These two are parallel implementations of the SAME two rt_* names and the
 * SAME on-the-wire protocol, per the standing rt_* dual-implementation
 * directive; they are never linked together (the Rust crate does not compile
 * this file, and the seed's core-C capsule does not link the crate).
 *
 * Why a real port and not a fail-closed -1 stub like the seven rt_cache_host_*
 * receipt entry points above: those are blocked on canonical byte-record and
 * cryptographic-corruption parity with the Rust provider, which is a genuine
 * open design question. These two are not. They are called from pure-Simple
 * stdlib product code (src/lib/common/cache_daemon_host_authority_v1.spl), so
 * with no C definition they are an unbacked extern -- silent nil, not a link
 * error. And route() returning -1 would be semantically WRONG rather than
 * merely conservative: the contract is that failure selects the anchored-spool
 * lane (2), so -1 asserts "spool failed too", which is a different claim.
 *
 * PROTOCOL -- must stay byte-identical to the Rust lane:
 *   request  40 bytes: "SCREQV1\0" (8) || client nonce (32)
 *   response 80 bytes: "SCACKV1\0" (8) || echoed nonce (32)
 *                      || server pid  (4, little-endian i32)
 *                      || server euid (4, little-endian u32)
 *                      || SHA-256 over the first 48 bytes (32)
 *   Both ends additionally require SO_PEERCRED uid == geteuid().
 *
 * Every helper here is named cdv1_*, never rt_*. The dual-implementation
 * ratchet harvests C definitions by TEXT -- an rt_-prefixed identifier followed
 * by a parenthesised parameter list and an opening brace -- so an rt_-prefixed
 * static helper would register as a brand-new c-only runtime symbol, and even
 * writing that pattern inside a comment is enough to trip it.
 * ======================================================================== */

#if defined(__linux__)

#include <poll.h>
#include <sys/file.h>
#include <sys/random.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <time.h>

#define CDV1_INVALID          ((int64_t)-1)
#define CDV1_ROUTE_DAEMON     ((int64_t)1)
#define CDV1_ROUTE_SPOOL      ((int64_t)2)
#define CDV1_CONNECT_BUDGET_MS 250
#define CDV1_IDLE_MIN_MS       10000u
#define CDV1_IDLE_MAX_MS       12000u
#define CDV1_IO_BUDGET_MS      50
#define CDV1_SOCKET_NAME      ".simple-cache-daemon-v1.sock"
#define CDV1_LOCK_NAME        ".simple-cache-daemon-v1.lock"
#define CDV1_REQ_MAGIC        "SCREQV1"   /* 7 chars + implicit NUL = 8 bytes */
#define CDV1_ACK_MAGIC        "SCACKV1"
#define CDV1_REQ_LEN          40
#define CDV1_ACK_LEN          80

/* ------------------------------------------------------------------ SHA-256
 * Self-contained on purpose. runtime_native.c's compressor is `static` and so
 * not linkable from this translation unit, and un-static-ing it would publish
 * a new rt_-prefixed symbol into the very population the ratchet freezes. */
static uint32_t cdv1_rotr(uint32_t v, unsigned s) { return (v >> s) | (v << (32 - s)); }

static void cdv1_sha256_block(uint32_t st[8], const uint8_t b[64]) {
    static const uint32_t K[64] = {
        0x428a2f98u,0x71374491u,0xb5c0fbcfu,0xe9b5dba5u,0x3956c25bu,0x59f111f1u,
        0x923f82a4u,0xab1c5ed5u,0xd807aa98u,0x12835b01u,0x243185beu,0x550c7dc3u,
        0x72be5d74u,0x80deb1feu,0x9bdc06a7u,0xc19bf174u,0xe49b69c1u,0xefbe4786u,
        0x0fc19dc6u,0x240ca1ccu,0x2de92c6fu,0x4a7484aau,0x5cb0a9dcu,0x76f988dau,
        0x983e5152u,0xa831c66du,0xb00327c8u,0xbf597fc7u,0xc6e00bf3u,0xd5a79147u,
        0x06ca6351u,0x14292967u,0x27b70a85u,0x2e1b2138u,0x4d2c6dfcu,0x53380d13u,
        0x650a7354u,0x766a0abbu,0x81c2c92eu,0x92722c85u,0xa2bfe8a1u,0xa81a664bu,
        0xc24b8b70u,0xc76c51a3u,0xd192e819u,0xd6990624u,0xf40e3585u,0x106aa070u,
        0x19a4c116u,0x1e376c08u,0x2748774cu,0x34b0bcb5u,0x391c0cb3u,0x4ed8aa4au,
        0x5b9cca4fu,0x682e6ff3u,0x748f82eeu,0x78a5636fu,0x84c87814u,0x8cc70208u,
        0x90befffau,0xa4506cebu,0xbef9a3f7u,0xc67178f2u };
    uint32_t w[64];
    for (int i = 0; i < 16; i++)
        w[i] = ((uint32_t)b[i*4] << 24) | ((uint32_t)b[i*4+1] << 16)
             | ((uint32_t)b[i*4+2] << 8) | (uint32_t)b[i*4+3];
    for (int i = 16; i < 64; i++) {
        uint32_t s0 = cdv1_rotr(w[i-15],7) ^ cdv1_rotr(w[i-15],18) ^ (w[i-15] >> 3);
        uint32_t s1 = cdv1_rotr(w[i-2],17) ^ cdv1_rotr(w[i-2],19) ^ (w[i-2] >> 10);
        w[i] = w[i-16] + s0 + w[i-7] + s1;
    }
    uint32_t a=st[0],bb=st[1],c=st[2],d=st[3],e=st[4],f=st[5],g=st[6],h=st[7];
    for (int i = 0; i < 64; i++) {
        uint32_t s1 = cdv1_rotr(e,6) ^ cdv1_rotr(e,11) ^ cdv1_rotr(e,25);
        uint32_t ch = (e & f) ^ ((~e) & g);
        uint32_t t1 = h + s1 + ch + K[i] + w[i];
        uint32_t s0 = cdv1_rotr(a,2) ^ cdv1_rotr(a,13) ^ cdv1_rotr(a,22);
        uint32_t mj = (a & bb) ^ (a & c) ^ (bb & c);
        uint32_t t2 = s0 + mj;
        h=g; g=f; f=e; e=d+t1; d=c; c=bb; bb=a; a=t1+t2;
    }
    st[0]+=a; st[1]+=bb; st[2]+=c; st[3]+=d; st[4]+=e; st[5]+=f; st[6]+=g; st[7]+=h;
}

/* Only ever called with len < 56, so a single padded block suffices; the loop
 * and the two-block tail are kept anyway so the helper is correct in general. */
static void cdv1_sha256(const uint8_t *msg, size_t len, uint8_t out[32]) {
    uint32_t st[8] = { 0x6a09e667u,0xbb67ae85u,0x3c6ef372u,0xa54ff53au,
                       0x510e527fu,0x9b05688cu,0x1f83d9abu,0x5be0cd19u };
    size_t i = 0;
    for (; i + 64 <= len; i += 64) cdv1_sha256_block(st, msg + i);
    uint8_t tail[128];
    size_t rem = len - i;
    memset(tail, 0, sizeof tail);
    memcpy(tail, msg + i, rem);
    tail[rem] = 0x80;
    size_t total = (rem + 1 + 8 <= 64) ? 64 : 128;
    uint64_t bits = (uint64_t)len * 8u;
    for (int k = 0; k < 8; k++) tail[total - 1 - k] = (uint8_t)(bits >> (8 * k));
    cdv1_sha256_block(st, tail);
    if (total == 128) cdv1_sha256_block(st, tail + 64);
    for (int k = 0; k < 8; k++) {
        out[k*4]   = (uint8_t)(st[k] >> 24);
        out[k*4+1] = (uint8_t)(st[k] >> 16);
        out[k*4+2] = (uint8_t)(st[k] >> 8);
        out[k*4+3] = (uint8_t)(st[k]);
    }
}

/* ------------------------------------------------------------------- helpers */

static int64_t cdv1_now_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return -1;
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* Mirrors Rust `absolute_root`: bounded, NUL-free, and absolute. */
static int cdv1_absolute_root(const uint8_t *p, int64_t n, char out[32769]) {
    if (!p || n <= 0 || n > 32768) return 0;
    if (memchr(p, 0, (size_t)n)) return 0;
    memcpy(out, p, (size_t)n);
    out[n] = 0;
    return out[0] == '/';
}

static int cdv1_open_root_checked(const char *path) {
    return open(path, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
}

static void cdv1_socket_path(int root_fd, char *out, size_t cap) {
    snprintf(out, cap, "/proc/self/fd/%d/%s", root_fd, CDV1_SOCKET_NAME);
}

static int cdv1_random_nonce(uint8_t out[32]) {
    size_t got = 0;
    while (got < 32) {
        ssize_t r = getrandom(out + got, 32 - got, 0);
        if (r <= 0) { if (errno == EINTR) continue; return 0; }
        got += (size_t)r;
    }
    return 1;
}

static int cdv1_set_io_budget(int fd) {
    struct timeval tv;
    tv.tv_sec = 0;
    tv.tv_usec = CDV1_IO_BUDGET_MS * 1000;
    if (setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv) != 0) return 0;
    return setsockopt(fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv) == 0;
}

static int cdv1_peer(int fd, uint32_t *uid, int32_t *pid) {
    struct ucred cred;
    socklen_t len = sizeof cred;
    memset(&cred, 0, sizeof cred);
    if (getsockopt(fd, SOL_SOCKET, SO_PEERCRED, &cred, &len) != 0) return 0;
    if (len != sizeof cred) return 0;
    *uid = (uint32_t)cred.uid;
    *pid = (int32_t)cred.pid;
    return 1;
}

static int cdv1_read_exact(int fd, uint8_t *buf, size_t n) {
    size_t got = 0;
    while (got < n) {
        ssize_t r = read(fd, buf + got, n - got);
        if (r == 0) return 0;
        if (r < 0) { if (errno == EINTR) continue; return 0; }
        got += (size_t)r;
    }
    return 1;
}

static int cdv1_write_all(int fd, const uint8_t *buf, size_t n) {
    size_t put = 0;
    while (put < n) {
        ssize_t w = write(fd, buf + put, n - put);
        if (w <= 0) { if (w < 0 && errno == EINTR) continue; return 0; }
        put += (size_t)w;
    }
    return 1;
}

static int cdv1_connect(const char *path) {
    struct sockaddr_un addr;
    size_t len = strlen(path);
    if (len >= sizeof addr.sun_path) return -1;
    int fd = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (fd < 0) return -1;
    memset(&addr, 0, sizeof addr);
    addr.sun_family = AF_UNIX;
    memcpy(addr.sun_path, path, len);
    if (connect(fd, (struct sockaddr *)&addr, sizeof addr) != 0) { close(fd); return -1; }
    return fd;
}

/* Client half of the handshake. Mirrors Rust `exchange`. */
static int cdv1_exchange(int fd) {
    uint8_t nonce[32], req[CDV1_REQ_LEN], ack[CDV1_ACK_LEN], digest[32];
    uint32_t uid = 0, ack_uid;
    int32_t pid = 0, ack_pid;
    if (!cdv1_set_io_budget(fd)) return 0;
    if (!cdv1_random_nonce(nonce)) return 0;
    memcpy(req, CDV1_REQ_MAGIC, 8);
    memcpy(req + 8, nonce, 32);
    if (!cdv1_write_all(fd, req, sizeof req)) return 0;
    if (!cdv1_read_exact(fd, ack, sizeof ack)) return 0;
    if (memcmp(ack, CDV1_ACK_MAGIC, 8) != 0) return 0;
    if (memcmp(ack + 8, nonce, 32) != 0) return 0;
    if (!cdv1_peer(fd, &uid, &pid)) return 0;
    ack_pid = (int32_t)((uint32_t)ack[40] | ((uint32_t)ack[41] << 8)
                      | ((uint32_t)ack[42] << 16) | ((uint32_t)ack[43] << 24));
    ack_uid = (uint32_t)ack[44] | ((uint32_t)ack[45] << 8)
            | ((uint32_t)ack[46] << 16) | ((uint32_t)ack[47] << 24);
    cdv1_sha256(ack, 48, digest);
    return uid == (uint32_t)geteuid() && uid == ack_uid && pid == ack_pid
        && memcmp(digest, ack + 48, 32) == 0;
}

static int cdv1_try_connect(int root_fd) {
    char path[128];
    cdv1_socket_path(root_fd, path, sizeof path);
    int fd = cdv1_connect(path);
    if (fd < 0) return 0;
    int ok = cdv1_exchange(fd);
    close(fd);
    return ok;
}

static int cdv1_anchored_spool(int root_fd) {
    if (mkdirat(root_fd, "spool", 0700) != 0 && errno != EEXIST) return 0;
    int fd = openat(root_fd, "spool", O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) return 0;
    int ok = fsync(fd) == 0;
    close(fd);
    return ok;
}

static int cdv1_lock(int root_fd) {
    int fd = openat(root_fd, CDV1_LOCK_NAME,
                    O_RDWR | O_CREAT | O_NOFOLLOW | O_CLOEXEC, 0600);
    if (fd < 0) return -1;
    if (flock(fd, LOCK_EX | LOCK_NB) != 0) { close(fd); return -1; }
    return fd;
}

static int cdv1_advance_epoch(int lock_fd, uint64_t *out) {
    uint8_t raw[8];
    uint64_t previous = 0, next;
    ssize_t got = pread(lock_fd, raw, sizeof raw, 0);
    if (got == (ssize_t)sizeof raw)
        for (int i = 7; i >= 0; i--) previous = (previous << 8) | raw[i];
    if (previous == UINT64_MAX) return 0;
    next = previous + 1;
    for (int i = 0; i < 8; i++) raw[i] = (uint8_t)(next >> (8 * i));
    if (pwrite(lock_fd, raw, sizeof raw, 0) != (ssize_t)sizeof raw) return 0;
    if (fdatasync(lock_fd) != 0) return 0;
    *out = next;
    return 1;
}

/* Server half of the handshake. Mirrors Rust `serve_client`. */
static int cdv1_serve_client(int fd, uint64_t epoch) {
    uint8_t req[CDV1_REQ_LEN], ack[CDV1_ACK_LEN], digest[32];
    uint32_t uid = 0, euid;
    int32_t pid = 0;
    int32_t self_pid;
    (void)epoch; /* Epoch stays lock-owned; journal operations bind it separately. */
    if (!cdv1_set_io_budget(fd)) return 0;
    if (!cdv1_peer(fd, &uid, &pid)) return 0;
    if (uid != (uint32_t)geteuid()) return 0;
    if (!cdv1_read_exact(fd, req, sizeof req)) return 0;
    if (memcmp(req, CDV1_REQ_MAGIC, 8) != 0) return 0;
    memset(ack, 0, sizeof ack);
    memcpy(ack, CDV1_ACK_MAGIC, 8);
    memcpy(ack + 8, req + 8, 32);
    self_pid = (int32_t)getpid();
    euid = (uint32_t)geteuid();
    for (int i = 0; i < 4; i++) ack[40 + i] = (uint8_t)(((uint32_t)self_pid) >> (8 * i));
    for (int i = 0; i < 4; i++) ack[44 + i] = (uint8_t)(euid >> (8 * i));
    cdv1_sha256(ack, 48, digest);
    memcpy(ack + 48, digest, 32);
    return cdv1_write_all(fd, ack, sizeof ack);
}

static int64_t cdv1_serve(int root_fd, int ready_fd, uint64_t idle_min_ms, uint64_t idle_max_ms) {
    char path[128];
    struct sockaddr_un addr;
    uint64_t epoch = 0;
    int64_t idle_since;
    int lock_fd, listener, flags;
    size_t path_len;

    lock_fd = cdv1_lock(root_fd);
    if (lock_fd < 0) return CDV1_INVALID;
    if (!cdv1_advance_epoch(lock_fd, &epoch)) {
        flock(lock_fd, LOCK_UN);
        close(lock_fd);
        return CDV1_INVALID;
    }

    cdv1_socket_path(root_fd, path, sizeof path);
    unlinkat(root_fd, CDV1_SOCKET_NAME, 0);

    path_len = strlen(path);
    if (path_len >= sizeof addr.sun_path) { close(lock_fd); return CDV1_INVALID; }
    listener = socket(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0);
    if (listener < 0) { close(lock_fd); return CDV1_INVALID; }
    memset(&addr, 0, sizeof addr);
    addr.sun_family = AF_UNIX;
    memcpy(addr.sun_path, path, path_len);
    if (bind(listener, (struct sockaddr *)&addr, sizeof addr) != 0
        || listen(listener, 128) != 0) {
        close(listener);
        close(lock_fd);
        return CDV1_INVALID;
    }
    fchmodat(root_fd, CDV1_SOCKET_NAME, 0600, 0);
    flags = fcntl(listener, F_GETFL, 0);
    if (flags < 0 || fcntl(listener, F_SETFL, flags | O_NONBLOCK) != 0) {
        close(listener);
        close(lock_fd);
        return CDV1_INVALID;
    }

    if (ready_fd >= 0) {
        ssize_t ignored = write(ready_fd, "R", 1);
        (void)ignored;
        close(ready_fd);
    }

    idle_since = cdv1_now_ms();
    for (;;) {
        struct pollfd pfd;
        int64_t elapsed = cdv1_now_ms() - idle_since;
        uint64_t remain, wait;
        int rc, client;
        if (elapsed < 0) break;
        if ((uint64_t)elapsed >= idle_min_ms) break;
        remain = idle_min_ms - (uint64_t)elapsed;
        wait = remain < idle_max_ms ? remain : idle_max_ms;
        pfd.fd = listener;
        pfd.events = POLLIN;
        pfd.revents = 0;
        rc = poll(&pfd, 1, wait > (uint64_t)INT32_MAX ? INT32_MAX : (int)wait);
        if (rc < 0) { if (errno == EINTR) continue; break; }
        if (rc == 0) continue;
        while ((client = accept4(listener, NULL, NULL, SOCK_CLOEXEC)) >= 0) {
            cdv1_serve_client(client, epoch);
            close(client);
            idle_since = cdv1_now_ms();
        }
    }

    close(listener);
    unlinkat(root_fd, CDV1_SOCKET_NAME, 0);
    fsync(root_fd); /* checkpoint before releasing the writer receipt */
    flock(lock_fd, LOCK_UN);
    close(lock_fd);
    return 0;
}

int64_t rt_cache_daemon_serve_v1(const uint8_t *path, int64_t len) {
    char root[32769];
    int root_fd;
    int64_t rc;
    if (!cdv1_absolute_root(path, len, root)) return CDV1_INVALID;
    root_fd = cdv1_open_root_checked(root);
    if (root_fd < 0) return CDV1_INVALID;
    rc = cdv1_serve(root_fd, -1, CDV1_IDLE_MIN_MS, CDV1_IDLE_MAX_MS);
    close(root_fd);
    return rc;
}

int64_t rt_cache_daemon_route_v1(const uint8_t *path, int64_t len) {
    char root[32769];
    int root_fd, signal_fds[2], spool;
    if (!cdv1_absolute_root(path, len, root)) return CDV1_INVALID;
    root_fd = cdv1_open_root_checked(root);
    if (root_fd < 0) return CDV1_INVALID;
    if (cdv1_try_connect(root_fd)) {
        close(root_fd);
        return CDV1_ROUTE_DAEMON;
    }
    if (pipe2(signal_fds, O_CLOEXEC) == 0) {
        pid_t pid = fork();
        if (pid == 0) {
            close(signal_fds[0]);
            int64_t rc = cdv1_serve(root_fd, signal_fds[1],
                                    CDV1_IDLE_MIN_MS, CDV1_IDLE_MAX_MS);
            _exit(rc == 0 ? 0 : 1);
        }
        close(signal_fds[1]);
        if (pid > 0) {
            struct pollfd pfd;
            uint8_t byte = 0;
            int ready;
            pfd.fd = signal_fds[0];
            pfd.events = POLLIN;
            pfd.revents = 0;
            poll(&pfd, 1, CDV1_CONNECT_BUDGET_MS);
            ready = read(signal_fds[0], &byte, 1) == 1 && byte == 'R';
            close(signal_fds[0]);
            if (ready && cdv1_try_connect(root_fd)) {
                close(root_fd);
                return CDV1_ROUTE_DAEMON;
            }
        } else {
            close(signal_fds[0]);
        }
    }
    spool = cdv1_anchored_spool(root_fd);
    close(root_fd);
    return spool ? CDV1_ROUTE_SPOOL : CDV1_INVALID;
}

#else /* !__linux__ -- mirrors the Rust lane's cfg(not(target_os = "linux")) */

int64_t rt_cache_daemon_serve_v1(const uint8_t *path, int64_t len) {
    (void)path; (void)len; return -1;
}
int64_t rt_cache_daemon_route_v1(const uint8_t *path, int64_t len) {
    (void)path; (void)len; return -1;
}

#endif /* __linux__ */
