/* Native-C parity provider for common.cache_host_authority_v1.
 * Unix and Windows file operations are descriptor/handle anchored. */
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
int64_t rt_cache_host_mutation_scope_available_v1(void){return -1;}
int64_t rt_cache_host_commit_journal_v1(int64_t lock,int64_t peer,int64_t ready,const uint8_t*nonce,int64_t nonce_len,int64_t epoch,int64_t expected,const uint8_t*prefix,int64_t prefix_len,const uint8_t*append,int64_t append_len){(void)lock;(void)peer;(void)ready;(void)nonce;(void)nonce_len;(void)epoch;(void)expected;(void)prefix;(void)prefix_len;(void)append;(void)append_len;return -1;}
int64_t rt_cache_host_read_journal_v1(int64_t lock,int64_t peer,int64_t ready,const uint8_t*nonce,int64_t nonce_len,int64_t epoch,uint8_t*out,int64_t cap){(void)lock;(void)peer;(void)ready;(void)nonce;(void)nonce_len;(void)epoch;(void)out;(void)cap;return -1;}
int64_t rt_cache_host_release_daemon_receipt_v1(int64_t handle){(void)handle;return -1;}
/* Host-GC v2 requires one cross-process writer/reader namespace plus exact
 * descriptor-bound unlink.  The native-C provider has no admitted receipt
 * table for that authority and therefore stays explicitly unsupported. */
int64_t rt_cache_host_capture_durable_head_v2(int64_t lock,int64_t peer,int64_t ready,const uint8_t*nonce,int64_t nonce_len,int64_t writer_epoch,int64_t journal_bytes,const uint8_t*journal_digest,int64_t journal_digest_len,int64_t journal_generation,int64_t superblock_generation,const uint8_t*superblock_digest,int64_t superblock_digest_len,int64_t root_count){(void)lock;(void)peer;(void)ready;(void)nonce;(void)nonce_len;(void)writer_epoch;(void)journal_bytes;(void)journal_digest;(void)journal_digest_len;(void)journal_generation;(void)superblock_generation;(void)superblock_digest;(void)superblock_digest_len;(void)root_count;return -1;}
int64_t rt_cache_host_gc_begin_v2(int64_t root,int64_t head,int64_t even_epoch,int64_t max_roots,int64_t max_page_bytes,int64_t max_candidates){(void)root;(void)head;(void)even_epoch;(void)max_roots;(void)max_page_bytes;(void)max_candidates;return -1;}
int64_t rt_cache_host_gc_root_page_v2(int64_t window,int64_t cursor,uint8_t*out,int64_t cap){(void)window;(void)cursor;(void)out;(void)cap;return -1;}
int64_t rt_cache_host_gc_pin_page_v2(int64_t window,int64_t cursor,uint8_t*out,int64_t cap){(void)window;(void)cursor;(void)out;(void)cap;return -1;}
int64_t rt_cache_host_gc_open_candidate_v2(int64_t window,const uint8_t*kind,int64_t kind_len,const uint8_t*digest,int64_t digest_len){(void)window;(void)kind;(void)kind_len;(void)digest;(void)digest_len;return -1;}
int64_t rt_cache_host_gc_unlink_candidate_v2(int64_t window,int64_t candidate){(void)window;(void)candidate;return -1;}
int64_t rt_cache_host_gc_finish_v2(int64_t window,int64_t odd_epoch){(void)window;(void)odd_epoch;return -1;}
int64_t rt_cache_host_gc_abort_v2(int64_t window,int64_t odd_epoch){(void)window;(void)odd_epoch;return -1;}
int64_t rt_cache_host_release_durable_head_v2(int64_t head){(void)head;return -1;}

/* V3 namespace ABI. The native-C capsule deliberately reports Unsupported
 * on POSIX and Windows until it has the same descriptor registry, durable
 * recovery barrier, and complete roots/readers/leases/pins inventory as an
 * admitted provider. Keeping the exact symbols here prevents an
 * unbacked extern from being mistaken for a successful zero result. */
int64_t rt_cache_host_namespace_available_v3(void){return -3;}
int64_t rt_cache_host_namespace_open_v3(int64_t r,int64_t l,int64_t p,int64_t ready,const uint8_t*n,int64_t nl,int64_t we,int64_t mr,int64_t mrd,int64_t mlr,int64_t mso,int64_t mpb,int64_t mc){(void)r;(void)l;(void)p;(void)ready;(void)n;(void)nl;(void)we;(void)mr;(void)mrd;(void)mlr;(void)mso;(void)mpb;(void)mc;return -3;}
int64_t rt_cache_host_namespace_begin_v3(int64_t ns,int64_t mode,const uint8_t*head,int64_t head_len,int64_t pin){(void)ns;(void)mode;(void)head;(void)head_len;(void)pin;return -3;}
int64_t rt_cache_host_namespace_sync_object_v3(int64_t scope,int64_t object,const uint8_t*kind,int64_t kind_len,int64_t schema,const uint8_t*digest,int64_t digest_len,int64_t size){(void)scope;(void)object;(void)kind;(void)kind_len;(void)schema;(void)digest;(void)digest_len;(void)size;return -3;}
int64_t rt_cache_host_namespace_commit_selected_v3(int64_t scope,const uint8_t*head,int64_t head_len,const uint8_t*append,int64_t append_len,const int64_t*objects,int64_t object_count){(void)scope;(void)head;(void)head_len;(void)append;(void)append_len;(void)objects;(void)object_count;return -3;}
int64_t rt_cache_host_namespace_recovery_capture_v3(int64_t scope){(void)scope;return -3;}
int64_t rt_cache_host_namespace_recovery_read_v3(int64_t recovery,int64_t part,int64_t offset,uint8_t*out,int64_t cap){(void)recovery;(void)part;(void)offset;(void)out;(void)cap;return -3;}
int64_t rt_cache_host_namespace_resolve_operation_v3(int64_t recovery,int64_t writer,const uint8_t*operation,int64_t operation_len,int64_t generation,const uint8_t*manifest,int64_t manifest_len){(void)recovery;(void)writer;(void)operation;(void)operation_len;(void)generation;(void)manifest;(void)manifest_len;return -3;}
int64_t rt_cache_host_namespace_gc_roots_page_v3(int64_t scope,int64_t cursor,uint8_t*out,int64_t cap){(void)scope;(void)cursor;(void)out;(void)cap;return -3;}
int64_t rt_cache_host_namespace_gc_open_candidate_v3(int64_t scope,const uint8_t*kind,int64_t kind_len,int64_t schema,const uint8_t*digest,int64_t digest_len){(void)scope;(void)kind;(void)kind_len;(void)schema;(void)digest;(void)digest_len;return -3;}
int64_t rt_cache_host_namespace_gc_unlink_candidate_v3(int64_t scope,int64_t candidate){(void)scope;(void)candidate;return -3;}
int64_t rt_cache_host_namespace_finish_v3(int64_t scope){(void)scope;return -3;}
int64_t rt_cache_host_namespace_abort_v3(int64_t scope){(void)scope;return -3;}
int64_t rt_cache_host_namespace_close_v3(int64_t ns){(void)ns;return -3;}

#ifdef _WIN32
/* Windows file-authority subset, implemented in its canonical C owner.
 * Every capability retains its directory ancestry without DELETE sharing.
 * Reads additionally exclude WRITE sharing: receipt bytes cannot be replaced
 * or modified through ordinary filesystem handles while their authority lives.
 * UNC/device roots and reparse points deliberately fail closed. */
#include <windows.h>
#include <stdlib.h>
#include <string.h>
#include <wchar.h>
#include <stdio.h>

#define CW_PATH 32760
#define CW_DEPTH 256
#define CW_LIMIT 67108864
enum cw_kind { CW_ROOT, CW_READ, CW_TEMP, CW_SEALED };
struct cw_cap {
    int64_t token;
    enum cw_kind kind;
    HANDLE handles[CW_DEPTH];
    unsigned count;
    int sealed;
    struct cw_cap *next;
};
static SRWLOCK cw_lock = SRWLOCK_INIT;
static struct cw_cap *cw_caps;
static int cw_random(void *,ULONG);

static struct cw_cap *cw_find(int64_t token) {
    struct cw_cap *c;
    for (c = cw_caps; c; c = c->next) if (c->token == token) return c;
    return NULL;
}
static HANDLE cw_file(struct cw_cap *c) { return c->handles[c->count - 1]; }
static void cw_free(struct cw_cap *c) {
    if (!c) return;
    while (c->count) CloseHandle(c->handles[--c->count]);
    free(c);
}
static int64_t cw_admit(struct cw_cap *c, enum cw_kind kind) {
    if (!c) return -1;
    for (int i=0; i<128; ++i) {
        uint64_t token;
        if (!cw_random(&token,sizeof token)) break;
        token &= INT64_MAX;
        if (!token || cw_find((int64_t)token)) continue;
        c->token=(int64_t)token; c->kind=kind; c->next=cw_caps; cw_caps=c;
        return c->token;
    }
    cw_free(c); return -1;
}
static struct cw_cap *cw_clone(struct cw_cap *src) {
    struct cw_cap *c = (struct cw_cap *)calloc(1, sizeof *c);
    if (!c) return NULL;
    for (unsigned i = 0; i < src->count; ++i) {
        if (!DuplicateHandle(GetCurrentProcess(), src->handles[i], GetCurrentProcess(),
                &c->handles[c->count], 0, FALSE, DUPLICATE_SAME_ACCESS)) { cw_free(c); return NULL; }
        ++c->count;
    }
    return c;
}
static wchar_t *cw_widen(const uint8_t *p, int64_t n) {
    if (!p || n <= 0 || n > CW_PATH || memchr(p, 0, (size_t)n)) return NULL;
    int len = MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, (const char *)p, (int)n, NULL, 0);
    if (len <= 0 || len >= CW_PATH) return NULL;
    wchar_t *w = (wchar_t *)calloc((size_t)len + 1, sizeof *w);
    if (!w) return NULL;
    if (!MultiByteToWideChar(CP_UTF8, MB_ERR_INVALID_CHARS, (const char *)p, (int)n, w, len)) { free(w); return NULL; }
    return w;
}
static int cw_component(const wchar_t *p, size_t n) {
    if (!n || n > 255 || p[n-1] == L'.' || p[n-1] == L' ') return 0;
    for (size_t i = 0; i < n; ++i)
        if (p[i] < 32 || wcschr(L"\\/:*?\"<>|", p[i])) return 0;
    size_t base = 0; while (base < n && p[base] != L'.') ++base;
    if ((base == 3 && (!_wcsnicmp(p,L"CON",3) || !_wcsnicmp(p,L"PRN",3) ||
            !_wcsnicmp(p,L"AUX",3) || !_wcsnicmp(p,L"NUL",3))) ||
        (base == 4 && (!_wcsnicmp(p,L"COM",3) || !_wcsnicmp(p,L"LPT",3)) &&
            ((p[3] >= L'1' && p[3] <= L'9') || p[3] == 0xb9 || p[3] == 0xb2 || p[3] == 0xb3))) return 0;
    return 1;
}
static int cw_relative(const wchar_t *p, int leaf) {
    const wchar_t *start = p;
    for (;;) {
        if (*p == L'/' || !*p) {
            if (!cw_component(start, (size_t)(p-start))) return 0;
            if (!*p) return 1;
            if (leaf) return 0;
            start = p + 1;
        }
        ++p;
    }
}
static int cw_final(HANDLE h, wchar_t *out) {
    DWORD n = GetFinalPathNameByHandleW(h, out, CW_PATH, FILE_NAME_NORMALIZED | VOLUME_NAME_DOS);
    return n > 0 && n < CW_PATH;
}
static int cw_append_path(HANDLE parent, const wchar_t *name, wchar_t *path) {
    if (!cw_final(parent, path)) return 0;
    size_t n = wcslen(path), m = wcslen(name);
    if (n + m + 2 >= CW_PATH) return 0;
    if (path[n-1] != L'\\') path[n++] = L'\\';
    memcpy(path+n, name, (m+1)*sizeof *name);
    return 1;
}
static int cw_checked_append(struct cw_cap *c, const wchar_t *path, DWORD access,
        DWORD sharing, DWORD disposition, int directory) {
    if (c->count == CW_DEPTH) return 0;
    HANDLE h = CreateFileW(path, access, sharing, NULL, disposition,
        FILE_FLAG_OPEN_REPARSE_POINT | FILE_FLAG_BACKUP_SEMANTICS |
        (disposition == CREATE_NEW ? FILE_FLAG_WRITE_THROUGH : 0), NULL);
    if (h == INVALID_HANDLE_VALUE) return 0;
    BY_HANDLE_FILE_INFORMATION info;
    wchar_t *actual = (wchar_t *)malloc(CW_PATH * sizeof *actual);
    int good = actual && GetFileInformationByHandle(h, &info) &&
        !(info.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT) &&
        !!(info.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) == directory &&
        GetFileType(h) == FILE_TYPE_DISK && cw_final(h, actual) && !_wcsicmp(path, actual);
    free(actual);
    if (!good) { CloseHandle(h); return 0; }
    c->handles[c->count++] = h;
    return 1;
}
int64_t rt_cache_host_open_root_v1(const uint8_t *p, int64_t n) {
    wchar_t *w = cw_widen(p,n), *path = NULL;
    struct cw_cap *c = NULL;
    int64_t result = -1;
    if (!w) return -1;
    for (wchar_t *t=w; *t; ++t) if (*t == L'/') *t=L'\\';
    wchar_t *root = w;
    if (!wcsncmp(root,L"\\\\?\\",4)) root += 4;
    if (wcslen(root) < 3 || !((root[0]>=L'A'&&root[0]<=L'Z')||(root[0]>=L'a'&&root[0]<=L'z')) ||
            root[1]!=L':' || root[2]!=L'\\') goto done;
    if (wcslen(root)>3 && root[wcslen(root)-1]==L'\\') goto done;
    path=(wchar_t *)calloc(CW_PATH,sizeof *path); c=(struct cw_cap *)calloc(1,sizeof *c);
    if (!path || !c) goto done;
    swprintf(path,CW_PATH,L"\\\\?\\%c:\\",root[0]);
    if (!cw_checked_append(c,path,FILE_READ_ATTRIBUTES,FILE_SHARE_READ|FILE_SHARE_WRITE,OPEN_EXISTING,1)) goto done;
    wchar_t *start=root+3;
    while (*start) {
        wchar_t *end=wcschr(start,L'\\'); if (!end) end=start+wcslen(start);
        if (!cw_component(start,(size_t)(end-start))) goto done;
        wchar_t saved=*end; *end=0;
        int good=cw_append_path(cw_file(c),start,path) &&
            cw_checked_append(c,path,FILE_READ_ATTRIBUTES,FILE_SHARE_READ|FILE_SHARE_WRITE,OPEN_EXISTING,1);
        *end=saved; if (!good) goto done;
        start=saved?end+1:end;
    }
    /* Directory flush needs write access. Its already-retained ancestry and
     * directory deny DELETE sharing, so this final-path reopen cannot swap
     * objects. ReOpenFile itself does not support directory handles. Denial
     * leaves a usable read root whose sync operation honestly fails. */
    if (cw_final(cw_file(c),path))
        (void)cw_checked_append(c,path,GENERIC_READ|GENERIC_WRITE,
            FILE_SHARE_READ|FILE_SHARE_WRITE,OPEN_EXISTING,1);
    AcquireSRWLockExclusive(&cw_lock); result=cw_admit(c,CW_ROOT); c=NULL; ReleaseSRWLockExclusive(&cw_lock);
done:
    cw_free(c); free(path); free(w); return result;
}
int64_t rt_cache_host_open_read_v1(int64_t token,const uint8_t *p,int64_t n) {
    wchar_t *w=cw_widen(p,n), *path=NULL;
    struct cw_cap *c=NULL; int64_t result=-1;
    if (!w || !cw_relative(w,0)) { free(w); return -1; }
    path=(wchar_t *)malloc(CW_PATH*sizeof *path); if (!path) { free(w); return -1; }
    AcquireSRWLockExclusive(&cw_lock);
    struct cw_cap *parent=cw_find(token);
    if (!parent || parent->kind!=CW_ROOT || !(c=cw_clone(parent))) goto done;
    wchar_t *start=w;
    for (;;) {
        wchar_t *end=wcschr(start,L'/'); int directory=end!=NULL;
        if (end) *end=0;
        if (!cw_append_path(cw_file(c),start,path) || !cw_checked_append(c,path,
                directory?FILE_READ_ATTRIBUTES:GENERIC_READ,
                directory?(FILE_SHARE_READ|FILE_SHARE_WRITE):FILE_SHARE_READ,OPEN_EXISTING,directory)) goto done;
        if (!directory) break;
        start=end+1;
    }
    result=cw_admit(c,CW_READ); c=NULL;
done:
    cw_free(c); ReleaseSRWLockExclusive(&cw_lock); free(path); free(w); return result;
}
int64_t rt_cache_host_size_v1(int64_t token,int64_t maximum) {
    if (maximum<0 || maximum>CW_LIMIT) return -1;
    AcquireSRWLockExclusive(&cw_lock); struct cw_cap *c=cw_find(token); LARGE_INTEGER size;
    int64_t result=c && (c->kind==CW_READ || c->kind==CW_SEALED) && GetFileSizeEx(cw_file(c),&size) &&
        size.QuadPart>=0 && size.QuadPart<=maximum ? size.QuadPart : -1;
    ReleaseSRWLockExclusive(&cw_lock); return result;
}
static int cw_read_at(HANDLE h,int64_t off,uint8_t *p,DWORD n) {
    LARGE_INTEGER pos; pos.QuadPart=off; DWORD got=0;
    return SetFilePointerEx(h,pos,NULL,FILE_BEGIN) && ReadFile(h,p,n,&got,NULL) && got==n;
}
int64_t rt_cache_host_pread_receipt_v1(int64_t token,int64_t off,uint8_t *out,int64_t cap) {
    if (!out || off || cap<0 || cap>CW_LIMIT) return -1;
    AcquireSRWLockExclusive(&cw_lock); struct cw_cap *c=cw_find(token);
    int64_t result=-1; BY_HANDLE_FILE_INFORMATION a,b; LARGE_INTEGER size;
    if (!c || (c->kind!=CW_READ && c->kind!=CW_SEALED) || !GetFileInformationByHandle(cw_file(c),&a) ||
            !GetFileSizeEx(cw_file(c),&size) || size.QuadPart<0 || size.QuadPart>cap) goto done;
    DWORD want=(DWORD)size.QuadPart;
    if (!cw_read_at(cw_file(c),0,out,want)) goto done;
    uint8_t verify[4096];
    for (DWORD checked=0; checked<want;) {
        DWORD n=want-checked; if (n>sizeof verify) n=sizeof verify;
        if (!cw_read_at(cw_file(c),checked,verify,n) || memcmp(out+checked,verify,n)) { result=-2; goto done; }
        checked+=n;
    }
    if (!GetFileInformationByHandle(cw_file(c),&b) ||
            a.dwVolumeSerialNumber!=b.dwVolumeSerialNumber || a.nFileIndexHigh!=b.nFileIndexHigh ||
            a.nFileIndexLow!=b.nFileIndexLow || a.nFileSizeHigh!=b.nFileSizeHigh ||
            a.nFileSizeLow!=b.nFileSizeLow || CompareFileTime(&a.ftLastWriteTime,&b.ftLastWriteTime)) result=-2;
    else result=want;
done:
    ReleaseSRWLockExclusive(&cw_lock); return result;
}
static int cw_random(void *out,ULONG n) {
    HMODULE lib=LoadLibraryW(L"advapi32.dll"); if (!lib) return 0;
    typedef BOOLEAN (WINAPI *random_fn)(PVOID,ULONG);
    random_fn random=(random_fn)(void *)GetProcAddress(lib,"SystemFunction036");
    int good=random && random(out,n); FreeLibrary(lib); return good;
}
int64_t rt_cache_host_secure_temp_v1(int64_t token) {
    wchar_t *path=(wchar_t *)malloc(CW_PATH*sizeof *path); if (!path) return -1;
    int64_t result=-1; struct cw_cap *c=NULL;
    AcquireSRWLockExclusive(&cw_lock); struct cw_cap *parent=cw_find(token);
    if (!parent || parent->kind!=CW_ROOT || !(c=cw_clone(parent))) goto done;
    for (int attempt=0; attempt<128; ++attempt) {
        uint64_t random[2]; wchar_t name[80]; if (!cw_random(random,sizeof random)) break;
        swprintf(name,80,L".simple-cache-tmp-%016llx%016llx",(unsigned long long)random[0],(unsigned long long)random[1]);
        if (!cw_append_path(cw_file(c),name,path)) break;
        if (cw_checked_append(c,path,GENERIC_READ|GENERIC_WRITE|DELETE,FILE_SHARE_READ,CREATE_NEW,0)) {
            result=cw_admit(c,CW_TEMP); c=NULL; break;
        }
        if (GetLastError()!=ERROR_FILE_EXISTS && GetLastError()!=ERROR_ALREADY_EXISTS) break;
    }
done:
    cw_free(c); ReleaseSRWLockExclusive(&cw_lock); free(path); return result;
}
int64_t rt_cache_host_write_temp_v1(int64_t token,int64_t off,const uint8_t *p,int64_t n) {
    if (!p || off<0 || n<0 || off>CW_LIMIT || n>CW_LIMIT-off) return -1;
    AcquireSRWLockExclusive(&cw_lock); struct cw_cap *c=cw_find(token); LARGE_INTEGER pos; pos.QuadPart=off; DWORD written;
    int64_t result=c && c->kind==CW_TEMP && !c->sealed && SetFilePointerEx(cw_file(c),pos,NULL,FILE_BEGIN) &&
        WriteFile(cw_file(c),p,(DWORD)n,&written,NULL) ? (int64_t)written : -1;
    ReleaseSRWLockExclusive(&cw_lock); return result;
}
static void cw_unlink_cap(struct cw_cap *c) {
    struct cw_cap **slot=&cw_caps; while (*slot && *slot!=c) slot=&(*slot)->next;
    if (*slot) *slot=c->next;
}
static int64_t cw_publish(int64_t token,const uint8_t *p,int64_t n,int retained) {
    wchar_t *name=cw_widen(p,n), *path=NULL; int64_t result=-1;
    if (!name || !cw_relative(name,1)) { free(name); return -1; }
    path=(wchar_t *)malloc(CW_PATH*sizeof *path); if (!path) { free(name); return -1; }
    AcquireSRWLockExclusive(&cw_lock); struct cw_cap *c=cw_find(token);
    if (!c || c->kind!=CW_TEMP || c->count<2 || !FlushFileBuffers(cw_file(c)) ||
            !cw_append_path(c->handles[c->count-2],name,path)) goto done;
    /* Reserve a distinct capability while the old TEMP token is still live.
     * Failure here leaves the TEMP available for its ordinary cleanup owner. */
    int64_t sealed_token=0;
    if (retained) {
        for (int i=0; i<128; ++i) {
            uint64_t candidate;
            if (!cw_random(&candidate,sizeof candidate)) break;
            candidate &= INT64_MAX;
            if (candidate && !cw_find((int64_t)candidate)) { sealed_token=(int64_t)candidate; break; }
        }
        if (!sealed_token) goto done;
    }
    FILE_BASIC_INFO basic; memset(&basic,0,sizeof basic); basic.FileAttributes=FILE_ATTRIBUTE_READONLY;
    if (!SetFileInformationByHandle(cw_file(c),FileBasicInfo,&basic,sizeof basic)) goto done;
    c->sealed=1;
    size_t bytes=wcslen(path)*sizeof *path;
    FILE_RENAME_INFO *rename=(FILE_RENAME_INFO *)calloc(1,sizeof *rename+bytes);
    if (!rename) goto done;
    rename->ReplaceIfExists=FALSE; rename->RootDirectory=NULL; rename->FileNameLength=(DWORD)bytes;
    memcpy(rename->FileName,path,bytes);
    int good=SetFileInformationByHandle(cw_file(c),FileRenameInfo,rename,(DWORD)(sizeof *rename+bytes));
    DWORD error=GetLastError(); free(rename);
    if (!good) { result=(error==ERROR_ALREADY_EXISTS || error==ERROR_FILE_EXISTS)?0:-1; goto done; }
    /* Flush the renamed file before reporting success. Publication is atomic
     * and no-replace; errors after rename remain errors, never fake success. */
    good=FlushFileBuffers(cw_file(c));
    if (good && retained) {
        /* Same original writer, acquired before sealing: no path reopen and
         * no write surface for the resulting capability. Old TEMP is invalid. */
        c->token=sealed_token; c->kind=CW_SEALED; result=sealed_token;
    } else { cw_unlink_cap(c); cw_free(c); result=good?1:-1; }
done:
    ReleaseSRWLockExclusive(&cw_lock); free(path); free(name); return result;
}
int64_t rt_cache_host_publish_noreplace_v1(int64_t token,const uint8_t *p,int64_t n) {
    return cw_publish(token,p,n,0);
}
int64_t rt_cache_host_publish_retained_noreplace_v2(int64_t token,const uint8_t *p,int64_t n) {
    return cw_publish(token,p,n,1);
}
int64_t rt_cache_host_fsync_v1(int64_t token) {
    AcquireSRWLockExclusive(&cw_lock); struct cw_cap *c=cw_find(token);
    /* Read capabilities intentionally cannot grant write/append access.
     * Windows therefore cannot flush them: preserve Unsupported rather than
     * claiming that a read-only FlushFileBuffers failure is durable success. */
    int64_t result=c && c->kind!=CW_READ && FlushFileBuffers(cw_file(c))?1:-1;
    ReleaseSRWLockExclusive(&cw_lock); return result;
}
int64_t rt_cache_host_close_v1(int64_t token) {
    AcquireSRWLockExclusive(&cw_lock); struct cw_cap *c=cw_find(token);
    if (!c) { ReleaseSRWLockExclusive(&cw_lock); return -1; }
    int64_t result=0;
    if (c->kind==CW_TEMP) {
        FILE_BASIC_INFO basic; memset(&basic,0,sizeof basic); basic.FileAttributes=FILE_ATTRIBUTE_NORMAL;
        FILE_DISPOSITION_INFO disposition; disposition.DeleteFile=TRUE;
        if (!SetFileInformationByHandle(cw_file(c),FileBasicInfo,&basic,sizeof basic) ||
                !SetFileInformationByHandle(cw_file(c),FileDispositionInfo,&disposition,sizeof disposition)) result=-1;
    }
    cw_unlink_cap(c); cw_free(c); ReleaseSRWLockExclusive(&cw_lock); return result;
}
#define UNSUPPORTED(name, args) int64_t name args { return -1; }
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
UNSUPPORTED(rt_cache_host_quarantine_v1, (int64_t r, int64_t o, const uint8_t *p, int64_t n))
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

/* Apple spells the POSIX-2008 nanosecond stat members st_mtimespec/st_ctimespec. */
#if defined(__APPLE__)
#define SPL_STAT_MTIM_NSEC(s) ((s).st_mtimespec.tv_nsec)
#define SPL_STAT_CTIM_NSEC(s) ((s).st_ctimespec.tv_nsec)
#else
#define SPL_STAT_MTIM_NSEC(s) ((s).st_mtim.tv_nsec)
#define SPL_STAT_CTIM_NSEC(s) ((s).st_ctim.tv_nsec)
#endif

enum cache_cap_kind { CAP_ROOT=1, CAP_DIR=2, CAP_READ=3, CAP_TEMP=4, CAP_CAS_ROOT=5, CAP_CAS_KIND=6, CAP_CAS_SHARD1=7, CAP_CAS_SHARD2=8, CAP_TEMP_CAS=9, CAP_SEALED=10 };
struct cache_cap { int64_t token; int fd; int parent_fd; enum cache_cap_kind kind; int sealed; char temp_name[96]; struct cache_cap *next; };
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
int64_t rt_cache_host_size_v1(int64_t h,int64_t maximum){if(maximum<0||maximum>67108864)return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);struct stat s;int64_t result=(!c||(c->kind!=CAP_READ&&c->kind!=CAP_SEALED)||fstat(c->fd,&s)||(s.st_mode&S_IFMT)!=S_IFREG||s.st_size<0||s.st_size>maximum)?-1:(int64_t)s.st_size;pthread_mutex_unlock(&caps_lock);return result;}
int64_t rt_cache_host_pread_receipt_v1(int64_t h,int64_t off,uint8_t*out,int64_t cap){if(!out||off||cap<0||cap>67108864)return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);if(!c||(c->kind!=CAP_READ&&c->kind!=CAP_SEALED)){pthread_mutex_unlock(&caps_lock);return-1;}struct stat a,b;if(fstat(c->fd,&a)||(a.st_mode&S_IFMT)!=S_IFREG||a.st_size<0||a.st_size>cap){pthread_mutex_unlock(&caps_lock);return-1;}size_t got=0,want=(size_t)a.st_size;while(got<want){ssize_t n=pread(c->fd,out+got,want-got,(off_t)got);if(n<=0){pthread_mutex_unlock(&caps_lock);return-1;}got+=(size_t)n;}uint8_t verify[4096];size_t checked=0;while(checked<want){size_t n=want-checked<sizeof verify?want-checked:sizeof verify;if(pread(c->fd,verify,n,(off_t)checked)!=(ssize_t)n||memcmp(out+checked,verify,n)){pthread_mutex_unlock(&caps_lock);return-2;}checked+=n;}int bad=fstat(c->fd,&b)||a.st_dev!=b.st_dev||a.st_ino!=b.st_ino||a.st_size!=b.st_size||SPL_STAT_MTIM_NSEC(a)!=SPL_STAT_MTIM_NSEC(b)||SPL_STAT_CTIM_NSEC(a)!=SPL_STAT_CTIM_NSEC(b)||a.st_mtime!=b.st_mtime||a.st_ctime!=b.st_ctime;pthread_mutex_unlock(&caps_lock);return bad?-2:(int64_t)want;}
int64_t rt_cache_host_secure_temp_v1(int64_t h){pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);if(!c||(c->kind!=CAP_ROOT&&c->kind!=CAP_DIR&&c->kind!=CAP_CAS_SHARD2)){pthread_mutex_unlock(&caps_lock);return-1;}int temp_kind=c->kind==CAP_CAS_SHARD2?CAP_TEMP_CAS:CAP_TEMP;int parent=fcntl(c->fd,F_DUPFD_CLOEXEC,3);pthread_mutex_unlock(&caps_lock);if(parent<0)return-1;for(int i=0;i<128;i++){char name[96];snprintf(name,sizeof name,".simple-cache-tmp-%ld-%lld",(long)getpid(),(long long)random_token());int fd=openat(parent,name,O_RDWR|O_CREAT|O_EXCL|O_NOFOLLOW|O_CLOEXEC,0600);if(fd>=0)return add_cap((enum cache_cap_kind)temp_kind,fd,parent,name);if(errno!=EEXIST)break;}close(parent);return-1;}
int64_t rt_cache_host_write_temp_v1(int64_t h,int64_t off,const uint8_t*p,int64_t n){if(!p||off<0||n<0||n>67108864)return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);ssize_t rc=(!c||c->sealed||(c->kind!=CAP_TEMP&&c->kind!=CAP_TEMP_CAS))?-1:pwrite(c->fd,p,(size_t)n,(off_t)off);pthread_mutex_unlock(&caps_lock);return rc;}
int64_t rt_cache_host_publish_noreplace_v1(int64_t h,const uint8_t*p,int64_t n){char dest[32769];if(!copy_name(p,n,dest)||!valid_relative(dest)||strchr(dest,'/'))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);if(!c||(c->kind!=CAP_TEMP&&c->kind!=CAP_TEMP_CAS)||(c->kind==CAP_TEMP_CAS&&!lower_hex_n(dest,60))||fsync(c->fd)||fchmod(c->fd,0444)){pthread_mutex_unlock(&caps_lock);return-1;}
#ifdef __linux__
int rc=(int)syscall(SYS_renameat2,c->parent_fd,c->temp_name,c->parent_fd,dest,RENAME_NOREPLACE);
#else
int rc=linkat(c->parent_fd,c->temp_name,c->parent_fd,dest,0);if(!rc)unlinkat(c->parent_fd,c->temp_name,0);
#endif
if(rc){int e=errno;pthread_mutex_unlock(&caps_lock);return e==EEXIST?0:-1;}fsync(c->parent_fd);struct cache_cap**slot=&caps;while(*slot&&*slot!=c)slot=&(*slot)->next;if(*slot)*slot=c->next;close(c->fd);close(c->parent_fd);free(c);pthread_mutex_unlock(&caps_lock);return 1;}
/* Retained original descriptor; destination-name observation is fail-closed,
 * not an atomic conditional rename or a cross-process directory lock. */
int64_t rt_cache_host_publish_retained_noreplace_v2(int64_t h,const uint8_t *p,int64_t n) {
    char dest[32769]; int64_t result=-1, token=-1; struct stat original,published;
    if (!copy_name(p,n,dest)||!valid_relative(dest)||strchr(dest,'/')) return -1;
    pthread_mutex_lock(&caps_lock); struct cache_cap *c=find_cap(h);
    if (!c||(c->kind!=CAP_TEMP&&c->kind!=CAP_TEMP_CAS)||
            (c->kind==CAP_TEMP_CAS&&!lower_hex_n(dest,60))||
            fstat(c->fd,&original)||(original.st_mode&S_IFMT)!=S_IFREG) goto done;
    for (int i=0;i<128;++i) { int64_t candidate=random_token();
        if (candidate>0&&!find_cap(candidate)) { token=candidate; break; } }
    if (token<0||fsync(c->fd)||fchmod(c->fd,0444)) goto done;
    c->sealed=1;
#ifdef __linux__
    int rc=(int)syscall(SYS_renameat2,c->parent_fd,c->temp_name,c->parent_fd,dest,RENAME_NOREPLACE);
#else
    int rc=linkat(c->parent_fd,c->temp_name,c->parent_fd,dest,0);
#endif
    if (rc) { result=errno==EEXIST?0:-1; goto done; }
#ifdef __linux__
    int removed_temp=1;
#else
    int removed_temp=unlinkat(c->parent_fd,c->temp_name,0)==0;
#endif
    int good=removed_temp&&!fstatat(c->parent_fd,dest,&published,AT_SYMLINK_NOFOLLOW)&&
        (published.st_mode&S_IFMT)==S_IFREG&&original.st_dev==published.st_dev&&
        original.st_ino==published.st_ino&&!fsync(c->fd)&&!fsync(c->parent_fd);
    if (good) { c->token=token; c->kind=CAP_SEALED; c->temp_name[0]=0; result=token; }
    else {
        struct cache_cap **slot=&caps; while (*slot&&*slot!=c) slot=&(*slot)->next;
        if (*slot) *slot=c->next;
        close(c->fd); close(c->parent_fd); free(c);
    }
 done:
    pthread_mutex_unlock(&caps_lock); return result;
}
int64_t rt_cache_host_quarantine_v1(int64_t r,int64_t o,const uint8_t*p,int64_t n){
#ifndef __linux__
(void)r;(void)o;(void)p;(void)n;return-1;
#else
char dest[32769];if(!copy_name(p,n,dest)||!valid_relative(dest)||strchr(dest,'/'))return-1;pthread_mutex_lock(&caps_lock);struct cache_cap*root=find_cap(r),*obj=find_cap(o);if(!root||!obj||(root->kind!=CAP_ROOT&&root->kind!=CAP_DIR)||obj->kind!=CAP_READ){pthread_mutex_unlock(&caps_lock);return-1;}int rc=linkat(obj->fd,"",root->fd,dest,AT_EMPTY_PATH);int e=errno;if(!rc)fsync(root->fd);pthread_mutex_unlock(&caps_lock);return rc?(e==EEXIST?0:-1):1;
#endif
}
int64_t rt_cache_host_fsync_v1(int64_t h){pthread_mutex_lock(&caps_lock);struct cache_cap*c=find_cap(h);int rc=c?fsync(c->fd):-1;pthread_mutex_unlock(&caps_lock);return rc?-1:1;}
int64_t rt_cache_host_close_v1(int64_t h){pthread_mutex_lock(&caps_lock);struct cache_cap**p=&caps,*c=NULL;while(*p){if((*p)->token==h){c=*p;*p=c->next;break;}p=&(*p)->next;}pthread_mutex_unlock(&caps_lock);if(!c)return-1;if(c->kind==CAP_TEMP||c->kind==CAP_TEMP_CAS){unlinkat(c->parent_fd,c->temp_name,0);close(c->parent_fd);}else if(c->kind==CAP_SEALED){close(c->parent_fd);}int rc=close(c->fd);free(c);return rc;}
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
