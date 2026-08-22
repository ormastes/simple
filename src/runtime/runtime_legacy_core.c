/*
 * Minimal legacy spl_* support for the core-C runtime lane.
 *
 * The bootstrap runtime.c contains a broad compatibility surface. Tiny native
 * binaries should not need that whole object, but runtime_native.c still has
 * optional bridge functions that reference a small legacy SplValue API. Keep
 * those references real so the linker never has to synthesize stubs.
 */

#include "runtime.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#if defined(_WIN32)
#include <direct.h>
#include <io.h>
#include <process.h>
#include <windows.h>
#else
#include <dirent.h>
#include <signal.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>
#endif

int64_t rt_getpid(void) {
#if defined(_WIN32)
    return (int64_t)_getpid();
#else
    return (int64_t)getpid();
#endif
}

int64_t rt_thread_available_parallelism(void) {
#if defined(_WIN32)
    SYSTEM_INFO info;
    GetSystemInfo(&info);
    return info.dwNumberOfProcessors > 0 ? (int64_t)info.dwNumberOfProcessors : 1;
#else
    long count = sysconf(_SC_NPROCESSORS_ONLN);
    return count > 0 ? (int64_t)count : 1;
#endif
}

int64_t rt_munmap_raw(int64_t addr, int64_t length) {
#if defined(_WIN32)
    (void)length;
    if (!addr) return -1;
    return VirtualFree((void*)(uintptr_t)addr, 0, MEM_RELEASE) ? 0 : -1;
#else
    return (int64_t)munmap((void*)(uintptr_t)addr, (size_t)length);
#endif
}

int64_t rt_mprotect(int64_t addr, int64_t length, int64_t prot) {
#if defined(_WIN32)
    DWORD protect = PAGE_READWRITE;
    if (prot == 0x1) protect = PAGE_READONLY;
    else if (prot == 0x5) protect = PAGE_EXECUTE_READ;
    else if (prot == 0x7) protect = PAGE_EXECUTE_READWRITE;
    DWORD old_protect;
    return VirtualProtect((void*)(uintptr_t)addr, (SIZE_T)length, protect, &old_protect) ? 0 : -1;
#else
    return (int64_t)mprotect((void*)(uintptr_t)addr, (size_t)length, (int)prot);
#endif
}

int64_t spl_thread_cpu_count(void) {
    return rt_thread_available_parallelism();
}

static SplValue spl_value_nil(void) {
    SplValue v;
    memset(&v, 0, sizeof(v));
    v.tag = SPL_NIL;
    return v;
}

SplValue spl_int(int64_t n) {
    SplValue v = spl_value_nil();
    v.tag = SPL_INT;
    v.as_int = n;
    return v;
}

SplValue spl_str(const char* s) {
    SplValue v = spl_value_nil();
    v.tag = SPL_STRING;
    v.as_str = spl_str_new(s ? s : "");
    return v;
}

const char* spl_as_str(SplValue v) {
    return v.tag == SPL_STRING && v.as_str ? v.as_str : "";
}

#if defined(_WIN32)
static void core_dir_walk_impl(const char* path, int64_t* result) {
    char pattern[4096];
    snprintf(pattern, sizeof(pattern), "%s\\*", path);
    WIN32_FIND_DATAA entry;
    HANDLE handle = FindFirstFileA(pattern, &entry);
    if (handle == INVALID_HANDLE_VALUE) return;
    do {
        if (strcmp(entry.cFileName, ".") == 0 || strcmp(entry.cFileName, "..") == 0) continue;
        char full[4096];
        snprintf(full, sizeof(full), "%s\\%s", path, entry.cFileName);
        if ((entry.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) &&
            !(entry.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT)) {
            core_dir_walk_impl(full, result);
        } else {
            rt_array_push((SplArray*)(uintptr_t)*result,
                          rt_string_new((const uint8_t*)full, (uint64_t)strlen(full)));
        }
    } while (FindNextFileA(handle, &entry));
    FindClose(handle);
}
#else
static void core_dir_walk_impl(const char* path, int64_t* result) {
    DIR* dir = opendir(path);
    if (!dir) return;
    struct dirent* entry;
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) continue;
        char full[4096];
        snprintf(full, sizeof(full), "%s/%s", path, entry->d_name);
        struct stat metadata;
        if (lstat(full, &metadata) != 0) continue;
        if (S_ISDIR(metadata.st_mode)) {
            core_dir_walk_impl(full, result);
        } else {
            rt_array_push((SplArray*)(uintptr_t)*result,
                          rt_string_new((const uint8_t*)full, (uint64_t)strlen(full)));
        }
    }
    closedir(dir);
}
#endif

/* (ptr, len): the compiler's `text` extern ABI (runtime_sffi.rs:1896 declares
 * &[I64, I64]). A Simple `text` is not NUL-terminated. */
/* -> RuntimeValue (array of text), per runtime_sffi.rs:1896. Used to return
 * the legacy spl_array_new() representation as a bare untagged address; see the
 * sibling in runtime.c for the reproduction and the revert-proof. */
int64_t rt_dir_walk(const uint8_t* path_ptr, uint64_t path_len) {
    int64_t result = (int64_t)(uintptr_t)rt_array_new(0);
    char path[4096];
    if (!path_ptr && path_len != 0) return result;
    if (path_len >= sizeof(path)) return result;
    if (path_len != 0) memcpy(path, path_ptr, (size_t)path_len);
    path[(size_t)path_len] = '\0';
    if (path[0]) core_dir_walk_impl(path, &result);
    return result;
}

char* spl_strdup(const char* s) {
    return spl_str_new(s);
}

char* spl_str_new(const char* s) {
    if (!s) s = "";
    size_t len = strlen(s);
    char* out = (char*)malloc(len + 1);
    if (!out) return NULL;
    memcpy(out, s, len + 1);
    return out;
}

int64_t spl_str_len(const char* s) {
    return s ? (int64_t)strlen(s) : 0;
}

int spl_str_cmp(const char* a, const char* b) {
    return strcmp(a ? a : "", b ? b : "");
}

char* spl_str_concat(const char* a, const char* b) {
    if (!a) a = "";
    if (!b) b = "";
    size_t alen = strlen(a);
    size_t blen = strlen(b);
    char* out = (char*)malloc(alen + blen + 1);
    if (!out) return NULL;
    memcpy(out, a, alen);
    memcpy(out + alen, b, blen + 1);
    return out;
}

char* spl_str_slice(const char* s, int64_t start, int64_t end) {
    if (!s) return spl_str_new("");
    int64_t len = (int64_t)strlen(s);
    if (start < 0) start = 0;
    if (end < start) end = start;
    if (end > len) end = len;
    if (start > len) start = len;
    int64_t out_len = end - start;
    char* out = (char*)malloc((size_t)out_len + 1);
    if (!out) return NULL;
    memcpy(out, s + start, (size_t)out_len);
    out[out_len] = '\0';
    /* UTF-8 slice audit, stage 1 (COUNTING ONLY, default off). See
     * runtime_simd_utf8.c -- records a mid-codepoint boundary, never fails. */
    if (rt_text_slice_audit_level() != 0) {
        rt_text_slice_audit_note(RT_TEXT_SLICE_SITE_SPL_LEGACY, "spl_str_slice_legacy",
                                 start, end,
                                 (const uint8_t*)s, (uint64_t)len,
                                 (const uint8_t*)out, (uint64_t)out_len);
    }
    return out;
}

int64_t spl_str_index_of(const char* s, const char* needle) {
    if (!s || !needle) return -1;
    char* found = strstr(s, needle);
    return found ? (int64_t)(found - s) : -1;
}

char* spl_str_replace(const char* s, const char* old_s, const char* new_s) {
    if (!s) return spl_str_new("");
    if (!old_s || !*old_s) return spl_str_new(s);
    if (!new_s) new_s = "";
    const char* hit = strstr(s, old_s);
    if (!hit) return spl_str_new(s);
    size_t before = (size_t)(hit - s);
    size_t old_len = strlen(old_s);
    size_t new_len = strlen(new_s);
    size_t after = strlen(hit + old_len);
    char* out = (char*)malloc(before + new_len + after + 1);
    if (!out) return NULL;
    memcpy(out, s, before);
    memcpy(out + before, new_s, new_len);
    memcpy(out + before + new_len, hit + old_len, after + 1);
    return out;
}

uint64_t spl_str_hash(const char* s) {
    uint64_t hash = 1469598103934665603ULL;
    if (!s) return hash;
    while (*s) {
        hash ^= (unsigned char)*s++;
        hash *= 1099511628211ULL;
    }
    return hash;
}

int64_t rt_str_hash(const char* s) {
    return (int64_t)spl_str_hash(s);
}

SplArray* spl_array_new_cap(int64_t cap) {
    if (cap < 1) cap = 4;
    SplArray* a = (SplArray*)calloc(1, sizeof(SplArray));
    if (!a) return NULL;
    a->items = (SplValue*)calloc((size_t)cap, sizeof(SplValue));
    if (!a->items) {
        free(a);
        return NULL;
    }
    a->cap = cap;
    return a;
}

SplArray* spl_array_new(void) {
    return spl_array_new_cap(4);
}

SplArray* spl_array_push(SplArray* a, SplValue v) {
    if (!a) a = spl_array_new();
    if (!a) return NULL;
    if (a->len >= a->cap) {
        int64_t next_cap = a->cap < 1 ? 4 : a->cap * 2;
        SplValue* next = (SplValue*)realloc(a->items, (size_t)next_cap * sizeof(SplValue));
        if (!next) return a;
        memset(next + a->cap, 0, (size_t)(next_cap - a->cap) * sizeof(SplValue));
        a->items = next;
        a->cap = next_cap;
    }
    a->items[a->len++] = v;
    return a;
}

void spl_array_push_i64(SplArray* a, int64_t n) {
    spl_array_push(a, spl_int(n));
}

SplValue spl_array_get(SplArray* a, int64_t idx) {
    if (!a || idx < 0 || idx >= a->len) return spl_value_nil();
    return a->items[idx];
}

int64_t spl_array_len(SplArray* a) {
    return a ? a->len : 0;
}

SplValue spl_array_pop(SplArray* a) {
    if (!a || a->len <= 0) return spl_value_nil();
    return a->items[--a->len];
}

SplArray* spl_str_split(const char* s, const char* delim) {
    SplArray* out = spl_array_new();
    if (!s) return out;
    if (!delim || !*delim) {
        spl_array_push(out, spl_str(s));
        return out;
    }
    size_t delim_len = strlen(delim);
    const char* start = s;
    const char* hit = NULL;
    while ((hit = strstr(start, delim)) != NULL) {
        char* part = spl_str_slice(start, 0, (int64_t)(hit - start));
        spl_array_push(out, spl_str(part));
        free(part);
        start = hit + delim_len;
    }
    spl_array_push(out, spl_str(start));
    return out;
}

SplDict* spl_dict_new(void) {
    return (SplDict*)calloc(1, sizeof(SplDict));
}

void spl_dict_set(SplDict* d, const char* key, SplValue value) {
    (void)d;
    (void)key;
    (void)value;
}

SplValue spl_dict_get(SplDict* d, const char* key) {
    (void)d;
    (void)key;
    return spl_value_nil();
}

int spl_dict_contains(SplDict* d, const char* key) {
    (void)d;
    (void)key;
    return 0;
}

int64_t spl_dict_len(SplDict* d) {
    return d ? d->len : 0;
}

void spl_print(const char* s) {
    fputs(s ? s : "", stdout);
}

void spl_println(const char* s) {
    fputs(s ? s : "", stdout);
    fputc('\n', stdout);
}

/* stderr sibling of spl_println. rt_eprintln (runtime_native.c) calls this
   since f858c7cf32e; runtime.c defines it too but is not a core-C archive
   member, so the core-C lane must provide it here beside spl_print/spl_println
   or every native link referencing eprint fails on spl_eprintln. */
void spl_eprintln(const char* s) {
    fputs(s ? s : "", stderr);
    fputc('\n', stderr);
}
void spl_panic(const char* msg) {
    fprintf(stderr, "panic: %s\n", msg ? msg : "");
    exit(1);
}

char* spl_file_read(const char* path) {
    if (!path) return spl_str_new("");
    FILE* f = fopen(path, "rb");
    if (!f) return spl_str_new("");
    /* Do NOT size the buffer from fseek(SEEK_END)/ftell(): pseudo-filesystems
     * (procfs, sysfs, etc.) report length 0 for files that generate content
     * on read, so a stat/seek-sized buffer reads zero bytes and silently
     * "succeeds" with an empty string instead of the real content (e.g.
     * spl_file_read("/proc/meminfo") always returned "" rather than the
     * meminfo text). Read to EOF into a growable buffer instead. */
    size_t cap = 4096;
    size_t len = 0;
    char* out = (char*)malloc(cap);
    if (!out) {
        fclose(f);
        return NULL;
    }
    for (;;) {
        if (len >= cap - 1) {
            size_t new_cap = cap * 2;
            char* new_out = (char*)realloc(out, new_cap);
            if (!new_out) {
                free(out);
                fclose(f);
                return NULL;
            }
            out = new_out;
            cap = new_cap;
        }
        size_t n = fread(out + len, 1, cap - 1 - len, f);
        len += n;
        if (n == 0) break;
    }
    fclose(f);
    out[len] = '\0';
    return out;
}

int rt_file_write(const char* path, const char* content) {
    FILE* f = path ? fopen(path, "wb") : NULL;
    if (!f) return 0;
    if (!content) content = "";
    size_t len = strlen(content);
    size_t n = fwrite(content, 1, len, f);
    fclose(f);
    return n == len ? 1 : 0;
}

int rt_file_append(const char* path, const char* content) {
    FILE* f = path ? fopen(path, "ab") : NULL;
    if (!f) return 0;
    if (!content) content = "";
    size_t len = strlen(content);
    size_t n = fwrite(content, 1, len, f);
    fclose(f);
    return n == len ? 1 : 0;
}

/* This copy had the right ARITY (2), so the extern ABI signature gate never
 * flagged it -- but it did `(void)path_len;` and used the pointer as a C
 * string, carrying the same non-NUL-terminated-`text` defect invisibly. Same
 * shape as the runtime.c copy. */
int rt_file_sync(const uint8_t* path_ptr, uint64_t path_len) {
    char path[4096];
    if (!path_ptr || path_len == 0 || path_len >= sizeof(path)) return 0;
    memcpy(path, path_ptr, (size_t)path_len);
    path[(size_t)path_len] = '\0';
    FILE* f = fopen(path, "rb");
    if (!f) return 0;
#if defined(_WIN32)
    int ok = _commit(_fileno(f)) == 0;
#else
    int ok = fsync(fileno(f)) == 0;
#endif
    fclose(f);
    return ok ? 1 : 0;
}

int64_t rt_crc32_text(const char* text, int64_t text_len) {
    if (!text || text_len <= 0) return 0;
    uint32_t crc = 0xFFFFFFFFU;
    const unsigned char* p = (const unsigned char*)text;
    for (int64_t i = 0; i < text_len; i++) {
        crc ^= p[i];
        for (int i = 0; i < 8; i++) crc = (crc >> 1) ^ (0xEDB88320U & -(crc & 1U));
    }
    return (int64_t)(crc ^ 0xFFFFFFFFU);
}

int rt_file_create_excl(const char* path, int64_t path_len,
                        const char* content, int64_t content_len) {
    if (!path || path_len <= 0 || (uint64_t)path_len >= SIZE_MAX ||
        memchr(path, '\0', (size_t)path_len) != NULL || content_len < 0 ||
        (content_len > 0 && !content)) return 0;
    char* path_copy = (char*)malloc((size_t)path_len + 1);
    if (!path_copy) return 0;
    memcpy(path_copy, path, (size_t)path_len);
    path_copy[path_len] = '\0';
    FILE* f = fopen(path_copy, "wx");
    if (!f) {
        free(path_copy);
        return 0;
    }
    size_t len = content && content_len > 0 ? (size_t)content_len : 0;
    int write_ok = fwrite(content ? content : "", 1, len, f) == len;
    int close_ok = fclose(f) == 0;
    if (!write_ok || !close_ok) {
        remove(path_copy);
        free(path_copy);
        return 0;
    }
    free(path_copy);
    return 1;
}

#if !defined(_WIN32) && !defined(__simpleos__)
static int rt_mem_snapshot_parent_fd(char* path, const char** leaf_out) {
    char* leaf = strrchr(path, '/'); int parent_fd;
    if (!leaf) { *leaf_out = path; return open(".", O_RDONLY | O_DIRECTORY | O_CLOEXEC); }
    *leaf++ = '\0';
    if (*leaf == '\0' || !strcmp(leaf, ".") || !strcmp(leaf, "..")) return -1;
    *leaf_out = leaf;
    parent_fd = open(path[0] == '\0' ? "/" : (path[0] == '/' ? "/" : "."), O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (parent_fd < 0) return -1;
    char* walk = path[0] == '/' ? path + 1 : path; char* save = NULL;
    for (char* part = strtok_r(walk, "/", &save); part; part = strtok_r(NULL, "/", &save)) {
        if (!strcmp(part, ".")) continue;
        if (!strcmp(part, "..")) { close(parent_fd); return -1; }
        int next = openat(parent_fd, part, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
        if (next < 0) { close(parent_fd); return -1; }
        close(parent_fd); parent_fd = next;
    }
    return parent_fd;
}
#endif
int64_t rt_mem_snapshot_open(const char* path_ptr, int64_t path_len) {
#if defined(_WIN32) || defined(__simpleos__)
    /* SimpleOS lacks secure openat path-walk authority; fail closed. */
    (void)path_ptr; (void)path_len; return -1;
#else
    char path[4096];
    if (!path_ptr || path_len <= 0 || path_len >= (int64_t)sizeof(path) ||
        memchr(path_ptr, '\0', (size_t)path_len)) return -1;
    memcpy(path, path_ptr, (size_t)path_len); path[path_len] = '\0';
    const char* leaf = NULL; int parent_fd = rt_mem_snapshot_parent_fd(path, &leaf);
    if (parent_fd < 0) return -1;
    int flags = O_WRONLY | O_CREAT | O_EXCL | O_APPEND;
#ifdef O_NOFOLLOW
    flags |= O_NOFOLLOW;
#endif
#ifdef O_CLOEXEC
    flags |= O_CLOEXEC;
#endif
    int fd = openat(parent_fd, leaf, flags, 0600); struct stat opened;
    close(parent_fd);
    if (fd < 0) return -1;
    if (fstat(fd, &opened) != 0 || !S_ISREG(opened.st_mode)) { close(fd); return -1; }
    return fd;
#endif
}

static int rt_mem_snapshot_append_flush_raw(int64_t fd64, const char* record, int64_t len) {
#if defined(_WIN32)
    (void)fd64; (void)record; (void)len; return 0;
#else
    if (fd64 < 0 || fd64 > INT_MAX || !record || len <= 0 || record[len - 1] != '\n') return 0;
    int64_t off = 0;
    while (off < len) { ssize_t n = write((int)fd64, record + off, (size_t)(len - off)); if (n <= 0) return 0; off += n; }
    return fsync((int)fd64) == 0;
#endif
}

int rt_mem_snapshot_append_flush(int64_t fd, const char* record, int64_t len) {
    return rt_mem_snapshot_append_flush_raw(fd, record, len);
}

static int rt_mem_snapshot_token(char* out, size_t cap, const char* in, int64_t len) {
    size_t used = 0; static const char hex[] = "0123456789ABCDEF";
    if (len < 0 || (len > 0 && !in)) return -1;
    for (int64_t i = 0; i < len; ++i) {
        unsigned char c = (unsigned char)in[i];
        if (c == '%' || c == ' ' || c == '=' || c == '\n' || c == '\r') {
            if (used + 3 >= cap) return -1;
            out[used++] = '%'; out[used++] = hex[c >> 4]; out[used++] = hex[c & 15];
        } else { if (used + 1 >= cap) return -1; out[used++] = (char)c; }
    }
    out[used] = '\0'; return (int)used;
}

static int64_t rt_mem_snapshot_status_kib(const char* key) {
    FILE* f = fopen("/proc/self/status", "r"); if (!f) return -1;
    char line[256]; int64_t value = -1;
    while (fgets(line, sizeof(line), f)) if (strncmp(line, key, strlen(key)) == 0) { value = strtoll(line + strlen(key), NULL, 10); break; }
    fclose(f); return value;
}
int64_t rt_process_rss_kib(void) { return rt_mem_snapshot_status_kib("VmRSS:"); }
int64_t rt_process_hwm_kib(void) { return rt_mem_snapshot_status_kib("VmHWM:"); }

int rt_mem_snapshot_record(int64_t fd, int64_t seq,
        const char* event, int64_t event_len, const char* phase, int64_t phase_len,
        int64_t source_index, const char* path, int64_t path_len,
        int64_t retained, int64_t keys, int64_t values, int64_t traits,
        int64_t names, int64_t symbols, int64_t functions, int64_t constants,
        int64_t enums, int64_t structs, int64_t classes) {
    char run[128], e[64], p[4096], sp[4096], line[9216];
    const char* run_id = getenv("SIMPLE_EVIDENCE_RUN_ID");
    if (!run_id || !*run_id) run_id = "none";
    if (rt_mem_snapshot_token(run, sizeof(run), run_id, (int64_t)strlen(run_id)) < 0 ||
        rt_mem_snapshot_token(e, sizeof(e), event, event_len) < 0 ||
        rt_mem_snapshot_token(p, sizeof(p), phase, phase_len) < 0 ||
        rt_mem_snapshot_token(sp, sizeof(sp), path, path_len) < 0) return 0;
    int n = snprintf(line, sizeof(line), "schema=simple.compiler.mem_snapshot.v1 run_id=%s seq=%lld pid=%lld monotonic_ms=%lld event=%s phase=%s source_index=%lld source_path_kind=%s source_path=%s retained_modules=%lld validation_keys=%lld validation_values=%lld shared_traits=%lld hir_names=%lld hir_symbols=%lld hir_functions=%lld hir_constants=%lld hir_enums=%lld hir_structs=%lld hir_classes=%lld heap_live_bytes=%lld heap_peak_bytes=%lld rss_kib=%lld hwm_kib=%lld\n",
        run, (long long)seq, (long long)rt_getpid(), (long long)rt_time_now_monotonic_ms(), e, p,
        (long long)source_index, path_len > 0 ? "recorded" : "none", path_len > 0 ? sp : "-",
        (long long)retained, (long long)keys, (long long)values, (long long)traits,
        (long long)names, (long long)symbols, (long long)functions, (long long)constants,
        (long long)enums, (long long)structs, (long long)classes,
        (long long)rt_heap_live_bytes(), (long long)rt_heap_peak_bytes(),
        (long long)rt_process_rss_kib(), (long long)rt_process_hwm_kib());
    return n > 0 && n < (int)sizeof(line) && rt_mem_snapshot_append_flush_raw(fd, line, n);
}

int rt_mem_snapshot_close(int64_t fd) {
#if defined(_WIN32)
    (void)fd; return 0;
#else
    return fd >= 0 && fd <= INT_MAX && close((int)fd) == 0;
#endif
}

bool rt_is_dir(const char* path) {
#if defined(_WIN32)
    DWORD attributes = path ? GetFileAttributesA(path) : INVALID_FILE_ATTRIBUTES;
    return attributes != INVALID_FILE_ATTRIBUTES && (attributes & FILE_ATTRIBUTE_DIRECTORY) != 0;
#else
    struct stat st;
    return path && stat(path, &st) == 0 && S_ISDIR(st.st_mode);
#endif
}

#if defined(_WIN32)
static bool core_dir_remove_all_impl(const char* path) {
    DWORD attributes = GetFileAttributesA(path);
    if (attributes == INVALID_FILE_ATTRIBUTES) {
        DWORD error = GetLastError();
        return error == ERROR_FILE_NOT_FOUND || error == ERROR_PATH_NOT_FOUND;
    }
    if ((attributes & FILE_ATTRIBUTE_DIRECTORY) == 0) return DeleteFileA(path) != 0;
    if ((attributes & FILE_ATTRIBUTE_REPARSE_POINT) != 0) return RemoveDirectoryA(path) != 0;

    char pattern[4096];
    int pattern_len = snprintf(pattern, sizeof(pattern), "%s\\*", path);
    if (pattern_len < 0 || (size_t)pattern_len >= sizeof(pattern)) return false;
    WIN32_FIND_DATAA entry;
    HANDLE handle = FindFirstFileA(pattern, &entry);
    if (handle != INVALID_HANDLE_VALUE) {
        do {
            if (strcmp(entry.cFileName, ".") == 0 || strcmp(entry.cFileName, "..") == 0) continue;
            char child[4096];
            int child_len = snprintf(child, sizeof(child), "%s\\%s", path, entry.cFileName);
            if (child_len < 0 || (size_t)child_len >= sizeof(child) || !core_dir_remove_all_impl(child)) {
                FindClose(handle);
                return false;
            }
        } while (FindNextFileA(handle, &entry));
        DWORD find_error = GetLastError();
        FindClose(handle);
        if (find_error != ERROR_NO_MORE_FILES) return false;
    } else if (GetLastError() != ERROR_FILE_NOT_FOUND) {
        return false;
    }
    return RemoveDirectoryA(path) != 0;
}
#else
static bool core_dir_remove_all_impl(const char* path) {
    struct stat metadata;
    if (lstat(path, &metadata) != 0) return errno == ENOENT;
    if (!S_ISDIR(metadata.st_mode) || S_ISLNK(metadata.st_mode)) return unlink(path) == 0;

    DIR* dir = opendir(path);
    if (!dir) return false;
    struct dirent* entry;
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) continue;
        char child[4096];
        int child_len = snprintf(child, sizeof(child), "%s/%s", path, entry->d_name);
        if (child_len < 0 || (size_t)child_len >= sizeof(child) || !core_dir_remove_all_impl(child)) {
            closedir(dir);
            return false;
        }
    }
    if (closedir(dir) != 0) return false;
    return rmdir(path) == 0;
}
#endif

/* (ptr, len): runtime_sffi.rs:1890 declares &[I64, I64]. Deleting a tree with
 * a path read past its end is the highest-consequence member of this family --
 * a truncated or extended path removes the wrong directory. */
bool rt_dir_remove_all(const uint8_t* path_ptr, uint64_t path_len) {
    char path[4096];
    if (!path_ptr || path_len == 0) return false;
    if (path_len >= sizeof(path)) return false;
    memcpy(path, path_ptr, (size_t)path_len);
    path[(size_t)path_len] = '\0';
    return core_dir_remove_all_impl(path);
}

char* rt_getcwd(void) {
    char buf[4096];
#if defined(_WIN32)
    if (!_getcwd(buf, sizeof(buf))) return spl_str_new("");
#else
    if (!getcwd(buf, sizeof(buf))) return spl_str_new("");
#endif
    return spl_str_new(buf);
}

const char* spl_env_get(const char* key) {
    const char* value = key ? getenv(key) : NULL;
    return value ? value : "";
}

void rt_sleep_ms_native(int64_t ms) {
    if (ms <= 0) return;
#if defined(_WIN32)
    Sleep((DWORD)ms);
#else
    struct timespec ts;
    ts.tv_sec = ms / 1000;
    ts.tv_nsec = (ms % 1000) * 1000000L;
    nanosleep(&ts, NULL);
#endif
}

int64_t rt_term_enable_ansi(void) {
#if defined(_WIN32)
    HANDLE out = GetStdHandle(STD_OUTPUT_HANDLE);
    DWORD mode = 0;
    if (out != INVALID_HANDLE_VALUE && GetConsoleMode(out, &mode)) {
        SetConsoleMode(out, mode | ENABLE_VIRTUAL_TERMINAL_PROCESSING);
    }
#endif
    return rt_value_bool(1);
}

int64_t rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count) {
    if (!cmd || !*cmd) return -1;
#if defined(_WIN32)
    char** argv = (char**)calloc((size_t)arg_count + 2, sizeof(char*));
    if (!argv) return -1;
    argv[0] = (char*)cmd;
    for (int64_t i = 0; i < arg_count; i++) argv[i + 1] = (char*)args[i];
    intptr_t pid = _spawnvp(_P_NOWAIT, cmd, (const char* const*)argv);
    free(argv);
    return pid < 0 ? -1 : (int64_t)pid;
#else
    pid_t pid = fork();
    if (pid < 0) return -1;
    if (pid == 0) {
        char** argv = (char**)calloc((size_t)arg_count + 2, sizeof(char*));
        if (!argv) _exit(1);
        argv[0] = (char*)cmd;
        for (int64_t i = 0; i < arg_count; i++) argv[i + 1] = (char*)args[i];
        execvp(cmd, argv);
        _exit(127);
    }
    return (int64_t)pid;
#endif
}

static void rt_legacy_stop_group(pid_t worker, bool worker_live) {
#if !defined(_WIN32)
    if (worker <= 0) return;
    if (kill(-worker, SIGTERM) != 0 && (!worker_live || kill(worker, SIGTERM) != 0)) return;
    usleep(100000);
    (void)kill(-worker, SIGKILL);
    if (worker_live) (void)kill(worker, SIGKILL);
#else
    (void)worker;
#endif
}

int64_t rt_process_spawn_guarded(const char* cmd, const char** args, int64_t arg_count) {
#if defined(_WIN32)
    return rt_process_spawn_async(cmd, args, arg_count);
#else
    if (!cmd || !*cmd) return -1;
    pid_t expected_parent = getpid();
    pid_t guardian = fork();
    if (guardian < 0) return -1;
    if (guardian != 0) return (int64_t)guardian;
    if (getppid() != expected_parent) _exit(143);

    pid_t worker = fork();
    if (worker < 0) _exit(127);
    if (worker == 0) {
        (void)setpgid(0, 0);
        char** argv = (char**)calloc((size_t)arg_count + 2, sizeof(char*));
        if (!argv) _exit(1);
        argv[0] = (char*)cmd;
        for (int64_t i = 0; i < arg_count; i++) argv[i + 1] = (char*)args[i];
        execvp(cmd, argv);
        _exit(127);
    }
    (void)setpgid(worker, worker);

    for (;;) {
        int status = 0;
        pid_t waited = waitpid(worker, &status, WNOHANG);
        if (waited == worker) {
            rt_legacy_stop_group(worker, false);
            if (WIFEXITED(status)) _exit(WEXITSTATUS(status));
            if (WIFSIGNALED(status)) {
                int sig = WTERMSIG(status);
                (void)signal(sig, SIG_DFL);
                (void)kill(getpid(), sig);
            }
            _exit(127);
        }
        if (waited < 0 && errno != EINTR) {
            rt_legacy_stop_group(worker, true);
            _exit(127);
        }
        if (getppid() != expected_parent) {
            rt_legacy_stop_group(worker, true);
            while (waitpid(worker, NULL, 0) < 0 && errno == EINTR) {}
            _exit(143);
        }
        usleep(10000);
    }
#endif
}
