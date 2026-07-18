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
#include <unistd.h>
#endif

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
static void core_dir_walk_impl(const char* path, SplArray* result) {
    size_t path_len = strlen(path);
    const char* separator = path_len > 0 && (path[path_len - 1] == '\\' || path[path_len - 1] == '/') ? "" : "\\";
    char pattern[4096];
    snprintf(pattern, sizeof(pattern), "%s%s*", path, separator);
    WIN32_FIND_DATAA entry;
    HANDLE handle = FindFirstFileA(pattern, &entry);
    if (handle == INVALID_HANDLE_VALUE) return;
    do {
        if (strcmp(entry.cFileName, ".") == 0 || strcmp(entry.cFileName, "..") == 0) continue;
        char full[4096];
        snprintf(full, sizeof(full), "%s%s%s", path, separator, entry.cFileName);
        if ((entry.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) &&
            !(entry.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT)) {
            core_dir_walk_impl(full, result);
        } else {
            rt_array_push(result, rt_string_new((const uint8_t*)full, strlen(full)));
        }
    } while (FindNextFileA(handle, &entry));
    FindClose(handle);
}
#else
static void core_dir_walk_impl(const char* path, SplArray* result) {
    size_t path_len = strlen(path);
    const char* separator = path_len > 0 && path[path_len - 1] == '/' ? "" : "/";
    DIR* dir = opendir(path);
    if (!dir) return;
    struct dirent* entry;
    while ((entry = readdir(dir)) != NULL) {
        if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) continue;
        char full[4096];
        snprintf(full, sizeof(full), "%s%s%s", path, separator, entry->d_name);
        struct stat metadata;
        if (lstat(full, &metadata) != 0) continue;
        if (S_ISDIR(metadata.st_mode)) {
            core_dir_walk_impl(full, result);
        } else {
            rt_array_push(result, rt_string_new((const uint8_t*)full, strlen(full)));
        }
    }
    closedir(dir);
}
#endif

SplArray* rt_dir_walk(const char* path) {
    SplArray* result = rt_array_new(4);
    if (path) core_dir_walk_impl(path, result);
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

void spl_panic(const char* msg) {
    fprintf(stderr, "panic: %s\n", msg ? msg : "");
    exit(1);
}

char* spl_file_read(const char* path) {
    if (!path) return spl_str_new("");
    FILE* f = fopen(path, "rb");
    if (!f) return spl_str_new("");
    if (fseek(f, 0, SEEK_END) != 0) {
        fclose(f);
        return spl_str_new("");
    }
    long len = ftell(f);
    if (len < 0) len = 0;
    if (fseek(f, 0, SEEK_SET) != 0) {
        fclose(f);
        return spl_str_new("");
    }
    char* out = (char*)malloc((size_t)len + 1);
    if (!out) {
        fclose(f);
        return NULL;
    }
    size_t n = fread(out, 1, (size_t)len, f);
    fclose(f);
    out[n] = '\0';
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

int rt_file_sync(const char* path, int64_t path_len) {
    (void)path_len;
    FILE* f = path ? fopen(path, "rb") : NULL;
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

bool rt_dir_remove_all(const char* path) {
    return path && *path && core_dir_remove_all_impl(path);
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
