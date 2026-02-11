/*
 * Simple Bootstrap Runtime Library — Implementation
 *
 * Provides tagged values, strings, dynamic arrays, hash-table dicts,
 * file I/O, formatting, and process execution for the bootstrap compiler.
 *
 * Build: cc -c bootstrap/runtime.c -o bootstrap/runtime.o -std=c11 -O2
 * Test:  cc -o /tmp/runtime_test bootstrap/runtime_test.c bootstrap/runtime.c -std=c11 && /tmp/runtime_test
 */

#if !defined(_WIN32)
#define _POSIX_C_SOURCE 200809L
#define _XOPEN_SOURCE 500
#endif

#include "runtime.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <sys/stat.h>

#ifndef _WIN32
#include <ftw.h>
#include <sys/file.h>
#include <fcntl.h>
#include <unistd.h>
#endif

#ifdef _WIN32
#include <io.h>
#include <process.h>
#define popen  _popen
#define pclose _pclose
#define strdup _strdup
#endif

/* ================================================================
 * Value Constructors
 * ================================================================ */

SplValue spl_nil(void) {
    SplValue v;
    v.tag = SPL_NIL;
    v.as_int = 0;
    return v;
}

SplValue spl_bool(int64_t b) {
    SplValue v;
    v.tag = SPL_BOOL;
    v.as_bool = b ? 1 : 0;
    return v;
}

SplValue spl_int(int64_t n) {
    SplValue v;
    v.tag = SPL_INT;
    v.as_int = n;
    return v;
}

SplValue spl_float(double f) {
    SplValue v;
    v.tag = SPL_FLOAT;
    v.as_float = f;
    return v;
}

SplValue spl_str(const char* s) {
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = s ? strdup(s) : strdup("");
    return v;
}

SplValue spl_str_own(char* s) {
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = s ? s : strdup("");
    return v;
}

SplValue spl_array_val(SplArray* a) {
    SplValue v;
    v.tag = SPL_ARRAY;
    v.as_array = a;
    return v;
}

SplValue spl_dict_val(SplDict* d) {
    SplValue v;
    v.tag = SPL_DICT;
    v.as_dict = d;
    return v;
}

/* ================================================================
 * Value Accessors
 * ================================================================ */

int64_t spl_as_bool(SplValue v) {
    return v.as_bool;
}

int64_t spl_as_int(SplValue v) {
    return v.as_int;
}

double spl_as_float(SplValue v) {
    return v.as_float;
}

const char* spl_as_str(SplValue v) {
    return v.as_str ? v.as_str : "";
}

SplArray* spl_as_array(SplValue v) {
    return v.as_array;
}

SplDict* spl_as_dict(SplValue v) {
    return v.as_dict;
}

/* ================================================================
 * Value Operations
 * ================================================================ */

int spl_is_truthy(SplValue v) {
    switch (v.tag) {
        case SPL_NIL:    return 0;
        case SPL_BOOL:   return v.as_bool != 0;
        case SPL_INT:    return v.as_int != 0;
        case SPL_FLOAT:  return v.as_float != 0.0;
        case SPL_STRING: return v.as_str && v.as_str[0] != '\0';
        case SPL_ARRAY:  return v.as_array && v.as_array->len > 0;
        case SPL_DICT:   return v.as_dict && v.as_dict->len > 0;
    }
    return 0;
}

int spl_eq(SplValue a, SplValue b) {
    if (a.tag != b.tag) return 0;
    switch (a.tag) {
        case SPL_NIL:    return 1;
        case SPL_BOOL:   return a.as_bool == b.as_bool;
        case SPL_INT:    return a.as_int == b.as_int;
        case SPL_FLOAT:  return a.as_float == b.as_float;
        case SPL_STRING: return strcmp(a.as_str ? a.as_str : "",
                                       b.as_str ? b.as_str : "") == 0;
        case SPL_ARRAY: {
            SplArray* aa = a.as_array;
            SplArray* ba = b.as_array;
            if (!aa && !ba) return 1;
            if (!aa || !ba) return 0;
            if (aa->len != ba->len) return 0;
            for (int64_t i = 0; i < aa->len; i++) {
                if (!spl_eq(aa->items[i], ba->items[i])) return 0;
            }
            return 1;
        }
        case SPL_DICT:
            return a.as_dict == b.as_dict; /* pointer equality for dicts */
    }
    return 0;
}

SplValue spl_to_string(SplValue v) {
    switch (v.tag) {
        case SPL_NIL:    return spl_str("nil");
        case SPL_BOOL:   return spl_str(v.as_bool ? "true" : "false");
        case SPL_INT:    return spl_str_own(spl_i64_to_str(v.as_int));
        case SPL_FLOAT:  return spl_str_own(spl_f64_to_str(v.as_float));
        case SPL_STRING: return spl_str(v.as_str);
        case SPL_ARRAY: {
            /* [elem1, elem2, ...] */
            SplArray* a = v.as_array;
            if (!a || a->len == 0) return spl_str("[]");
            char* buf = (char*)malloc(1024);
            int64_t buf_cap = 1024;
            int64_t pos = 0;
            buf[pos++] = '[';
            for (int64_t i = 0; i < a->len; i++) {
                if (i > 0) { buf[pos++] = ','; buf[pos++] = ' '; }
                SplValue s = spl_to_string(a->items[i]);
                int64_t slen = (int64_t)strlen(s.as_str);
                while (pos + slen + 4 > buf_cap) {
                    buf_cap *= 2;
                    buf = (char*)realloc(buf, buf_cap);
                }
                memcpy(buf + pos, s.as_str, slen);
                pos += slen;
                spl_free_value(s);
            }
            buf[pos++] = ']';
            buf[pos] = '\0';
            return spl_str_own(buf);
        }
        case SPL_DICT: return spl_str("{...}");
    }
    return spl_str("?");
}

void spl_free_value(SplValue v) {
    switch (v.tag) {
        case SPL_STRING:
            free(v.as_str);
            break;
        case SPL_ARRAY:
            spl_array_free(v.as_array);
            break;
        case SPL_DICT:
            spl_dict_free(v.as_dict);
            break;
        default:
            break;
    }
}

/* ================================================================
 * String Operations
 * ================================================================ */

char* spl_str_new(const char* s) {
    return strdup(s ? s : "");
}

char* spl_str_concat(const char* a, const char* b) {
    if (!a) a = "";
    if (!b) b = "";
    size_t alen = strlen(a);
    size_t blen = strlen(b);
    char* result = (char*)malloc(alen + blen + 1);
    memcpy(result, a, alen);
    memcpy(result + alen, b, blen);
    result[alen + blen] = '\0';
    return result;
}

int64_t spl_str_len(const char* s) {
    return s ? (int64_t)strlen(s) : 0;
}

int spl_str_eq(const char* a, const char* b) {
    if (!a) a = "";
    if (!b) b = "";
    return strcmp(a, b) == 0;
}

int spl_str_cmp(const char* a, const char* b) {
    if (!a) a = "";
    if (!b) b = "";
    return strcmp(a, b);
}

char* spl_str_slice(const char* s, int64_t start, int64_t end) {
    if (!s) return strdup("");
    int64_t slen = (int64_t)strlen(s);
    if (start < 0) start = slen + start;
    if (end < 0)   end = slen + end;
    if (start < 0) start = 0;
    if (end > slen) end = slen;
    if (start >= end) return strdup("");
    int64_t len = end - start;
    char* result = (char*)malloc(len + 1);
    memcpy(result, s + start, len);
    result[len] = '\0';
    return result;
}

char* spl_str_index_char(const char* s, int64_t idx) {
    if (!s) return strdup("");
    int64_t slen = (int64_t)strlen(s);
    if (idx < 0) idx = slen + idx;
    if (idx < 0 || idx >= slen) return strdup("");
    char buf[2] = { s[idx], '\0' };
    return strdup(buf);
}

uint64_t spl_str_hash(const char* s) {
    /* FNV-1a 64-bit */
    uint64_t h = 14695981039346656037ULL;
    if (!s) return h;
    while (*s) {
        h ^= (uint64_t)(unsigned char)*s++;
        h *= 1099511628211ULL;
    }
    return h;
}

int spl_str_contains(const char* s, const char* needle) {
    if (!s || !needle) return 0;
    return strstr(s, needle) != NULL;
}

int spl_str_starts_with(const char* s, const char* prefix) {
    if (!s || !prefix) return 0;
    return strncmp(s, prefix, strlen(prefix)) == 0;
}

int spl_str_ends_with(const char* s, const char* suffix) {
    if (!s || !suffix) return 0;
    size_t slen = strlen(s);
    size_t suflen = strlen(suffix);
    if (suflen > slen) return 0;
    return strcmp(s + slen - suflen, suffix) == 0;
}

char* spl_str_replace(const char* s, const char* old_s, const char* new_s) {
    if (!s) return strdup("");
    if (!old_s || !new_s || strlen(old_s) == 0) return strdup(s);
    size_t old_len = strlen(old_s);
    size_t new_len = strlen(new_s);
    /* Count occurrences */
    size_t count = 0;
    const char* tmp = s;
    while ((tmp = strstr(tmp, old_s)) != NULL) { count++; tmp += old_len; }
    if (count == 0) return strdup(s);
    /* Build result */
    size_t result_len = strlen(s) + count * (new_len - old_len + (new_len < old_len ? 0 : 0));
    /* recalculate properly */
    result_len = strlen(s) - count * old_len + count * new_len;
    char* result = (char*)malloc(result_len + 1);
    char* dst = result;
    while (*s) {
        if (strncmp(s, old_s, old_len) == 0) {
            memcpy(dst, new_s, new_len);
            dst += new_len;
            s += old_len;
        } else {
            *dst++ = *s++;
        }
    }
    *dst = '\0';
    return result;
}

char* spl_str_trim(const char* s) {
    if (!s) return strdup("");
    while (*s && (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r')) s++;
    size_t len = strlen(s);
    while (len > 0 && (s[len-1] == ' ' || s[len-1] == '\t' ||
                        s[len-1] == '\n' || s[len-1] == '\r')) len--;
    char* result = (char*)malloc(len + 1);
    memcpy(result, s, len);
    result[len] = '\0';
    return result;
}

int64_t spl_str_index_of(const char* s, const char* needle) {
    if (!s || !needle) return -1;
    const char* found = strstr(s, needle);
    if (!found) return -1;
    return (int64_t)(found - s);
}

char* spl_str_to_upper(const char* s) {
    if (!s) return strdup("");
    size_t len = strlen(s);
    char* result = (char*)malloc(len + 1);
    for (size_t i = 0; i < len; i++) {
        result[i] = (char)toupper((unsigned char)s[i]);
    }
    result[len] = '\0';
    return result;
}

char* spl_str_to_lower(const char* s) {
    if (!s) return strdup("");
    size_t len = strlen(s);
    char* result = (char*)malloc(len + 1);
    for (size_t i = 0; i < len; i++) {
        result[i] = (char)tolower((unsigned char)s[i]);
    }
    result[len] = '\0';
    return result;
}

/* ================================================================
 * Dynamic Array
 * ================================================================ */

#define SPL_ARRAY_INIT_CAP 16

SplArray* spl_array_new(void) {
    return spl_array_new_cap(SPL_ARRAY_INIT_CAP);
}

SplArray* spl_array_new_cap(int64_t cap) {
    if (cap < 4) cap = 4;
    SplArray* a = (SplArray*)malloc(sizeof(SplArray));
    a->items = (SplValue*)calloc(cap, sizeof(SplValue));
    a->len = 0;
    a->cap = cap;
    return a;
}

static void spl_array_grow(SplArray* a) {
    int64_t new_cap = a->cap * 2;
    a->items = (SplValue*)realloc(a->items, new_cap * sizeof(SplValue));
    /* Zero new slots */
    memset(a->items + a->cap, 0, (new_cap - a->cap) * sizeof(SplValue));
    a->cap = new_cap;
}

void spl_array_push(SplArray* a, SplValue v) {
    if (!a) return;
    if (a->len >= a->cap) spl_array_grow(a);
    a->items[a->len++] = v;
}

SplValue spl_array_get(SplArray* a, int64_t idx) {
    if (!a) return spl_nil();
    if (idx < 0) idx = a->len + idx;
    if (idx < 0 || idx >= a->len) return spl_nil();
    return a->items[idx];
}

void spl_array_set(SplArray* a, int64_t idx, SplValue v) {
    if (!a) return;
    if (idx < 0) idx = a->len + idx;
    if (idx < 0 || idx >= a->len) return;
    a->items[idx] = v;
}

int64_t spl_array_len(SplArray* a) {
    return a ? a->len : 0;
}

SplValue spl_array_pop(SplArray* a) {
    if (!a || a->len == 0) return spl_nil();
    return a->items[--a->len];
}

SplArray* spl_array_slice(SplArray* a, int64_t start, int64_t end) {
    if (!a) return spl_array_new();
    if (start < 0) start = a->len + start;
    if (end < 0)   end = a->len + end;
    if (start < 0) start = 0;
    if (end > a->len) end = a->len;
    if (start >= end) return spl_array_new();
    int64_t count = end - start;
    SplArray* result = spl_array_new_cap(count);
    for (int64_t i = 0; i < count; i++) {
        result->items[i] = a->items[start + i]; /* shallow copy */
    }
    result->len = count;
    return result;
}

SplArray* spl_array_concat(SplArray* a, SplArray* b) {
    int64_t alen = a ? a->len : 0;
    int64_t blen = b ? b->len : 0;
    SplArray* result = spl_array_new_cap(alen + blen + 1);
    for (int64_t i = 0; i < alen; i++) {
        result->items[i] = a->items[i];
    }
    for (int64_t i = 0; i < blen; i++) {
        result->items[alen + i] = b->items[i];
    }
    result->len = alen + blen;
    return result;
}

void spl_array_free(SplArray* a) {
    if (!a) return;
    for (int64_t i = 0; i < a->len; i++) {
        spl_free_value(a->items[i]);
    }
    free(a->items);
    free(a);
}

/* Typed convenience: i64 */
SplArray* spl_array_new_i64(void) { return spl_array_new(); }
void      spl_array_push_i64(SplArray* a, int64_t n)    { spl_array_push(a, spl_int(n)); }
int64_t   spl_array_get_i64(SplArray* a, int64_t idx)   { return spl_as_int(spl_array_get(a, idx)); }
void      spl_array_set_i64(SplArray* a, int64_t idx, int64_t n) { spl_array_set(a, idx, spl_int(n)); }

/* Typed convenience: text */
SplArray* spl_array_new_text(void) { return spl_array_new(); }
void      spl_array_push_text(SplArray* a, const char* s) { spl_array_push(a, spl_str(s)); }
const char* spl_array_get_text(SplArray* a, int64_t idx) { return spl_as_str(spl_array_get(a, idx)); }

/* ================================================================
 * Hash-Table Dictionary (open addressing, linear probing)
 * ================================================================ */

#define SPL_DICT_INIT_CAP 16
#define SPL_DICT_LOAD_FACTOR 0.70

SplDict* spl_dict_new(void) {
    return spl_dict_new_cap(SPL_DICT_INIT_CAP);
}

SplDict* spl_dict_new_cap(int64_t cap) {
    /* Round up to power of 2 */
    int64_t actual = 4;
    while (actual < cap) actual *= 2;
    SplDict* d = (SplDict*)malloc(sizeof(SplDict));
    d->entries = (SplDictEntry*)calloc(actual, sizeof(SplDictEntry));
    d->cap = actual;
    d->len = 0;
    d->tombstones = 0;
    return d;
}

static void spl_dict_resize(SplDict* d, int64_t new_cap) {
    SplDictEntry* old = d->entries;
    int64_t old_cap = d->cap;
    d->entries = (SplDictEntry*)calloc(new_cap, sizeof(SplDictEntry));
    d->cap = new_cap;
    d->len = 0;
    d->tombstones = 0;
    for (int64_t i = 0; i < old_cap; i++) {
        if (old[i].occupied == 1) {
            spl_dict_set(d, old[i].key, old[i].value);
            free(old[i].key); /* spl_dict_set made a copy */
        }
    }
    free(old);
}

void spl_dict_set(SplDict* d, const char* key, SplValue value) {
    if (!d || !key) return;
    /* Resize if load factor exceeded */
    if ((d->len + d->tombstones + 1) * 100 > d->cap * (int64_t)(SPL_DICT_LOAD_FACTOR * 100)) {
        spl_dict_resize(d, d->cap * 2);
    }
    uint64_t h = spl_str_hash(key);
    int64_t idx = (int64_t)(h & (uint64_t)(d->cap - 1));
    for (;;) {
        SplDictEntry* e = &d->entries[idx];
        if (e->occupied == 0) {
            /* Empty slot — insert */
            e->key = strdup(key);
            e->value = value;
            e->hash = h;
            e->occupied = 1;
            d->len++;
            return;
        }
        if (e->occupied == -1) {
            /* Tombstone — reuse */
            e->key = strdup(key);
            e->value = value;
            e->hash = h;
            e->occupied = 1;
            d->len++;
            d->tombstones--;
            return;
        }
        if (e->hash == h && strcmp(e->key, key) == 0) {
            /* Key exists — update value */
            e->value = value;
            return;
        }
        idx = (idx + 1) & (d->cap - 1);
    }
}

static SplDictEntry* spl_dict_find(SplDict* d, const char* key) {
    if (!d || !key || d->len == 0) return NULL;
    uint64_t h = spl_str_hash(key);
    int64_t idx = (int64_t)(h & (uint64_t)(d->cap - 1));
    for (;;) {
        SplDictEntry* e = &d->entries[idx];
        if (e->occupied == 0) return NULL; /* empty = not found */
        if (e->occupied == 1 && e->hash == h && strcmp(e->key, key) == 0) {
            return e;
        }
        idx = (idx + 1) & (d->cap - 1);
    }
}

SplValue spl_dict_get(SplDict* d, const char* key) {
    SplDictEntry* e = spl_dict_find(d, key);
    return e ? e->value : spl_nil();
}

int spl_dict_contains(SplDict* d, const char* key) {
    return spl_dict_find(d, key) != NULL;
}

SplArray* spl_dict_keys(SplDict* d) {
    SplArray* keys = spl_array_new();
    if (!d) return keys;
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].occupied == 1) {
            spl_array_push(keys, spl_str(d->entries[i].key));
        }
    }
    return keys;
}

SplArray* spl_dict_values(SplDict* d) {
    SplArray* vals = spl_array_new();
    if (!d) return vals;
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].occupied == 1) {
            spl_array_push(vals, d->entries[i].value);
        }
    }
    return vals;
}

int64_t spl_dict_len(SplDict* d) {
    return d ? d->len : 0;
}

void spl_dict_remove(SplDict* d, const char* key) {
    SplDictEntry* e = spl_dict_find(d, key);
    if (!e) return;
    free(e->key);
    e->key = NULL;
    e->occupied = -1; /* tombstone */
    d->len--;
    d->tombstones++;
}

void spl_dict_free(SplDict* d) {
    if (!d) return;
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].occupied == 1) {
            free(d->entries[i].key);
            spl_free_value(d->entries[i].value);
        }
    }
    free(d->entries);
    free(d);
}

/* ================================================================
 * File I/O
 * ================================================================ */

char* spl_file_read(const char* path) {
    if (!path) return strdup("");
    FILE* f = fopen(path, "rb");
    if (!f) return strdup("");
    fseek(f, 0, SEEK_END);
    long len = ftell(f);
    fseek(f, 0, SEEK_SET);
    char* buf = (char*)malloc(len + 1);
    size_t read_len = fread(buf, 1, len, f);
    buf[read_len] = '\0';
    fclose(f);
    return buf;
}

int spl_file_write(const char* path, const char* content) {
    if (!path) return 0;
    FILE* f = fopen(path, "wb");
    if (!f) return 0;
    if (content) fputs(content, f);
    fclose(f);
    return 1;
}

int spl_file_append(const char* path, const char* content) {
    if (!path) return 0;
    FILE* f = fopen(path, "ab");
    if (!f) return 0;
    if (content) fputs(content, f);
    fclose(f);
    return 1;
}

int spl_file_exists(const char* path) {
    if (!path) return 0;
    FILE* f = fopen(path, "r");
    if (f) { fclose(f); return 1; }
    return 0;
}

/* ================================================================
 * Directory Operations
 * ================================================================ */

#ifndef _WIN32
static int unlink_cb(const char *fpath, const struct stat *sb, int typeflag, struct FTW *ftwbuf) {
    (void)sb; (void)typeflag; (void)ftwbuf;
    return remove(fpath);
}

bool rt_dir_remove_all(const char* path) {
    if (!path) return false;
    return nftw(path, unlink_cb, 64, FTW_DEPTH | FTW_PHYS) == 0;
}

/* ================================================================
 * File Locking
 * ================================================================ */

int64_t rt_file_lock(const char* path, int64_t timeout_secs) {
    if (!path) return -1;

    int fd = open(path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) return -1;

    if (timeout_secs > 0) {
        alarm(timeout_secs);
    }

    int result = flock(fd, LOCK_EX);
    alarm(0);

    if (result == 0) return fd;
    close(fd);
    return -1;
}

bool rt_file_unlock(int64_t handle) {
    if (handle < 0) return false;
    flock((int)handle, LOCK_UN);
    close((int)handle);
    return true;
}
#else
/* Windows stubs - not implemented yet */
bool rt_dir_remove_all(const char* path) {
    (void)path;
    return false;
}

int64_t rt_file_lock(const char* path, int64_t timeout_secs) {
    (void)path; (void)timeout_secs;
    return -1;
}

bool rt_file_unlock(int64_t handle) {
    (void)handle;
    return false;
}
#endif

/* ================================================================
 * Output
 * ================================================================ */

void spl_print(const char* s) {
    if (s) fputs(s, stdout);
}

void spl_println(const char* s) {
    if (s) fputs(s, stdout);
    putchar('\n');
}

void spl_print_i64(int64_t n) {
    printf("%lld", (long long)n);
}

void spl_print_f64(double f) {
    printf("%g", f);
}

/* ================================================================
 * Formatting
 * ================================================================ */

char* spl_i64_to_str(int64_t n) {
    char buf[32];
    snprintf(buf, sizeof(buf), "%lld", (long long)n);
    return strdup(buf);
}

char* spl_f64_to_str(double f) {
    char buf[64];
    snprintf(buf, sizeof(buf), "%g", f);
    return strdup(buf);
}

char* spl_sprintf(const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    /* Determine required size */
    va_list args_copy;
    va_copy(args_copy, args);
    int len = vsnprintf(NULL, 0, fmt, args_copy);
    va_end(args_copy);
    if (len < 0) { va_end(args); return strdup(""); }
    char* buf = (char*)malloc(len + 1);
    vsnprintf(buf, len + 1, fmt, args);
    va_end(args);
    return buf;
}

/* ================================================================
 * Process
 * ================================================================ */

int64_t spl_shell(const char* cmd) {
    if (!cmd) return -1;
    return (int64_t)system(cmd);
}

char* spl_shell_output(const char* cmd) {
    if (!cmd) return strdup("");
    FILE* pipe = popen(cmd, "r");
    if (!pipe) return strdup("");
    char* buf = (char*)malloc(4096);
    int64_t buf_cap = 4096;
    int64_t pos = 0;
    char tmp[1024];
    while (fgets(tmp, sizeof(tmp), pipe)) {
        size_t chunk = strlen(tmp);
        while (pos + (int64_t)chunk + 1 > buf_cap) {
            buf_cap *= 2;
            buf = (char*)realloc(buf, buf_cap);
        }
        memcpy(buf + pos, tmp, chunk);
        pos += (int64_t)chunk;
    }
    buf[pos] = '\0';
    pclose(pipe);
    return buf;
}

/* ================================================================
 * Environment
 * ================================================================ */

const char* spl_env_get(const char* key) {
    if (!key) return "";
    const char* val = getenv(key);
    return val ? val : "";
}

void spl_env_set(const char* key, const char* value) {
    if (!key) return;
#ifdef _WIN32
    _putenv_s(key, value ? value : "");
#else
    if (value) {
        setenv(key, value, 1);
    } else {
        unsetenv(key);
    }
#endif
}

/* ================================================================
 * Memory
 * ================================================================ */

void* spl_malloc(int64_t size) {
    return malloc((size_t)size);
}

void spl_free(void* ptr) {
    free(ptr);
}

char* spl_strdup(const char* s) {
    return strdup(s ? s : "");
}

/* ================================================================
 * Panic
 * ================================================================ */

/* ================================================================
 * Command-Line Arguments
 * ================================================================ */

static int    g_argc = 0;
static char** g_argv = NULL;

void spl_init_args(int argc, char** argv) {
    g_argc = argc;
    g_argv = argv;
}

int64_t spl_arg_count(void) {
    return (int64_t)g_argc;
}

const char* spl_get_arg(int64_t idx) {
    if (idx < 0 || idx >= g_argc) return "";
    return g_argv[idx] ? g_argv[idx] : "";
}

/* ================================================================
 * Dynamic Loading (WFFI)
 * ================================================================ */

#ifdef _WIN32
#include <windows.h>
void* spl_dlopen(const char* path) {
    return (void*)LoadLibraryA(path);
}
void* spl_dlsym(void* handle, const char* name) {
    return (void*)GetProcAddress((HMODULE)handle, name);
}
int64_t spl_dlclose(void* handle) {
    return FreeLibrary((HMODULE)handle) ? 0 : -1;
}
#else
#include <dlfcn.h>
void* spl_dlopen(const char* path) {
    return dlopen(path, RTLD_NOW);
}
void* spl_dlsym(void* handle, const char* name) {
    return dlsym(handle, name);
}
int64_t spl_dlclose(void* handle) {
    return (int64_t)dlclose(handle);
}
#endif

int64_t spl_wffi_call_i64(void* fptr, int64_t* args, int64_t nargs) {
    typedef int64_t (*fn0)(void);
    typedef int64_t (*fn1)(int64_t);
    typedef int64_t (*fn2)(int64_t, int64_t);
    typedef int64_t (*fn3)(int64_t, int64_t, int64_t);
    typedef int64_t (*fn4)(int64_t, int64_t, int64_t, int64_t);
    if (!fptr) return 0;
    switch (nargs) {
        case 0: return ((fn0)fptr)();
        case 1: return ((fn1)fptr)(args[0]);
        case 2: return ((fn2)fptr)(args[0], args[1]);
        case 3: return ((fn3)fptr)(args[0], args[1], args[2]);
        case 4: return ((fn4)fptr)(args[0], args[1], args[2], args[3]);
        default: return 0;
    }
}

/* ================================================================
 * JIT Exec Manager (stubs — core compiler uses tree-walk interpreter)
 * ================================================================ */

int64_t rt_exec_manager_create(const char* backend) {
    (void)backend;
    return 0;
}

const char* rt_exec_manager_compile(int64_t handle, const char* mir_data) {
    (void)handle; (void)mir_data;
    return "";
}

int64_t rt_exec_manager_execute(int64_t handle, const char* name, SplArray* args) {
    (void)handle; (void)name; (void)args;
    return 0;
}

bool rt_exec_manager_has_function(int64_t handle, const char* name) {
    (void)handle; (void)name;
    return false;
}

void rt_exec_manager_cleanup(int64_t handle) {
    (void)handle;
}

/* ================================================================
 * Panic
 * ================================================================ */

void spl_panic(const char* msg) {
    fprintf(stderr, "PANIC: %s\n", msg ? msg : "unknown error");
    exit(1);
}
