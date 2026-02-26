/*
 * Simple Bootstrap Runtime Library — Implementation
 *
 * Provides tagged values, strings, dynamic arrays, hash-table dicts,
 * file I/O, formatting, and process execution for the bootstrap compiler.
 *
 * Build: cc -c bootstrap/runtime.c -o bootstrap/runtime.o -std=c11 -O2
 * Test:  cc -o /tmp/runtime_test bootstrap/runtime_test.c bootstrap/runtime.c -std=c11 && /tmp/runtime_test
 */

#include "platform/platform.h"

#include "runtime.h"
#include "runtime_memtrack.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <ctype.h>
#include <errno.h>
#include <sys/stat.h>

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
    v.as_str = s ? SPL_STRDUP(s, "str") : SPL_STRDUP("", "str");
    return v;
}

SplValue spl_str_own(char* s) {
    SplValue v;
    v.tag = SPL_STRING;
    v.as_str = s ? s : SPL_STRDUP("", "str");
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
            char* buf = (char*)SPL_MALLOC(1024, "buf");
            int64_t buf_cap = 1024;
            int64_t pos = 0;
            buf[pos++] = '[';
            for (int64_t i = 0; i < a->len; i++) {
                if (i > 0) { buf[pos++] = ','; buf[pos++] = ' '; }
                SplValue s = spl_to_string(a->items[i]);
                int64_t slen = (int64_t)strlen(s.as_str);
                while (pos + slen + 4 > buf_cap) {
                    buf_cap *= 2;
                    buf = (char*)SPL_REALLOC(buf, buf_cap, "buf");
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
            SPL_FREE(v.as_str);
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
    return SPL_STRDUP(s ? s : "", "str");
}

char* spl_str_concat(const char* a, const char* b) {
    if (!a) a = "";
    if (!b) b = "";
    size_t alen = strlen(a);
    size_t blen = strlen(b);
    char* result = (char*)SPL_MALLOC(alen + blen + 1, "str");
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
    if (!s) return SPL_STRDUP("", "str");
    int64_t slen = (int64_t)strlen(s);
    if (start < 0) start = slen + start;
    if (end < 0)   end = slen + end;
    if (start < 0) start = 0;
    if (end > slen) end = slen;
    if (start >= end) return SPL_STRDUP("", "str");
    int64_t len = end - start;
    char* result = (char*)SPL_MALLOC(len + 1, "str");
    memcpy(result, s + start, len);
    result[len] = '\0';
    return result;
}

char* spl_str_index_char(const char* s, int64_t idx) {
    if (!s) return SPL_STRDUP("", "str");
    int64_t slen = (int64_t)strlen(s);
    if (idx < 0) idx = slen + idx;
    if (idx < 0 || idx >= slen) return SPL_STRDUP("", "str");
    char buf[2] = { s[idx], '\0' };
    return SPL_STRDUP(buf, "str");
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
    if (!s) return SPL_STRDUP("", "str");
    if (!old_s || !new_s || strlen(old_s) == 0) return SPL_STRDUP(s, "str");
    size_t old_len = strlen(old_s);
    size_t new_len = strlen(new_s);
    /* Count occurrences */
    size_t count = 0;
    const char* tmp = s;
    while ((tmp = strstr(tmp, old_s)) != NULL) { count++; tmp += old_len; }
    if (count == 0) return SPL_STRDUP(s, "str");
    /* Build result */
    size_t result_len = strlen(s) + count * (new_len - old_len + (new_len < old_len ? 0 : 0));
    /* recalculate properly */
    result_len = strlen(s) - count * old_len + count * new_len;
    char* result = (char*)SPL_MALLOC(result_len + 1, "str");
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
    if (!s) return SPL_STRDUP("", "str");
    while (*s && (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r')) s++;
    size_t len = strlen(s);
    while (len > 0 && (s[len-1] == ' ' || s[len-1] == '\t' ||
                        s[len-1] == '\n' || s[len-1] == '\r')) len--;
    char* result = (char*)SPL_MALLOC(len + 1, "str");
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

int64_t spl_str_last_index_of(const char* s, const char* needle) {
    if (!s || !needle) return -1;
    int64_t needle_len = (int64_t)strlen(needle);
    int64_t slen = (int64_t)strlen(s);
    if (needle_len == 0 || needle_len > slen) return -1;
    for (int64_t i = slen - needle_len; i >= 0; i--) {
        if (strncmp(s + i, needle, (size_t)needle_len) == 0) {
            return i;
        }
    }
    return -1;
}

char* spl_str_to_upper(const char* s) {
    if (!s) return SPL_STRDUP("", "str");
    size_t len = strlen(s);
    char* result = (char*)SPL_MALLOC(len + 1, "str");
    for (size_t i = 0; i < len; i++) {
        result[i] = (char)toupper((unsigned char)s[i]);
    }
    result[len] = '\0';
    return result;
}

char* spl_str_to_lower(const char* s) {
    if (!s) return SPL_STRDUP("", "str");
    size_t len = strlen(s);
    char* result = (char*)SPL_MALLOC(len + 1, "str");
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
    SplArray* a = (SplArray*)SPL_MALLOC(sizeof(SplArray), "arr");
    a->items = (SplValue*)SPL_CALLOC(cap, sizeof(SplValue), "arr");
    a->len = 0;
    a->cap = cap;
    return a;
}

static void spl_array_grow(SplArray* a) {
    int64_t new_cap = a->cap * 2;
    a->items = (SplValue*)SPL_REALLOC(a->items, new_cap * sizeof(SplValue), "arr");
    /* Zero new slots */
    memset(a->items + a->cap, 0, (new_cap - a->cap) * sizeof(SplValue));
    a->cap = new_cap;
}

SplArray* spl_array_push(SplArray* a, SplValue v) {
    if (!a) return NULL;
    if (a->len >= a->cap) spl_array_grow(a);
    a->items[a->len++] = v;
    return a;
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
    SPL_FREE(a->items);
    SPL_FREE(a);
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

/* String array utilities */
int spl_array_contains_str(SplArray* arr, const char* needle) {
    if (!arr || !needle) return 0;
    for (int64_t i = 0; i < arr->len; i++) {
        if (arr->items[i].tag == SPL_STRING && arr->items[i].as_str &&
            strcmp(arr->items[i].as_str, needle) == 0) return 1;
    }
    return 0;
}

SplArray* spl_str_split(const char* s, const char* delim) {
    SplArray* arr = spl_array_new();
    if (!s) return arr;
    if (!delim || strlen(delim) == 0) {
        spl_array_push(arr, spl_str(s));
        return arr;
    }
    size_t delim_len = strlen(delim);
    const char* start = s;
    const char* found;
    while ((found = strstr(start, delim)) != NULL) {
        size_t len = (size_t)(found - start);
        char* part = (char*)SPL_MALLOC(len + 1, "str");
        memcpy(part, start, len);
        part[len] = '\0';
        spl_array_push(arr, spl_str_own(part));
        start = found + delim_len;
    }
    spl_array_push(arr, spl_str(start));
    return arr;
}

char* spl_str_join(SplArray* arr, const char* delim) {
    if (!arr || arr->len == 0) return SPL_STRDUP("", "str");
    const char* safe_delim = delim ? delim : "";
    size_t delim_len = strlen(safe_delim);
    size_t total = 0;
    for (int64_t i = 0; i < arr->len; i++) {
        const char* s = (arr->items[i].tag == SPL_STRING && arr->items[i].as_str)
                        ? arr->items[i].as_str : "";
        total += strlen(s);
        if (i < arr->len - 1) total += delim_len;
    }
    char* result = (char*)SPL_MALLOC(total + 1, "str");
    char* dst = result;
    for (int64_t i = 0; i < arr->len; i++) {
        const char* s = (arr->items[i].tag == SPL_STRING && arr->items[i].as_str)
                        ? arr->items[i].as_str : "";
        size_t slen = strlen(s);
        memcpy(dst, s, slen);
        dst += slen;
        if (i < arr->len - 1) {
            memcpy(dst, safe_delim, delim_len);
            dst += delim_len;
        }
    }
    *dst = '\0';
    return result;
}

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
    SplDict* d = (SplDict*)SPL_MALLOC(sizeof(SplDict), "dict");
    d->entries = (SplDictEntry*)SPL_CALLOC(actual, sizeof(SplDictEntry), "dict");
    d->cap = actual;
    d->len = 0;
    d->tombstones = 0;
    return d;
}

static void spl_dict_resize(SplDict* d, int64_t new_cap) {
    SplDictEntry* old = d->entries;
    int64_t old_cap = d->cap;
    d->entries = (SplDictEntry*)SPL_CALLOC(new_cap, sizeof(SplDictEntry), "dict");
    d->cap = new_cap;
    d->len = 0;
    d->tombstones = 0;
    for (int64_t i = 0; i < old_cap; i++) {
        if (old[i].occupied == 1) {
            spl_dict_set(d, old[i].key, old[i].value);
            SPL_FREE(old[i].key); /* spl_dict_set made a copy */
        }
    }
    SPL_FREE(old);
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
            e->key = SPL_STRDUP(key, "dict");
            e->value = value;
            e->hash = h;
            e->occupied = 1;
            d->len++;
            return;
        }
        if (e->occupied == -1) {
            /* Tombstone — reuse */
            e->key = SPL_STRDUP(key, "dict");
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
    SPL_FREE(e->key);
    e->key = NULL;
    e->occupied = -1; /* tombstone */
    d->len--;
    d->tombstones++;
}

void spl_dict_free(SplDict* d) {
    if (!d) return;
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].occupied == 1) {
            SPL_FREE(d->entries[i].key);
            spl_free_value(d->entries[i].value);
        }
    }
    SPL_FREE(d->entries);
    SPL_FREE(d);
}

/* ================================================================
 * File I/O
 * ================================================================ */

char* spl_file_read(const char* path) {
    if (!path) return SPL_STRDUP("", "file");
#if !defined(_WIN32) && !defined(__EMSCRIPTEN__)
    /* Use mmap for files >= 4KB — avoids malloc+copy overhead.
     * For source files (typically 1-50KB), mmap lets the OS page in
     * directly from the page cache without a user-space buffer copy. */
    int fd = open(path, O_RDONLY);
    if (fd < 0) return SPL_STRDUP("", "file");
    struct stat st;
    if (fstat(fd, &st) != 0 || st.st_size <= 0) {
        close(fd);
        return SPL_STRDUP("", "file");
    }
    size_t len = (size_t)st.st_size;
    if (len >= 4096) {
        /* mmap path: map file, copy to owned buffer, unmap */
        void* mapped = mmap(NULL, len, PROT_READ, MAP_PRIVATE, fd, 0);
        if (mapped != MAP_FAILED) {
            /* Advise sequential access for readahead */
            madvise(mapped, len, MADV_SEQUENTIAL);
            char* buf = (char*)SPL_MALLOC(len + 1, "file");
            memcpy(buf, mapped, len);
            buf[len] = '\0';
            munmap(mapped, len);
            close(fd);
            return buf;
        }
        /* mmap failed — fall through to read() */
    }
    /* Small file or mmap fallback: use read() */
    char* buf = (char*)SPL_MALLOC(len + 1, "file");
    ssize_t nread = read(fd, buf, len);
    buf[nread > 0 ? nread : 0] = '\0';
    close(fd);
    return buf;
#else
    /* Windows / Emscripten: use fopen/fread */
    FILE* f = fopen(path, "rb");
    if (!f) return SPL_STRDUP("", "file");
    fseek(f, 0, SEEK_END);
    long len = ftell(f);
    fseek(f, 0, SEEK_SET);
    char* buf = (char*)SPL_MALLOC(len + 1, "file");
    size_t read_len = fread(buf, 1, len, f);
    buf[read_len] = '\0';
    fclose(f);
    return buf;
#endif
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

int spl_file_delete(const char* path) {
    if (!path) return 0;
    return remove(path) == 0 ? 1 : 0;
}

int64_t spl_file_size(const char* path) {
    if (!path) return -1;
    FILE* f = fopen(path, "rb");
    if (!f) return -1;
    fseek(f, 0, SEEK_END);
    int64_t size = (int64_t)ftell(f);
    fclose(f);
    return size;
}

/* ================================================================
 * Directory Operations
 * ================================================================ */

/* rt_dir_remove_all, rt_file_lock, rt_file_unlock — see platform/ headers */

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

void spl_eprintln(const char* s) {
    if (s) fputs(s, stderr);
    fputc('\n', stderr);
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
    return SPL_STRDUP(buf, "fmt");
}

char* spl_f64_to_str(double f) {
    char buf[64];
    snprintf(buf, sizeof(buf), "%g", f);
    return SPL_STRDUP(buf, "fmt");
}

/* ===== Bit-cast Helpers (f64 <-> i64 for DynLoader) ===== */

int64_t spl_f64_to_bits(double f) {
    int64_t bits;
    memcpy(&bits, &f, sizeof(double));
    return bits;
}

double spl_bits_to_f64(int64_t bits) {
    double f;
    memcpy(&f, &bits, sizeof(int64_t));
    return f;
}

int64_t spl_str_ptr(const char* s) {
    return (int64_t)(uintptr_t)s;
}

char* spl_sprintf(const char* fmt, ...) {
    va_list args;
    va_start(args, fmt);
    /* Determine required size */
    va_list args_copy;
    va_copy(args_copy, args);
    int len = vsnprintf(NULL, 0, fmt, args_copy);
    va_end(args_copy);
    if (len < 0) { va_end(args); return SPL_STRDUP("", "fmt"); }
    char* buf = (char*)SPL_MALLOC(len + 1, "fmt");
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
    if (!cmd) return SPL_STRDUP("", "shell");
    FILE* pipe = popen(cmd, "r");
    if (!pipe) return SPL_STRDUP("", "shell");
    char* buf = (char*)SPL_MALLOC(4096, "shell");
    int64_t buf_cap = 4096;
    int64_t pos = 0;
    char tmp[1024];
    while (fgets(tmp, sizeof(tmp), pipe)) {
        size_t chunk = strlen(tmp);
        while (pos + (int64_t)chunk + 1 > buf_cap) {
            buf_cap *= 2;
            buf = (char*)SPL_REALLOC(buf, buf_cap, "shell");
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

const char* rt_env_get(const char* key) {
    return spl_env_get(key);
}

/* spl_env_set — see platform/ headers */

/* ================================================================
 * Memory
 * ================================================================ */

void* spl_malloc(int64_t size) {
    return SPL_MALLOC((size_t)size, "user");
}

void spl_free(void* ptr) {
    SPL_FREE(ptr);
}

char* spl_strdup(const char* s) {
    return SPL_STRDUP(s ? s : "", "user");
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
 * rt_ Aliases (FFI-compatible wrappers)
 * ================================================================ */

const char* rt_file_read_text(const char* path) { return spl_file_read(path); }
int         rt_file_exists(const char* path)    { return spl_file_exists(path); }
int         rt_file_write(const char* path, const char* content) {
    if (!path) return 0;
    FILE* f = fopen(path, "w");
    if (!f) return 0;
    if (content) fputs(content, f);
    fclose(f);
    return 1;
}
int         rt_file_append(const char* path, const char* content) {
    return spl_file_append(path, content);
}
int         rt_file_copy(const char* src, const char* dst) {
    FILE* in = fopen(src, "rb");
    if (!in) return 0;
    
    FILE* out = fopen(dst, "wb");
    if (!out) {
        fclose(in);
        return 0;
    }
    
    char buf[8192];
    size_t n;
    while ((n = fread(buf, 1, sizeof(buf), in)) > 0) {
        if (fwrite(buf, 1, n, out) != n) {
            fclose(in);
            fclose(out);
            return 0;
        }
    }
    
    fclose(in);
    fclose(out);
    return 1;
}
int         rt_file_delete(const char* path)    { return spl_file_delete(path); }
int64_t     rt_file_size(const char* path)      { return spl_file_size(path); }

int64_t rt_file_stat(const char* path) {
    struct stat st;
    if (stat(path, &st) == 0) {
        return (int64_t)st.st_mtime;
    }
    return 0;
}

const char* rt_shell_output(const char* cmd) { return spl_shell_output(cmd); }

SplArray* rt_cli_get_args(void) {
    SplArray* arr = spl_array_new();
    for (int i = 0; i < g_argc; i++) {
        spl_array_push(arr, spl_str(g_argv && g_argv[i] ? g_argv[i] : ""));
    }
    return arr;
}

/* ================================================================
 * Directory Walk (returns all files recursively)
 * ================================================================ */

#ifdef _WIN32
static void rt_dir_walk_impl(const char* path, SplArray* result) {
    char pattern[4096];
    snprintf(pattern, sizeof(pattern), "%s\\*", path);

    WIN32_FIND_DATAA find_data;
    HANDLE hFind = FindFirstFileA(pattern, &find_data);
    if (hFind == INVALID_HANDLE_VALUE) return;

    do {
        if (strcmp(find_data.cFileName, ".") == 0 || strcmp(find_data.cFileName, "..") == 0) continue;

        char full[4096];
        snprintf(full, sizeof(full), "%s\\%s", path, find_data.cFileName);

        if (find_data.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY) {
            rt_dir_walk_impl(full, result);
        } else {
            spl_array_push(result, spl_str(full));
        }
    } while (FindNextFileA(hFind, &find_data));

    FindClose(hFind);
}
#else
static void rt_dir_walk_impl(const char* path, SplArray* result) {
    DIR* dir = opendir(path);
    if (!dir) return;

    struct dirent* ent;
    while ((ent = readdir(dir)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;

        char full[4096];
        snprintf(full, sizeof(full), "%s/%s", path, ent->d_name);

        struct stat st;
        if (stat(full, &st) != 0) continue;

        if (S_ISDIR(st.st_mode)) {
            rt_dir_walk_impl(full, result);
        } else {
            spl_array_push(result, spl_str(full));
        }
    }
    closedir(dir);
}
#endif

SplArray* rt_dir_walk(const char* path) {
    SplArray* result = spl_array_new();
    if (!path) return result;
    rt_dir_walk_impl(path, result);
    return result;
}

SplArray* rt_dir_list_array(const char* path) {
    int64_t count = 0;
    const char** entries = rt_dir_list(path, &count);
    SplArray* result = spl_array_new_cap(count + 1);
    for (int64_t i = 0; i < count; i++) {
        spl_array_push(result, spl_str(entries[i]));
    }
    if (entries) rt_dir_list_free(entries, count);
    return result;
}

/* ================================================================
 * Dynamic Loading (WFFI)
 * ================================================================ */

/* spl_dlopen, spl_dlsym, spl_dlclose — see platform/ headers */

int64_t spl_wffi_call_i64(void* fptr, int64_t* args, int64_t nargs) {
    typedef int64_t (*fn0)(void);
    typedef int64_t (*fn1)(int64_t);
    typedef int64_t (*fn2)(int64_t, int64_t);
    typedef int64_t (*fn3)(int64_t, int64_t, int64_t);
    typedef int64_t (*fn4)(int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*fn5)(int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*fn6)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*fn7)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    typedef int64_t (*fn8)(int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t, int64_t);
    if (!fptr) return 0;
    switch (nargs) {
        case 0: return ((fn0)fptr)();
        case 1: return ((fn1)fptr)(args[0]);
        case 2: return ((fn2)fptr)(args[0], args[1]);
        case 3: return ((fn3)fptr)(args[0], args[1], args[2]);
        case 4: return ((fn4)fptr)(args[0], args[1], args[2], args[3]);
        case 5: return ((fn5)fptr)(args[0], args[1], args[2], args[3], args[4]);
        case 6: return ((fn6)fptr)(args[0], args[1], args[2], args[3], args[4], args[5]);
        case 7: return ((fn7)fptr)(args[0], args[1], args[2], args[3], args[4], args[5], args[6]);
        case 8: return ((fn8)fptr)(args[0], args[1], args[2], args[3], args[4], args[5], args[6], args[7]);
        default: return 0;
    }
}

/* ================================================================
 * JIT Exec Manager (stubs — core compiler uses tree-walk interpreter)
 * ================================================================ */

__attribute__((weak)) int64_t rt_exec_manager_create(const char* backend) {
    (void)backend;
    return 0;
}

__attribute__((weak)) const char* rt_exec_manager_compile(int64_t handle, const char* mir_data) {
    (void)handle; (void)mir_data;
    return "";
}

__attribute__((weak)) int64_t rt_exec_manager_execute(int64_t handle, const char* name, SplArray* args) {
    (void)handle; (void)name; (void)args;
    return 0;
}

__attribute__((weak)) bool rt_exec_manager_has_function(int64_t handle, const char* name) {
    (void)handle; (void)name;
    return false;
}

__attribute__((weak)) void rt_exec_manager_cleanup(int64_t handle) {
    /* Clean up soft JIT temp file if it exists. */
    char path[256];
    snprintf(path, sizeof(path), "tmp/jit/simple_soft_jit_%lld.spl",
             (long long)handle);
    remove(path);  /* ignore errors — file may not exist */
}

/* ================================================================
 * Power
 * ================================================================ */

int64_t __simple_pow(int64_t base, int64_t exp) {
    if (exp < 0) return 0;
    int64_t result = 1;
    while (exp > 0) {
        if (exp & 1) result *= base;
        base *= base;
        exp >>= 1;
    }
    return result;
}

/* ================================================================
 * Intrinsics (stubs for C backend)
 * ================================================================ */

int64_t __simple_intrinsic_unreachable(void) {
    fprintf(stderr, "PANIC: reached unreachable intrinsic\n");
    exit(1);
    return 0;
}

int64_t __simple_intrinsic_trap(void) {
    fprintf(stderr, "PANIC: trap intrinsic\n");
    exit(1);
    return 0;
}

int64_t __simple_intrinsic_assume(int64_t cond) {
    (void)cond;
    return 0;
}

int64_t __simple_intrinsic_likely(int64_t cond) {
    return cond;
}

int64_t __simple_intrinsic_unlikely(int64_t cond) {
    return cond;
}

int64_t __simple_intrinsic_prefetch(void* ptr) {
    (void)ptr;
    return 0;
}

int64_t __simple_intrinsic_memcpy(void* dst, const void* src, int64_t n) {
    memcpy(dst, src, (size_t)n);
    return 0;
}

int64_t __simple_intrinsic_memset(void* dst, int64_t val, int64_t n) {
    memset(dst, (int)val, (size_t)n);
    return 0;
}

/* ================================================================
 * Panic
 * ================================================================ */

void spl_panic(const char* msg) {
    fprintf(stderr, "PANIC: %s\n", msg ? msg : "unknown error");
    exit(1);
}
