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
#include <signal.h>
#include <sys/stat.h>
#ifndef _WIN32
#include <dirent.h>
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

char* spl_str_append(char* dest, const char* suffix) {
    if (!suffix || !*suffix) return dest ? dest : spl_str_new("");
    if (!dest) return spl_str_new(suffix);
    size_t dlen = strlen(dest);
    size_t slen = strlen(suffix);
    dest = (char*)SPL_REALLOC(dest, dlen + slen + 1, "str");
    memcpy(dest + dlen, suffix, slen);
    dest[dlen + slen] = '\0';
    return dest;
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

int64_t rt_str_hash(const char* s) {
    return (int64_t)spl_str_hash(s);
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

static int spl_array_is_nil(SplArray* a) {
    return !a || (uintptr_t)a < 4096;
}

SplArray* spl_array_push(SplArray* a, SplValue v) {
    if (spl_array_is_nil(a)) a = spl_array_new();
    if (a->len >= a->cap) spl_array_grow(a);
    a->items[a->len++] = v;
    return a;
}

SplValue spl_array_get(SplArray* a, int64_t idx) {
    if (spl_array_is_nil(a)) return spl_nil();
    if (idx < 0) idx = a->len + idx;
    if (idx < 0 || idx >= a->len) return spl_nil();
    return a->items[idx];
}

void spl_array_set(SplArray* a, int64_t idx, SplValue v) {
    if (spl_array_is_nil(a)) return;
    if (idx < 0) idx = a->len + idx;
    if (idx < 0 || idx >= a->len) return;
    a->items[idx] = v;
}

int64_t spl_array_len(SplArray* a) {
    return spl_array_is_nil(a) ? 0 : a->len;
}

SplValue spl_array_pop(SplArray* a) {
    if (spl_array_is_nil(a) || a->len == 0) return spl_nil();
    return a->items[--a->len];
}

SplArray* spl_array_slice(SplArray* a, int64_t start, int64_t end) {
    if (spl_array_is_nil(a)) return spl_array_new();
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
    int64_t alen = spl_array_is_nil(a) ? 0 : a->len;
    int64_t blen = spl_array_is_nil(b) ? 0 : b->len;
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
    if (spl_array_is_nil(a)) return;
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
    if (spl_array_is_nil(arr) || !needle) return 0;
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

    /* Cache string pointers and lengths to avoid double-strlen */
    int use_heap = (arr->len * (sizeof(size_t) + sizeof(const char*))) > 65536;
    size_t* lens;
    const char** strs;
    if (use_heap) {
        lens = (size_t*)malloc(arr->len * sizeof(size_t));
        strs = (const char**)malloc(arr->len * sizeof(const char*));
    } else {
        lens = (size_t*)alloca(arr->len * sizeof(size_t));
        strs = (const char**)alloca(arr->len * sizeof(const char*));
    }

    size_t total = 0;
    for (int64_t i = 0; i < arr->len; i++) {
        strs[i] = (arr->items[i].tag == SPL_STRING && arr->items[i].as_str)
                   ? arr->items[i].as_str : "";
        lens[i] = strlen(strs[i]);
        total += lens[i];
        if (i < arr->len - 1) total += delim_len;
    }

    char* result = (char*)SPL_MALLOC(total + 1, "str");
    char* dst = result;
    for (int64_t i = 0; i < arr->len; i++) {
        memcpy(dst, strs[i], lens[i]);
        dst += lens[i];
        if (i < arr->len - 1 && delim_len > 0) {
            memcpy(dst, safe_delim, delim_len);
            dst += delim_len;
        }
    }
    *dst = '\0';

    if (use_heap) {
        free(lens);
        free(strs);
    }
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

__attribute__((weak))
const char* rt_env_get(const char* key) {
    return spl_env_get(key);
}

/* spl_env_set — see platform/ headers */

/* ================================================================
 * Memory
 * ================================================================ */

#ifdef USE_MIMALLOC
#include "mimalloc.h"
void* spl_malloc(int64_t size) { return mi_malloc((size_t)size); }
void  spl_free(void* ptr)      { mi_free(ptr); }
#else
void* spl_malloc(int64_t size) {
    return SPL_MALLOC((size_t)size, "user");
}

void spl_free(void* ptr) {
    SPL_FREE(ptr);
}
#endif

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
 * File Prefetch (CLI keyword support)
 * ================================================================ */

#if !defined(_WIN32) && !defined(__EMSCRIPTEN__)
/* ---- POSIX (Linux, macOS, FreeBSD, OpenBSD, NetBSD) ---- */
static pid_t g_prefetch_pid = 0;

void spl_prefetch_start(const char* path) {
    if (!path || !path[0]) return;
    g_prefetch_pid = fork();
    if (g_prefetch_pid == 0) {
        /* Child: mmap file + MADV_POPULATE_READ to warm page cache */
        int fd = open(path, O_RDONLY);
        if (fd >= 0) {
            struct stat st;
            if (fstat(fd, &st) == 0 && st.st_size > 0) {
                void* mapped = mmap(NULL, (size_t)st.st_size, PROT_READ, MAP_PRIVATE, fd, 0);
                if (mapped != MAP_FAILED) {
#ifdef MADV_POPULATE_READ
                    madvise(mapped, (size_t)st.st_size, MADV_POPULATE_READ);
#else
                    madvise(mapped, (size_t)st.st_size, MADV_SEQUENTIAL);
                    /* Touch first byte of each page to force read */
                    volatile char c;
                    for (size_t off = 0; off < (size_t)st.st_size; off += 4096) {
                        c = ((char*)mapped)[off];
                    }
                    (void)c;
#endif
                    munmap(mapped, (size_t)st.st_size);
                }
            }
            close(fd);
        }
        _exit(0);
    }
}

void spl_prefetch_wait(void) {
    if (g_prefetch_pid > 0) {
        int status;
        waitpid(g_prefetch_pid, &status, 0);
        g_prefetch_pid = 0;
    }
}

#elif defined(_WIN32)
/* ---- Windows ---- */
static HANDLE g_prefetch_thread = NULL;

static DWORD WINAPI spl_prefetch_thread_func(LPVOID param) {
    const char* path = (const char*)param;
    HANDLE hFile = CreateFileA(path, GENERIC_READ, FILE_SHARE_READ, NULL,
                               OPEN_EXISTING, FILE_FLAG_SEQUENTIAL_SCAN, NULL);
    if (hFile != INVALID_HANDLE_VALUE) {
        /* Read through the file to populate OS file cache */
        char buf[65536];
        DWORD bytesRead;
        while (ReadFile(hFile, buf, sizeof(buf), &bytesRead, NULL) && bytesRead > 0) {}
        CloseHandle(hFile);
    }
    free((void*)param);
    return 0;
}

void spl_prefetch_start(const char* path) {
    if (!path || !path[0]) return;
    char* path_copy = _strdup(path);
    if (!path_copy) return;
    g_prefetch_thread = CreateThread(NULL, 0, spl_prefetch_thread_func, path_copy, 0, NULL);
}

void spl_prefetch_wait(void) {
    if (g_prefetch_thread) {
        WaitForSingleObject(g_prefetch_thread, INFINITE);
        CloseHandle(g_prefetch_thread);
        g_prefetch_thread = NULL;
    }
}

#else
/* ---- Emscripten / other ---- */
void spl_prefetch_start(const char* path) { (void)path; }
void spl_prefetch_wait(void) {}
#endif

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

typedef struct { struct stat st; } rt_stat_handle;

int64_t rt_stat_open(const char* path) {
    if (!path) return 0;
    rt_stat_handle* h = (rt_stat_handle*)malloc(sizeof(rt_stat_handle));
    if (!h) return 0;
    if (stat(path, &h->st) != 0) { free(h); return 0; }
    return (int64_t)(uintptr_t)h;
}
int64_t rt_file_stat_size(int64_t handle) {
    if (!handle) return 0;
    return (int64_t)((rt_stat_handle*)(uintptr_t)handle)->st.st_size;
}
int64_t rt_file_stat_mtime(int64_t handle) {
    if (!handle) return 0;
    return (int64_t)((rt_stat_handle*)(uintptr_t)handle)->st.st_mtime;
}
int rt_file_stat_is_dir(int64_t handle) {
    if (!handle) return 0;
    return S_ISDIR(((rt_stat_handle*)(uintptr_t)handle)->st.st_mode);
}
int rt_file_stat_is_file(int64_t handle) {
    if (!handle) return 0;
    return S_ISREG(((rt_stat_handle*)(uintptr_t)handle)->st.st_mode);
}
void rt_file_stat_free(int64_t handle) {
    if (handle) free((void*)(uintptr_t)handle);
}

#ifndef _WIN32
typedef struct {
    char** entries;
    int64_t count;
    int64_t cap;
} rt_dir_listing;

int64_t rt_readdir(const char* path) {
    if (!path) return 0;
    DIR* d = opendir(path);
    if (!d) return 0;
    rt_dir_listing* dl = (rt_dir_listing*)calloc(1, sizeof(rt_dir_listing));
    if (!dl) { closedir(d); return 0; }
    dl->cap = 64;
    dl->entries = (char**)malloc(sizeof(char*) * (size_t)dl->cap);
    dl->count = 0;
    struct dirent* ent;
    while ((ent = readdir(d)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        if (dl->count >= dl->cap) {
            dl->cap *= 2;
            dl->entries = (char**)realloc(dl->entries, sizeof(char*) * (size_t)dl->cap);
        }
        dl->entries[dl->count++] = strdup(ent->d_name);
    }
    closedir(d);
    return (int64_t)(uintptr_t)dl;
}
int64_t rt_readdir_count(int64_t handle) {
    if (!handle) return 0;
    return ((rt_dir_listing*)(uintptr_t)handle)->count;
}
const char* rt_readdir_entry(int64_t handle, int64_t index) {
    if (!handle) return "";
    rt_dir_listing* dl = (rt_dir_listing*)(uintptr_t)handle;
    if (index < 0 || index >= dl->count) return "";
    return dl->entries[index];
}
void rt_readdir_free(int64_t handle) {
    if (!handle) return;
    rt_dir_listing* dl = (rt_dir_listing*)(uintptr_t)handle;
    for (int64_t i = 0; i < dl->count; i++) free(dl->entries[i]);
    free(dl->entries);
    free(dl);
}

int64_t rt_mkdir(const char* path, int64_t mode) {
    if (!path) return -1;
    if (mode == 0) mode = 0755;
    return mkdir(path, (mode_t)mode) == 0 ? 0 : -(int64_t)errno;
}

int64_t rt_remove(const char* path) {
    if (!path) return -1;
    struct stat st;
    if (stat(path, &st) != 0) return -(int64_t)errno;
    if (S_ISDIR(st.st_mode))
        return rmdir(path) == 0 ? 0 : -(int64_t)errno;
    return unlink(path) == 0 ? 0 : -(int64_t)errno;
}
#else
int64_t rt_readdir(const char* p) { (void)p; return 0; }
int64_t rt_readdir_count(int64_t h) { (void)h; return 0; }
const char* rt_readdir_entry(int64_t h, int64_t i) { (void)h; (void)i; return ""; }
void rt_readdir_free(int64_t h) { (void)h; }
int64_t rt_mkdir(const char* p, int64_t m) { (void)p; (void)m; return -1; }
int64_t rt_remove(const char* p) { (void)p; return -1; }
#endif

const char* rt_shell_output(const char* cmd) { return spl_shell_output(cmd); }

SplArray* rt_cli_get_args(void) {
    SplArray* arr = spl_array_new();
    for (int i = 0; i < g_argc; i++) {
        spl_array_push(arr, spl_str(g_argv && g_argv[i] ? g_argv[i] : ""));
    }
    return arr;
}

/* rt_ FFI wrappers for prefetch */
void rt_prefetch_start(const char* path) { spl_prefetch_start(path); }
void rt_prefetch_wait(void) { spl_prefetch_wait(); }

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

/* spl_wffi_call_i64 is now provided by Rust (wffi_native.rs) which accepts
 * tagged RuntimeValues. This C version is kept for C-only tests. */
int64_t spl_wffi_call_i64_c(void* fptr, int64_t* args, int64_t nargs) {
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
    const char* safe_msg = msg ? msg : "unknown error";
    fprintf(stderr, "PANIC: %s\n", safe_msg);

    /* Write crash log to file (best-effort, all platforms with stdio) */
    {
        char crash_path[512];
        const char* log_dir = getenv("SIMPLE_LOG_DIR");
#if defined(_WIN32)
        const char* tmp = log_dir ? log_dir : (getenv("TEMP") ? getenv("TEMP") : ".");
#elif defined(__linux__) || defined(__APPLE__) || defined(__FreeBSD__)
        const char* tmp = log_dir ? log_dir : "/tmp";
#else
        /* Baremetal / unknown: try current dir */
        const char* tmp = log_dir ? log_dir : ".";
#endif
        snprintf(crash_path, sizeof(crash_path), "%s/simple_crash_%d.log",
                 tmp, (int)getpid());
        FILE* f = fopen(crash_path, "a");
        if (f) {
            fprintf(f, "=== SIMPLE C RUNTIME CRASH ===\n");
            fprintf(f, "PID: %d\n", (int)getpid());
            fprintf(f, "Message: %s\n", safe_msg);
            fprintf(f, "==============================\n\n");
            fclose(f);
            fprintf(stderr, "[crash] report written to %s\n", crash_path);
        }
    }

    exit(1);
}

/* ================================================================
 * Signal Handling
 * ================================================================ */

static volatile sig_atomic_t _signal_flags[32] = {0};
static volatile sig_atomic_t _atexit_flag = 0;

static void _spl_signal_handler(int signum) {
    if (signum >= 0 && signum < 32) {
        _signal_flags[signum] = 1;
    }
}

static void _spl_atexit_handler(void) {
    _atexit_flag = 1;
}

int64_t rt_signal_install(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32) return 0;
    struct sigaction sa;
    sa.sa_handler = _spl_signal_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = SA_RESTART;
    if (sigaction((int)signal_num, &sa, NULL) == -1) return 0;
    return 1;
}

int64_t rt_signal_check(int64_t signal_num) {
    if (signal_num < 0 || signal_num >= 32) return 0;
    if (_signal_flags[signal_num]) {
        _signal_flags[signal_num] = 0;
        return 1;
    }
    return 0;
}

int64_t rt_atexit_install(void) {
    static int installed = 0;
    if (!installed) {
        atexit(_spl_atexit_handler);
        installed = 1;
    }
    return 1;
}

int64_t rt_atexit_check(void) {
    if (_atexit_flag) {
        _atexit_flag = 0;
        return 1;
    }
    return 0;
}

/* ================================================================
 * Byte / Encoding / Crypto / Network Externs
 * ================================================================ */

/* ---- rt_byte_char: integer 0-255 -> 1-byte string ---- */
const char* rt_byte_char(int64_t v) {
    /* Returns a malloc'd 2-byte buffer: [byte_value, '\0'].
     * Note: rt_byte_char(0) returns a string whose first byte is NUL,
     * so strlen() will report 0. This is intentional for binary wire use. */
    char* buf = (char*)SPL_MALLOC(2, "str");
    buf[0] = (char)(unsigned char)(v & 0xFF);
    buf[1] = '\0';
    return buf;
}

/* ---- rt_time_now_seconds: Unix timestamp in seconds ---- */
int64_t rt_time_now_seconds(void) {
    return (int64_t)time(NULL);
}

/* ---- rt_random_i64: cryptographically random i64 ---- */
int64_t rt_random_i64(void) {
#ifdef _WIN32
    /* Windows: BCryptGenRandom */
    int64_t val = 0;
    /* Link with bcrypt.lib; BCryptGenRandom is available on Vista+ */
    typedef long (WINAPI *BCryptGenRandomFn)(void*, unsigned char*, unsigned long, unsigned long);
    HMODULE hLib = LoadLibraryA("bcrypt.dll");
    if (hLib) {
        BCryptGenRandomFn fn = (BCryptGenRandomFn)GetProcAddress(hLib, "BCryptGenRandom");
        if (fn) {
            /* BCRYPT_USE_SYSTEM_PREFERRED_RNG = 0x00000002 */
            fn(NULL, (unsigned char*)&val, sizeof(val), 0x00000002);
        }
        FreeLibrary(hLib);
    }
    return val;
#else
    /* Unix: /dev/urandom */
    int64_t val = 0;
    int fd = open("/dev/urandom", O_RDONLY);
    if (fd >= 0) {
        ssize_t n = read(fd, &val, sizeof(val));
        (void)n;
        close(fd);
    }
    return val;
#endif
}

/* ---- Base64url (RFC 4648 section 5) ---- */

static const char b64url_enc_table[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789-_";

const char* rt_base64url_encode(const char* input, int64_t len) {
    if (!input || len <= 0) return SPL_STRDUP("", "str");
    size_t in_len = (size_t)len;
    size_t out_len = ((in_len + 2) / 3) * 4;
    char* out = (char*)SPL_MALLOC(out_len + 1, "str");
    size_t j = 0;
    for (size_t i = 0; i < in_len; ) {
        uint32_t a = (unsigned char)input[i++];
        uint32_t b = (i < in_len) ? (unsigned char)input[i++] : 0;
        uint32_t c = (i < in_len) ? (unsigned char)input[i++] : 0;
        uint32_t triple = (a << 16) | (b << 8) | c;
        out[j++] = b64url_enc_table[(triple >> 18) & 0x3F];
        out[j++] = b64url_enc_table[(triple >> 12) & 0x3F];
        out[j++] = b64url_enc_table[(triple >>  6) & 0x3F];
        out[j++] = b64url_enc_table[(triple      ) & 0x3F];
    }
    /* Strip padding: no '=' in base64url (RFC 4648 section 5) */
    size_t rem = in_len % 3;
    if (rem == 1) j -= 2;
    else if (rem == 2) j -= 1;
    out[j] = '\0';
    return out;
}

static int b64url_decode_char(char c) {
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '-') return 62;
    if (c == '_') return 63;
    return -1;
}

const char* rt_base64url_decode(const char* input) {
    if (!input || !*input) return SPL_STRDUP("", "str");
    size_t in_len = strlen(input);
    /* Pad to multiple of 4 for decoding */
    size_t padded = in_len;
    if (padded % 4 != 0) padded += 4 - (padded % 4);
    size_t out_max = (padded / 4) * 3;
    char* out = (char*)SPL_MALLOC(out_max + 1, "str");
    size_t j = 0;
    for (size_t i = 0; i < padded; i += 4) {
        int a = (i     < in_len) ? b64url_decode_char(input[i])     : 0;
        int b = (i + 1 < in_len) ? b64url_decode_char(input[i + 1]) : 0;
        int c = (i + 2 < in_len) ? b64url_decode_char(input[i + 2]) : -1;
        int d = (i + 3 < in_len) ? b64url_decode_char(input[i + 3]) : -1;
        if (a < 0) a = 0;
        if (b < 0) b = 0;
        uint32_t triple = ((uint32_t)a << 18) | ((uint32_t)b << 12);
        if (c >= 0) triple |= ((uint32_t)c << 6);
        if (d >= 0) triple |= (uint32_t)d;
        out[j++] = (char)((triple >> 16) & 0xFF);
        if (c >= 0 || (i + 2 < in_len)) out[j++] = (char)((triple >> 8) & 0xFF);
        if (d >= 0 || (i + 3 < in_len)) out[j++] = (char)(triple & 0xFF);
    }
    out[j] = '\0';
    return out;
}

/* ---- SHA-1 (RFC 3174) — minimal inline implementation ---- */

static void sha1_process_block(uint32_t state[5], const uint8_t block[64]) {
    uint32_t w[80];
    for (int i = 0; i < 16; i++) {
        w[i] = ((uint32_t)block[i*4] << 24) | ((uint32_t)block[i*4+1] << 16) |
                ((uint32_t)block[i*4+2] << 8) | (uint32_t)block[i*4+3];
    }
    for (int i = 16; i < 80; i++) {
        uint32_t t = w[i-3] ^ w[i-8] ^ w[i-14] ^ w[i-16];
        w[i] = (t << 1) | (t >> 31);
    }
    uint32_t a = state[0], b = state[1], c = state[2], d = state[3], e = state[4];
    for (int i = 0; i < 80; i++) {
        uint32_t f, k;
        if (i < 20)      { f = (b & c) | ((~b) & d);          k = 0x5A827999; }
        else if (i < 40) { f = b ^ c ^ d;                      k = 0x6ED9EBA1; }
        else if (i < 60) { f = (b & c) | (b & d) | (c & d);   k = 0x8F1BBCDC; }
        else              { f = b ^ c ^ d;                      k = 0xCA62C1D6; }
        uint32_t temp = ((a << 5) | (a >> 27)) + f + e + k + w[i];
        e = d; d = c; c = (b << 30) | (b >> 2); b = a; a = temp;
    }
    state[0] += a; state[1] += b; state[2] += c; state[3] += d; state[4] += e;
}

const char* rt_sha1(const char* data) {
    if (!data) return SPL_STRDUP("da39a3ee5e6b4b0d3255bfef95601890afd80709", "str"); /* SHA-1 of "" */
    size_t len = strlen(data);
    uint32_t state[5] = { 0x67452301, 0xEFCDAB89, 0x98BADCFE, 0x10325476, 0xC3D2E1F0 };
    /* Process full blocks */
    size_t i;
    for (i = 0; i + 64 <= len; i += 64) {
        sha1_process_block(state, (const uint8_t*)(data + i));
    }
    /* Final block(s) with padding */
    uint8_t block[128]; /* up to 2 blocks for final padding */
    size_t rem = len - i;
    memcpy(block, data + i, rem);
    block[rem++] = 0x80;
    if (rem > 56) {
        /* Need two blocks */
        memset(block + rem, 0, 64 - rem);
        sha1_process_block(state, block);
        memset(block, 0, 56);
    } else {
        memset(block + rem, 0, 56 - rem);
    }
    /* Append bit length (big-endian 64-bit) */
    uint64_t bit_len = (uint64_t)len * 8;
    block[56] = (uint8_t)(bit_len >> 56);
    block[57] = (uint8_t)(bit_len >> 48);
    block[58] = (uint8_t)(bit_len >> 40);
    block[59] = (uint8_t)(bit_len >> 32);
    block[60] = (uint8_t)(bit_len >> 24);
    block[61] = (uint8_t)(bit_len >> 16);
    block[62] = (uint8_t)(bit_len >>  8);
    block[63] = (uint8_t)(bit_len);
    sha1_process_block(state, block);
    /* Format as 40-char hex string */
    char* hex = (char*)SPL_MALLOC(41, "str");
    snprintf(hex, 41, "%08x%08x%08x%08x%08x",
             state[0], state[1], state[2], state[3], state[4]);
    return hex;
}

/* ---- rt_http_get: minimal sync HTTP GET (POSIX sockets) ----
 * Returns body text after headers. Empty string on error.
 * WARNING: .spl callers declare conflicting signatures for this function:
 *   http_ffi.spl: -> (i64, text, text)   (tuple)
 *   service_adapter.spl: -> {text: text}  (dict)
 * This C implementation returns const char* (body only) per task spec.
 * Callers using tuple/dict signatures will need .spl-side adaptation. */
#ifndef _WIN32
#include <netdb.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#endif

const char* rt_http_get(const char* url) {
    if (!url) return SPL_STRDUP("", "str");
#ifdef _WIN32
    /* Minimal Windows stub — would need Winsock init */
    (void)url;
    return SPL_STRDUP("", "str");
#else
    /* Parse URL: http://host[:port]/path */
    if (strncmp(url, "http://", 7) != 0) return SPL_STRDUP("", "str");
    const char* host_start = url + 7;
    const char* path_start = strchr(host_start, '/');
    const char* path = path_start ? path_start : "/";
    /* Extract host and port */
    char host[256];
    int port = 80;
    size_t host_len;
    const char* colon = NULL;
    const char* host_end = path_start ? path_start : host_start + strlen(host_start);
    /* Search for port separator only within host part */
    for (const char* p = host_start; p < host_end; p++) {
        if (*p == ':') { colon = p; break; }
    }
    if (colon && colon < host_end) {
        host_len = (size_t)(colon - host_start);
        port = atoi(colon + 1);
        if (port <= 0 || port > 65535) port = 80;
    } else {
        host_len = (size_t)(host_end - host_start);
    }
    if (host_len >= sizeof(host)) host_len = sizeof(host) - 1;
    memcpy(host, host_start, host_len);
    host[host_len] = '\0';
    /* DNS resolve */
    struct addrinfo hints, *res;
    memset(&hints, 0, sizeof(hints));
    hints.ai_family = AF_UNSPEC;
    hints.ai_socktype = SOCK_STREAM;
    char port_str[8];
    snprintf(port_str, sizeof(port_str), "%d", port);
    if (getaddrinfo(host, port_str, &hints, &res) != 0)
        return SPL_STRDUP("", "str");
    int sock = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (sock < 0) { freeaddrinfo(res); return SPL_STRDUP("", "str"); }
    if (connect(sock, res->ai_addr, res->ai_addrlen) != 0) {
        close(sock); freeaddrinfo(res); return SPL_STRDUP("", "str");
    }
    freeaddrinfo(res);
    /* Send HTTP request */
    char req[4096];
    int req_len = snprintf(req, sizeof(req),
        "GET %s HTTP/1.1\r\nHost: %s\r\nConnection: close\r\n\r\n", path, host);
    if (send(sock, req, (size_t)req_len, 0) < 0) {
        close(sock); return SPL_STRDUP("", "str");
    }
    /* Read response */
    size_t buf_cap = 8192;
    size_t buf_len = 0;
    char* buf = (char*)SPL_MALLOC(buf_cap, "str");
    ssize_t n;
    while ((n = recv(sock, buf + buf_len, buf_cap - buf_len - 1, 0)) > 0) {
        buf_len += (size_t)n;
        if (buf_len + 1 >= buf_cap) {
            buf_cap *= 2;
            buf = (char*)SPL_REALLOC(buf, buf_cap, "str");
        }
    }
    close(sock);
    buf[buf_len] = '\0';
    /* Find end of headers */
    char* body = strstr(buf, "\r\n\r\n");
    if (body) {
        body += 4;
        char* result = SPL_STRDUP(body, "str");
        SPL_FREE(buf);
        return result;
    }
    /* No header separator found — return empty */
    SPL_FREE(buf);
    return SPL_STRDUP("", "str");
#endif
}

/* ================================================================
 * TLS Crypto Externs — AES-128-GCM + RSA PKCS#1 v1.5
 * ================================================================
 *
 * IMPORTANT — NUL byte limitation:
 * The strlen-based wrappers (rt_aes_gcm_encrypt, rt_aes_gcm_decrypt,
 * rt_rsa_decrypt) truncate at embedded NUL bytes (0x00).  For correct
 * TLS operation with arbitrary key material, use the _with_len variants
 * which accept explicit lengths and report output length via int64_t*
 * out_len outparam.
 *
 * The _with_len API is the canonical binary-safe interface; the plain
 * functions are thin wrappers that call strlen on each argument.
 * ================================================================ */

/* --- OpenSSL is opt-in only ---
 * Pass -DSPL_HAVE_OPENSSL and link -lssl -lcrypto to enable.
 * Without it, AES-128-GCM uses the from-scratch implementation below
 * (byte-identical output verified against OpenSSL 3.x).
 * RSA decryption requires OpenSSL — the no-OpenSSL path is a stub. */

#ifdef SPL_HAVE_OPENSSL
#include <openssl/evp.h>
#include <openssl/rsa.h>
#include <openssl/pem.h>
#include <openssl/err.h>
#include <openssl/bio.h>

/* ---- rt_rsa_decrypt_with_len: binary-safe RSA PKCS#1 v1.5 (OpenSSL) ---- */
const char* rt_rsa_decrypt_with_len(const char* ciphertext, int64_t ct_len,
                                     const char* private_key_pem, int64_t pk_len,
                                     int64_t* out_len) {
    if (out_len) *out_len = 0;
    if (!ciphertext || !private_key_pem || ct_len <= 0 || pk_len <= 0)
        return SPL_STRDUP("", "str");

    BIO* bio = BIO_new_mem_buf(private_key_pem, (int)pk_len);
    if (!bio) return SPL_STRDUP("", "str");

    EVP_PKEY* pkey = PEM_read_bio_PrivateKey(bio, NULL, NULL, NULL);
    BIO_free(bio);
    if (!pkey) return SPL_STRDUP("", "str");

    EVP_PKEY_CTX* ctx = EVP_PKEY_CTX_new(pkey, NULL);
    if (!ctx) { EVP_PKEY_free(pkey); return SPL_STRDUP("", "str"); }

    if (EVP_PKEY_decrypt_init(ctx) <= 0) {
        EVP_PKEY_CTX_free(ctx); EVP_PKEY_free(pkey);
        return SPL_STRDUP("", "str");
    }
    if (EVP_PKEY_CTX_set_rsa_padding(ctx, RSA_PKCS1_PADDING) <= 0) {
        EVP_PKEY_CTX_free(ctx); EVP_PKEY_free(pkey);
        return SPL_STRDUP("", "str");
    }

    size_t dec_len = 0;
    if (EVP_PKEY_decrypt(ctx, NULL, &dec_len,
                         (const unsigned char*)ciphertext, (size_t)ct_len) <= 0) {
        EVP_PKEY_CTX_free(ctx); EVP_PKEY_free(pkey);
        return SPL_STRDUP("", "str");
    }

    unsigned char* result = (unsigned char*)SPL_MALLOC(dec_len + 1, "str");
    if (EVP_PKEY_decrypt(ctx, result, &dec_len,
                         (const unsigned char*)ciphertext, (size_t)ct_len) <= 0) {
        SPL_FREE(result);
        EVP_PKEY_CTX_free(ctx); EVP_PKEY_free(pkey);
        return SPL_STRDUP("", "str");
    }

    EVP_PKEY_CTX_free(ctx);
    EVP_PKEY_free(pkey);

    result[dec_len] = '\0';
    if (out_len) *out_len = (int64_t)dec_len;
    return (const char*)result;
}

const char* rt_rsa_decrypt(const char* ciphertext, const char* private_key_pem) {
    if (!ciphertext || !private_key_pem) return SPL_STRDUP("", "str");
    return rt_rsa_decrypt_with_len(ciphertext, (int64_t)strlen(ciphertext),
                                    private_key_pem, (int64_t)strlen(private_key_pem),
                                    NULL);
}

/* ---- rt_aes_gcm_encrypt_with_len: binary-safe AES-128-GCM encrypt (OpenSSL) ---- */
const char* rt_aes_gcm_encrypt_with_len(const char* key, int64_t key_len,
                                         const char* iv, int64_t iv_len,
                                         const char* plaintext, int64_t pt_len,
                                         const char* aad, int64_t aad_len,
                                         int64_t* out_len) {
    if (out_len) *out_len = 0;
    if (!key || !iv || !plaintext || key_len < 16 || iv_len < 12 || pt_len < 0)
        return SPL_STRDUP("", "str");

    EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
    if (!ctx) return SPL_STRDUP("", "str");

    if (EVP_EncryptInit_ex(ctx, EVP_aes_128_gcm(), NULL, NULL, NULL) != 1) {
        EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
    }
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, (int)iv_len, NULL) != 1) {
        EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
    }
    if (EVP_EncryptInit_ex(ctx, NULL, NULL,
                           (const unsigned char*)key,
                           (const unsigned char*)iv) != 1) {
        EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
    }

    int tmp_len = 0;
    if (aad && aad_len > 0) {
        if (EVP_EncryptUpdate(ctx, NULL, &tmp_len,
                              (const unsigned char*)aad, (int)aad_len) != 1) {
            EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
        }
    }

    /* Output: ciphertext (same length as plaintext) + 16-byte GCM tag */
    unsigned char* result = (unsigned char*)SPL_MALLOC((size_t)pt_len + 16 + 1, "str");
    int enc_len = 0;
    if (EVP_EncryptUpdate(ctx, result, &enc_len,
                          (const unsigned char*)plaintext, (int)pt_len) != 1) {
        SPL_FREE(result); EVP_CIPHER_CTX_free(ctx);
        return SPL_STRDUP("", "str");
    }

    int final_len = 0;
    if (EVP_EncryptFinal_ex(ctx, result + enc_len, &final_len) != 1) {
        SPL_FREE(result); EVP_CIPHER_CTX_free(ctx);
        return SPL_STRDUP("", "str");
    }
    enc_len += final_len;

    /* Append 16-byte GCM authentication tag */
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_GET_TAG, 16, result + enc_len) != 1) {
        SPL_FREE(result); EVP_CIPHER_CTX_free(ctx);
        return SPL_STRDUP("", "str");
    }
    enc_len += 16;

    EVP_CIPHER_CTX_free(ctx);
    result[enc_len] = '\0';
    if (out_len) *out_len = (int64_t)enc_len;
    return (const char*)result;
}

const char* rt_aes_gcm_encrypt(const char* key, const char* iv,
                                const char* plaintext, const char* aad) {
    if (!key || !iv || !plaintext) return SPL_STRDUP("", "str");
    return rt_aes_gcm_encrypt_with_len(key, (int64_t)strlen(key),
                                        iv, (int64_t)strlen(iv),
                                        plaintext, (int64_t)strlen(plaintext),
                                        aad, aad ? (int64_t)strlen(aad) : 0,
                                        NULL);
}

/* ---- rt_aes_gcm_decrypt_with_len: binary-safe AES-128-GCM decrypt (OpenSSL) ---- */
const char* rt_aes_gcm_decrypt_with_len(const char* key, int64_t key_len,
                                         const char* iv, int64_t iv_len,
                                         const char* ciphertext, int64_t ct_len,
                                         const char* aad, int64_t aad_len,
                                         int64_t* out_len) {
    if (out_len) *out_len = 0;
    if (!key || !iv || !ciphertext || key_len < 16 || iv_len < 12 || ct_len < 16)
        return SPL_STRDUP("", "str");

    int64_t actual_ct_len = ct_len - 16; /* last 16 bytes are the GCM tag */

    EVP_CIPHER_CTX* ctx = EVP_CIPHER_CTX_new();
    if (!ctx) return SPL_STRDUP("", "str");

    if (EVP_DecryptInit_ex(ctx, EVP_aes_128_gcm(), NULL, NULL, NULL) != 1) {
        EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
    }
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_IVLEN, (int)iv_len, NULL) != 1) {
        EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
    }
    if (EVP_DecryptInit_ex(ctx, NULL, NULL,
                           (const unsigned char*)key,
                           (const unsigned char*)iv) != 1) {
        EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
    }

    int tmp_len = 0;
    if (aad && aad_len > 0) {
        if (EVP_DecryptUpdate(ctx, NULL, &tmp_len,
                              (const unsigned char*)aad, (int)aad_len) != 1) {
            EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
        }
    }

    /* Set expected GCM tag (last 16 bytes of ciphertext buffer) */
    if (EVP_CIPHER_CTX_ctrl(ctx, EVP_CTRL_GCM_SET_TAG, 16,
                            (void*)((const unsigned char*)ciphertext + actual_ct_len)) != 1) {
        EVP_CIPHER_CTX_free(ctx); return SPL_STRDUP("", "str");
    }

    unsigned char* result = (unsigned char*)SPL_MALLOC((size_t)actual_ct_len + 1, "str");
    int dec_len = 0;
    if (EVP_DecryptUpdate(ctx, result, &dec_len,
                          (const unsigned char*)ciphertext, (int)actual_ct_len) != 1) {
        SPL_FREE(result); EVP_CIPHER_CTX_free(ctx);
        return SPL_STRDUP("", "str");
    }

    int final_len = 0;
    if (EVP_DecryptFinal_ex(ctx, result + dec_len, &final_len) != 1) {
        /* Authentication failed */
        SPL_FREE(result); EVP_CIPHER_CTX_free(ctx);
        return SPL_STRDUP("", "str");
    }
    dec_len += final_len;

    EVP_CIPHER_CTX_free(ctx);
    result[dec_len] = '\0';
    if (out_len) *out_len = (int64_t)dec_len;
    return (const char*)result;
}

const char* rt_aes_gcm_decrypt(const char* key, const char* iv,
                                const char* ciphertext, const char* aad) {
    if (!key || !iv || !ciphertext) return SPL_STRDUP("", "str");
    return rt_aes_gcm_decrypt_with_len(key, (int64_t)strlen(key),
                                        iv, (int64_t)strlen(iv),
                                        ciphertext, (int64_t)strlen(ciphertext),
                                        aad, aad ? (int64_t)strlen(aad) : 0,
                                        NULL);
}

#else /* !SPL_HAVE_OPENSSL — from-scratch AES-128-GCM implementation */

/* ================================================================
 * AES-128 Core (FIPS 197) — SubBytes, ShiftRows, MixColumns, 10 rounds
 * ================================================================ */

static const uint8_t aes_sbox[256] = {
    0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
    0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
    0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
    0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
    0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
    0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
    0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
    0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
    0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
    0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
    0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
    0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
    0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
    0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
    0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
    0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16
};

static const uint8_t aes_rcon[11] = {
    0x00, 0x01, 0x02, 0x04, 0x08, 0x10, 0x20, 0x40, 0x80, 0x1b, 0x36
};

/* GF(2^8) multiplication */
static uint8_t gf_mul(uint8_t a, uint8_t b) {
    uint8_t result = 0;
    for (int i = 0; i < 8; i++) {
        if (b & 1) result ^= a;
        uint8_t hi = a & 0x80;
        a <<= 1;
        if (hi) a ^= 0x1b; /* x^8 + x^4 + x^3 + x + 1 */
        b >>= 1;
    }
    return result;
}

/* AES-128 key expansion: 16-byte key -> 11 round keys (176 bytes) */
static void aes128_expand_key(const uint8_t key[16], uint8_t round_keys[176]) {
    memcpy(round_keys, key, 16);
    for (int i = 4; i < 44; i++) {
        uint8_t temp[4];
        memcpy(temp, round_keys + (i - 1) * 4, 4);
        if (i % 4 == 0) {
            uint8_t t = temp[0];
            temp[0] = aes_sbox[temp[1]] ^ aes_rcon[i / 4];
            temp[1] = aes_sbox[temp[2]];
            temp[2] = aes_sbox[temp[3]];
            temp[3] = aes_sbox[t];
        }
        for (int j = 0; j < 4; j++)
            round_keys[i * 4 + j] = round_keys[(i - 4) * 4 + j] ^ temp[j];
    }
}

/* AES-128 encrypt a single 16-byte block in-place */
static void aes128_encrypt_block(const uint8_t round_keys[176], uint8_t block[16]) {
    for (int i = 0; i < 16; i++) block[i] ^= round_keys[i];

    for (int round = 1; round <= 10; round++) {
        /* SubBytes */
        for (int i = 0; i < 16; i++) block[i] = aes_sbox[block[i]];

        /* ShiftRows */
        uint8_t t;
        t = block[1]; block[1] = block[5]; block[5] = block[9]; block[9] = block[13]; block[13] = t;
        t = block[2]; block[2] = block[10]; block[10] = t;
        t = block[6]; block[6] = block[14]; block[14] = t;
        t = block[15]; block[15] = block[11]; block[11] = block[7]; block[7] = block[3]; block[3] = t;

        /* MixColumns (skip on last round) */
        if (round < 10) {
            for (int c = 0; c < 4; c++) {
                int off = c * 4;
                uint8_t a0 = block[off], a1 = block[off+1], a2 = block[off+2], a3 = block[off+3];
                block[off]   = gf_mul(2,a0) ^ gf_mul(3,a1) ^ a2 ^ a3;
                block[off+1] = a0 ^ gf_mul(2,a1) ^ gf_mul(3,a2) ^ a3;
                block[off+2] = a0 ^ a1 ^ gf_mul(2,a2) ^ gf_mul(3,a3);
                block[off+3] = gf_mul(3,a0) ^ a1 ^ a2 ^ gf_mul(2,a3);
            }
        }

        /* AddRoundKey */
        for (int i = 0; i < 16; i++) block[i] ^= round_keys[round * 16 + i];
    }
}

/* ================================================================
 * GCM Mode — GHASH + CTR
 * ================================================================ */

static void xor_block(uint8_t out[16], const uint8_t a[16], const uint8_t b[16]) {
    for (int i = 0; i < 16; i++) out[i] = a[i] ^ b[i];
}

/* GF(2^128) multiplication for GHASH (bit-by-bit, big-endian) */
static void ghash_mul(uint8_t result[16], const uint8_t X[16], const uint8_t H[16]) {
    uint8_t Z[16] = {0};
    uint8_t V[16];
    memcpy(V, H, 16);

    for (int i = 0; i < 128; i++) {
        if (X[i / 8] & (0x80 >> (i % 8))) {
            for (int j = 0; j < 16; j++) Z[j] ^= V[j];
        }
        uint8_t carry = V[15] & 1;
        for (int j = 15; j > 0; j--) V[j] = (V[j] >> 1) | (V[j-1] << 7);
        V[0] >>= 1;
        if (carry) V[0] ^= 0xe1; /* x^128 + x^7 + x^2 + x + 1 */
    }
    memcpy(result, Z, 16);
}

/* GHASH: process AAD and ciphertext, produce tag input */
static void ghash(const uint8_t H[16],
                  const uint8_t* aad, size_t aad_len,
                  const uint8_t* ct, size_t ct_len,
                  uint8_t out[16]) {
    uint8_t Y[16] = {0};
    uint8_t tmp[16];

    size_t i;
    for (i = 0; i + 16 <= aad_len; i += 16) {
        xor_block(tmp, Y, aad + i);
        ghash_mul(Y, tmp, H);
    }
    if (i < aad_len) {
        uint8_t pad[16] = {0};
        memcpy(pad, aad + i, aad_len - i);
        xor_block(tmp, Y, pad);
        ghash_mul(Y, tmp, H);
    }

    for (i = 0; i + 16 <= ct_len; i += 16) {
        xor_block(tmp, Y, ct + i);
        ghash_mul(Y, tmp, H);
    }
    if (i < ct_len) {
        uint8_t pad[16] = {0};
        memcpy(pad, ct + i, ct_len - i);
        xor_block(tmp, Y, pad);
        ghash_mul(Y, tmp, H);
    }

    /* Final block: len(A) || len(C) in bits, 64-bit big-endian each */
    uint8_t len_block[16] = {0};
    uint64_t aad_bits = (uint64_t)aad_len * 8;
    uint64_t ct_bits  = (uint64_t)ct_len * 8;
    len_block[0] = (uint8_t)(aad_bits >> 56); len_block[1] = (uint8_t)(aad_bits >> 48);
    len_block[2] = (uint8_t)(aad_bits >> 40); len_block[3] = (uint8_t)(aad_bits >> 32);
    len_block[4] = (uint8_t)(aad_bits >> 24); len_block[5] = (uint8_t)(aad_bits >> 16);
    len_block[6] = (uint8_t)(aad_bits >>  8); len_block[7] = (uint8_t)(aad_bits);
    len_block[8]  = (uint8_t)(ct_bits >> 56); len_block[9]  = (uint8_t)(ct_bits >> 48);
    len_block[10] = (uint8_t)(ct_bits >> 40); len_block[11] = (uint8_t)(ct_bits >> 32);
    len_block[12] = (uint8_t)(ct_bits >> 24); len_block[13] = (uint8_t)(ct_bits >> 16);
    len_block[14] = (uint8_t)(ct_bits >>  8); len_block[15] = (uint8_t)(ct_bits);

    xor_block(tmp, Y, len_block);
    ghash_mul(out, tmp, H);
}

/* Increment rightmost 32 bits of 16-byte counter (big-endian) */
static void gcm_inc32(uint8_t counter[16]) {
    for (int i = 15; i >= 12; i--) {
        if (++counter[i] != 0) break;
    }
}

/* AES-GCM encrypt: returns ciphertext in out, tag in tag; 0 on success */
static int aes_gcm_encrypt_impl(const uint8_t* key, size_t key_len,
                                 const uint8_t* iv, size_t iv_len,
                                 const uint8_t* pt, size_t pt_len,
                                 const uint8_t* aad, size_t aad_len,
                                 uint8_t* out, uint8_t tag[16]) {
    if (key_len != 16) return -1;

    uint8_t round_keys[176];
    aes128_expand_key(key, round_keys);

    uint8_t H[16] = {0};
    aes128_encrypt_block(round_keys, H);

    uint8_t J0[16] = {0};
    if (iv_len == 12) {
        memcpy(J0, iv, 12);
        J0[15] = 1;
    } else {
        ghash(H, NULL, 0, iv, iv_len, J0);
    }

    uint8_t E_J0[16];
    memcpy(E_J0, J0, 16);
    aes128_encrypt_block(round_keys, E_J0);

    uint8_t counter[16];
    memcpy(counter, J0, 16);

    for (size_t i = 0; i < pt_len; i += 16) {
        gcm_inc32(counter);
        uint8_t keystream[16];
        memcpy(keystream, counter, 16);
        aes128_encrypt_block(round_keys, keystream);

        size_t block_len = (pt_len - i < 16) ? (pt_len - i) : 16;
        for (size_t j = 0; j < block_len; j++)
            out[i + j] = pt[i + j] ^ keystream[j];
    }

    uint8_t ghash_out[16];
    ghash(H, aad, aad_len, out, pt_len, ghash_out);
    xor_block(tag, ghash_out, E_J0);
    return 0;
}

/* AES-GCM decrypt: returns 0 on success (tag verified), -1 on failure */
static int aes_gcm_decrypt_impl(const uint8_t* key, size_t key_len,
                                 const uint8_t* iv, size_t iv_len,
                                 const uint8_t* ct, size_t ct_len,
                                 const uint8_t* aad, size_t aad_len,
                                 const uint8_t expected_tag[16],
                                 uint8_t* out) {
    if (key_len != 16) return -1;

    uint8_t round_keys[176];
    aes128_expand_key(key, round_keys);

    uint8_t H[16] = {0};
    aes128_encrypt_block(round_keys, H);

    uint8_t J0[16] = {0};
    if (iv_len == 12) {
        memcpy(J0, iv, 12);
        J0[15] = 1;
    } else {
        ghash(H, NULL, 0, iv, iv_len, J0);
    }

    uint8_t E_J0[16];
    memcpy(E_J0, J0, 16);
    aes128_encrypt_block(round_keys, E_J0);

    /* Verify tag before decrypting */
    uint8_t ghash_out[16];
    ghash(H, aad, aad_len, ct, ct_len, ghash_out);

    uint8_t computed_tag[16];
    xor_block(computed_tag, ghash_out, E_J0);

    /* Constant-time tag comparison */
    uint8_t diff = 0;
    for (int i = 0; i < 16; i++) diff |= computed_tag[i] ^ expected_tag[i];
    if (diff != 0) return -1;

    /* CTR mode decryption */
    uint8_t counter[16];
    memcpy(counter, J0, 16);

    for (size_t i = 0; i < ct_len; i += 16) {
        gcm_inc32(counter);
        uint8_t keystream[16];
        memcpy(keystream, counter, 16);
        aes128_encrypt_block(round_keys, keystream);

        size_t block_len = (ct_len - i < 16) ? (ct_len - i) : 16;
        for (size_t j = 0; j < block_len; j++)
            out[i + j] = ct[i + j] ^ keystream[j];
    }

    return 0;
}

/* ---- rt_rsa_decrypt: stub without OpenSSL ---- */
const char* rt_rsa_decrypt_with_len(const char* ciphertext, int64_t ct_len,
                                     const char* private_key_pem, int64_t pk_len,
                                     int64_t* out_len) {
    (void)ciphertext; (void)ct_len;
    (void)private_key_pem; (void)pk_len;
    if (out_len) *out_len = 0;
    fprintf(stderr, "rt_rsa_decrypt: OpenSSL not available, RSA decryption unsupported\n");
    return SPL_STRDUP("", "str");
}

const char* rt_rsa_decrypt(const char* ciphertext, const char* private_key_pem) {
    (void)ciphertext; (void)private_key_pem;
    fprintf(stderr, "rt_rsa_decrypt: OpenSSL not available, RSA decryption unsupported\n");
    return SPL_STRDUP("", "str");
}

/* ---- rt_aes_gcm_encrypt_with_len: binary-safe (from-scratch fallback) ---- */
const char* rt_aes_gcm_encrypt_with_len(const char* key, int64_t key_len,
                                         const char* iv, int64_t iv_len,
                                         const char* plaintext, int64_t pt_len,
                                         const char* aad, int64_t aad_len,
                                         int64_t* out_len) {
    if (out_len) *out_len = 0;
    if (!key || !iv || !plaintext || key_len < 16 || iv_len < 12 || pt_len < 0)
        return SPL_STRDUP("", "str");

    uint8_t* ct_buf = (uint8_t*)SPL_MALLOC((size_t)pt_len + 16 + 1, "str");
    uint8_t tag[16];

    if (aes_gcm_encrypt_impl((const uint8_t*)key, 16,
                              (const uint8_t*)iv, (size_t)iv_len,
                              (const uint8_t*)plaintext, (size_t)pt_len,
                              aad ? (const uint8_t*)aad : (const uint8_t*)"",
                              aad ? (size_t)aad_len : 0,
                              ct_buf, tag) != 0) {
        SPL_FREE(ct_buf);
        return SPL_STRDUP("", "str");
    }

    memcpy(ct_buf + pt_len, tag, 16);
    ct_buf[pt_len + 16] = '\0';
    if (out_len) *out_len = (int64_t)pt_len + 16;
    return (const char*)ct_buf;
}

const char* rt_aes_gcm_encrypt(const char* key, const char* iv,
                                const char* plaintext, const char* aad) {
    if (!key || !iv || !plaintext) return SPL_STRDUP("", "str");
    return rt_aes_gcm_encrypt_with_len(key, (int64_t)strlen(key),
                                        iv, (int64_t)strlen(iv),
                                        plaintext, (int64_t)strlen(plaintext),
                                        aad, aad ? (int64_t)strlen(aad) : 0,
                                        NULL);
}

/* ---- rt_aes_gcm_decrypt_with_len: binary-safe (from-scratch fallback) ---- */
const char* rt_aes_gcm_decrypt_with_len(const char* key, int64_t key_len,
                                         const char* iv, int64_t iv_len,
                                         const char* ciphertext, int64_t ct_len,
                                         const char* aad, int64_t aad_len,
                                         int64_t* out_len) {
    if (out_len) *out_len = 0;
    if (!key || !iv || !ciphertext || key_len < 16 || iv_len < 12 || ct_len < 16)
        return SPL_STRDUP("", "str");

    int64_t actual_ct_len = ct_len - 16;
    const uint8_t* tag = (const uint8_t*)ciphertext + actual_ct_len;

    uint8_t* pt_buf = (uint8_t*)SPL_MALLOC((size_t)actual_ct_len + 1, "str");

    if (aes_gcm_decrypt_impl((const uint8_t*)key, 16,
                              (const uint8_t*)iv, (size_t)iv_len,
                              (const uint8_t*)ciphertext, (size_t)actual_ct_len,
                              aad ? (const uint8_t*)aad : (const uint8_t*)"",
                              aad ? (size_t)aad_len : 0,
                              tag, pt_buf) != 0) {
        SPL_FREE(pt_buf);
        return SPL_STRDUP("", "str");
    }

    pt_buf[actual_ct_len] = '\0';
    if (out_len) *out_len = actual_ct_len;
    return (const char*)pt_buf;
}

const char* rt_aes_gcm_decrypt(const char* key, const char* iv,
                                const char* ciphertext, const char* aad) {
    if (!key || !iv || !ciphertext) return SPL_STRDUP("", "str");
    return rt_aes_gcm_decrypt_with_len(key, (int64_t)strlen(key),
                                        iv, (int64_t)strlen(iv),
                                        ciphertext, (int64_t)strlen(ciphertext),
                                        aad, aad ? (int64_t)strlen(aad) : 0,
                                        NULL);
}

#endif /* SPL_HAVE_OPENSSL */

/* ============================================================================
 * Hex-domain AES-GCM wrappers (binary-safe, NUL-transparent)
 *
 * These accept and return hex-encoded strings (0-9a-f), which never contain
 * NUL bytes.  Internally they decode to binary, call the _with_len variants,
 * and re-encode the result to hex.  Simple code can use these via:
 *   extern fn rt_aes_gcm_encrypt_hex(...) -> text
 *   extern fn rt_aes_gcm_decrypt_hex(...) -> text
 * ========================================================================= */

static int hex_char_val(char c) {
    if (c >= '0' && c <= '9') return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return -1;
}

/* Decode hex string to binary buffer.  Caller must free().  Sets *out_len. */
static uint8_t* hex_decode(const char* hex, int64_t* out_len) {
    if (!hex) { *out_len = 0; return NULL; }
    size_t slen = strlen(hex);
    if (slen % 2 != 0) { *out_len = 0; return NULL; }
    size_t blen = slen / 2;
    uint8_t* buf = (uint8_t*)malloc(blen);
    if (!buf) { *out_len = 0; return NULL; }
    for (size_t i = 0; i < blen; i++) {
        int hi = hex_char_val(hex[2*i]);
        int lo = hex_char_val(hex[2*i+1]);
        if (hi < 0 || lo < 0) { free(buf); *out_len = 0; return NULL; }
        buf[i] = (uint8_t)((hi << 4) | lo);
    }
    *out_len = (int64_t)blen;
    return buf;
}

/* Encode binary buffer to hex string.  Caller must free(). */
static char* hex_encode(const uint8_t* data, int64_t len) {
    if (!data || len <= 0) {
        char* empty = (char*)malloc(1);
        if (empty) empty[0] = '\0';
        return empty;
    }
    char* hex = (char*)malloc((size_t)(len * 2 + 1));
    if (!hex) return NULL;
    static const char digits[] = "0123456789abcdef";
    for (int64_t i = 0; i < len; i++) {
        hex[2*i]     = digits[(data[i] >> 4) & 0x0F];
        hex[2*i + 1] = digits[data[i] & 0x0F];
    }
    hex[len * 2] = '\0';
    return hex;
}

const char* rt_aes_gcm_encrypt_hex(const char* key_hex, const char* iv_hex,
                                    const char* plaintext_hex, const char* aad_hex) {
    int64_t key_len, iv_len, pt_len, aad_len;
    uint8_t* key = hex_decode(key_hex, &key_len);
    uint8_t* iv  = hex_decode(iv_hex, &iv_len);
    uint8_t* pt  = hex_decode(plaintext_hex, &pt_len);
    uint8_t* aad = hex_decode(aad_hex, &aad_len);

    int64_t ct_len = 0;
    const char* ct_raw = rt_aes_gcm_encrypt_with_len(
        (const char*)key, key_len,
        (const char*)iv, iv_len,
        (const char*)pt, pt_len,
        (const char*)aad, aad_len,
        &ct_len);

    free(key); free(iv); free(pt); free(aad);

    if (!ct_raw) return NULL;
    char* result = hex_encode((const uint8_t*)ct_raw, ct_len);
    return result;
}

const char* rt_aes_gcm_decrypt_hex(const char* key_hex, const char* iv_hex,
                                    const char* ciphertext_hex, const char* aad_hex) {
    int64_t key_len, iv_len, ct_len, aad_len;
    uint8_t* key = hex_decode(key_hex, &key_len);
    uint8_t* iv  = hex_decode(iv_hex, &iv_len);
    uint8_t* ct  = hex_decode(ciphertext_hex, &ct_len);
    uint8_t* aad = hex_decode(aad_hex, &aad_len);

    int64_t pt_len = 0;
    const char* pt_raw = rt_aes_gcm_decrypt_with_len(
        (const char*)key, key_len,
        (const char*)iv, iv_len,
        (const char*)ct, ct_len,
        (const char*)aad, aad_len,
        &pt_len);

    free(key); free(iv); free(ct); free(aad);

    if (!pt_raw) return NULL;
    char* result = hex_encode((const uint8_t*)pt_raw, pt_len);
    return result;
}

/* Convert wire text (may contain NUL) to hex string, given explicit length. */
const char* rt_wire_to_hex(const char* wire, int64_t wire_len) {
    if (!wire || wire_len <= 0) {
        char* empty = (char*)malloc(1);
        if (empty) empty[0] = '\0';
        return empty;
    }
    return hex_encode((const uint8_t*)wire, wire_len);
}

/* Convert hex string back to wire text (binary, may contain NUL).
 * Returns a NUL-terminated buffer but the logical length is strlen(hex)/2.
 * The caller can pass the result to _with_len functions using that length. */
const char* rt_hex_to_wire(const char* hex_str) {
    int64_t len;
    uint8_t* buf = hex_decode(hex_str, &len);
    if (!buf) {
        char* empty = (char*)malloc(1);
        if (empty) empty[0] = '\0';
        return empty;
    }
    /* Ensure NUL termination for C string safety */
    uint8_t* result = (uint8_t*)realloc(buf, (size_t)(len + 1));
    if (!result) { free(buf); return NULL; }
    result[len] = 0;
    return (const char*)result;
}

/* ---- Byte array handle for [u8] FFI ----
 * The [u8] type in Simple FFI maps to an opaque int64_t handle.
 * Internally: pointer to { uint8_t* data; int64_t len; int64_t cap; } */
typedef struct {
    uint8_t* data;
    int64_t  len;
    int64_t  cap;
} rt_byte_buf;

static rt_byte_buf* rt_byte_buf_from_handle(int64_t handle) {
    return (rt_byte_buf*)(uintptr_t)handle;
}

/* rt_text_to_bytes: create byte array handle from text string */
int64_t rt_text_to_bytes(const char* text) {
    if (!text) text = "";
    size_t len = strlen(text);
    rt_byte_buf* bb = (rt_byte_buf*)SPL_MALLOC(sizeof(rt_byte_buf), "bytes");
    bb->len = (int64_t)len;
    bb->cap = (int64_t)len;
    bb->data = (uint8_t*)SPL_MALLOC(len > 0 ? len : 1, "bytes");
    if (len > 0) memcpy(bb->data, text, len);
    return (int64_t)(uintptr_t)bb;
}

/* rt_bytes_to_text: convert byte array handle back to text (null-terminated) */
const char* rt_bytes_to_text(int64_t handle) {
    if (!handle) return SPL_STRDUP("", "str");
    rt_byte_buf* bb = rt_byte_buf_from_handle(handle);
    if (!bb->data || bb->len <= 0) return SPL_STRDUP("", "str");
    char* result = (char*)SPL_MALLOC((size_t)bb->len + 1, "str");
    memcpy(result, bb->data, (size_t)bb->len);
    result[bb->len] = '\0';
    return result;
}
