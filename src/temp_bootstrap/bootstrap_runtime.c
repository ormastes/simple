/*
 * Bootstrap Runtime for Simple-to-C compiled binaries.
 *
 * All values are int64_t. Heap objects (strings, arrays, dicts, objects,
 * closures, tuples, enums) are malloc'd and their pointer stored as int64_t.
 * Value 0 = nil.
 *
 * This runtime is intentionally simple and correct rather than fast.
 * It provides enough functionality to run the Simple compiler compiled to C.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>
#include <errno.h>
#include <ctype.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <unistd.h>
#include <dirent.h>
#include <pthread.h>
#include <fcntl.h>
#include <libgen.h>
#include <sys/wait.h>

/* ================================================================
 * Heap Object Headers
 * ================================================================ */

/* Object types stored in header */
#define OBJ_STRING  1
#define OBJ_ARRAY   2
#define OBJ_DICT    3
#define OBJ_OBJECT  4
#define OBJ_CLOSURE 5
#define OBJ_TUPLE   6
#define OBJ_ENUM    7

typedef struct {
    int32_t obj_type;
    int32_t extra; /* depends on obj_type */
} HeapHeader;

/* String: header + length + data (null-terminated) */
typedef struct {
    HeapHeader hdr;  /* obj_type = OBJ_STRING */
    int64_t len;
    char data[];     /* flexible array member */
} SplString;

/* Array: header + len + cap + elements */
typedef struct {
    HeapHeader hdr;  /* obj_type = OBJ_ARRAY */
    int64_t len;
    int64_t cap;
    int64_t *items;
} SplArray;

/* Dict entry */
typedef struct {
    int64_t key;     /* string value (int64_t) */
    int64_t value;
    int used;        /* 0=empty, 1=occupied, -1=tombstone */
} DictEntry;

/* Dict: open-addressing hash table */
typedef struct {
    HeapHeader hdr;  /* obj_type = OBJ_DICT */
    int64_t len;
    int64_t cap;
    DictEntry *entries;
} SplDict;

/* Object: type_id + field_count + fields[] */
typedef struct {
    HeapHeader hdr;  /* obj_type = OBJ_OBJECT, extra = type_id */
    int64_t field_count;
    int64_t fields[];
} SplObject;

/* Closure: func_ptr + capture_count + captures[] */
typedef struct {
    HeapHeader hdr;  /* obj_type = OBJ_CLOSURE */
    int64_t func_ptr;
    int64_t capture_count;
    int64_t captures[];
} SplClosure;

/* Tuple: len + elements[] */
typedef struct {
    HeapHeader hdr;  /* obj_type = OBJ_TUPLE */
    int64_t len;
    int64_t items[];
} SplTuple;

/* Enum: discriminant + payload */
typedef struct {
    HeapHeader hdr;  /* obj_type = OBJ_ENUM */
    int64_t discriminant;
    int64_t payload;
} SplEnum;

/* ================================================================
 * Debug service state (bootstrap shim)
 * ================================================================ */

/* The Simple sources define ds_set_active() and other debug-service helpers
 * in lib.nogc_sync_mut.io.debug_state. The bootstrap runtime does not pull
 * that module in, so we provide a minimal C implementation to satisfy
 * references during Stage2 linking. The compiler only checks for existence;
 * a tiny bool flag is enough for now. */

static int64_t g_ds_is_active = 0;

int64_t ds_set_active(int64_t active) {
    g_ds_is_active = active ? 1 : 0;
    return 0;  /* Simple void returns are encoded as int64_t 0 */
}

/* Fault/limit controls (bootstrap shim)
 * The Simple sources declare these as externs; provide harmless defaults so
 * the native bootstrap links without relying on platform-specific watchdogs.
 * Marked weak so they can be overridden by a real runtime if present.
 */
/* Expose fault controls with C names that match extern declarations.  We
 * provide both `int64_t`-returning versions (used by Simple) and `void`
 * aliases (in case headers declared them differently). Weak linkage lets a
 * real runtime override these if linked later. */

__attribute__((weak)) int64_t rt_fault_set_stack_overflow_detection(int64_t enabled) {
    (void)enabled;
    return 1;
}
__attribute__((weak)) void rt_fault_set_stack_overflow_detection_void(int64_t enabled) {
    (void)enabled;
}

__attribute__((weak)) int64_t rt_fault_set_max_recursion_depth(int64_t depth) {
    (void)depth;
    return 1;
}
__attribute__((weak)) void rt_fault_set_max_recursion_depth_void(int64_t depth) {
    (void)depth;
}

__attribute__((weak)) int64_t rt_fault_set_timeout(int64_t timeout_ms) {
    (void)timeout_ms;
    return 1;
}
__attribute__((weak)) void rt_fault_set_timeout_void(int64_t timeout_ms) {
    (void)timeout_ms;
}

__attribute__((weak)) int64_t rt_fault_set_execution_limit(int64_t limit) {
    (void)limit;
    return 1;
}
__attribute__((weak)) void rt_fault_set_execution_limit_void(int64_t limit) {
    (void)limit;
}

/* ================================================================
 * Type checking helpers
 * ================================================================ */

static inline int is_heap_obj(int64_t v) {
    return v != 0 && (uint64_t)v >= 0x10000ULL;
}

static inline HeapHeader *get_header(int64_t v) {
    return (HeapHeader *)(intptr_t)v;
}

static inline int obj_type(int64_t v) {
    if (!is_heap_obj(v)) return 0;
    return get_header(v)->obj_type;
}

static inline SplString *as_string(int64_t v) {
    return (SplString *)(intptr_t)v;
}

static inline SplArray *as_array(int64_t v) {
    return (SplArray *)(intptr_t)v;
}

static inline SplDict *as_dict(int64_t v) {
    return (SplDict *)(intptr_t)v;
}

static inline SplObject *as_object(int64_t v) {
    return (SplObject *)(intptr_t)v;
}

static inline SplClosure *as_closure(int64_t v) {
    return (SplClosure *)(intptr_t)v;
}

static inline SplTuple *as_tuple(int64_t v) {
    return (SplTuple *)(intptr_t)v;
}

static inline SplEnum *as_enum(int64_t v) {
    return (SplEnum *)(intptr_t)v;
}

/* ================================================================
 * String Operations
 * ================================================================ */

int64_t rt_string_new(int64_t ptr, int64_t len) {
    SplString *s = (SplString *)malloc(sizeof(SplString) + len + 1);
    s->hdr.obj_type = OBJ_STRING;
    s->hdr.extra = 0;
    s->len = len;
    if (ptr && len > 0) {
        memcpy(s->data, (const char *)(intptr_t)ptr, len);
    }
    s->data[len] = '\0';
    return (int64_t)(intptr_t)s;
}

int64_t rt_string_concat(int64_t a, int64_t b) {
    const char *sa = "", *sb = "";
    int64_t la = 0, lb = 0;
    if (is_heap_obj(a) && obj_type(a) == OBJ_STRING) {
        sa = as_string(a)->data;
        la = as_string(a)->len;
    }
    if (is_heap_obj(b) && obj_type(b) == OBJ_STRING) {
        sb = as_string(b)->data;
        lb = as_string(b)->len;
    }
    int64_t total = la + lb;
    SplString *s = (SplString *)malloc(sizeof(SplString) + total + 1);
    s->hdr.obj_type = OBJ_STRING;
    s->hdr.extra = 0;
    s->len = total;
    if (la > 0) memcpy(s->data, sa, la);
    if (lb > 0) memcpy(s->data + la, sb, lb);
    s->data[total] = '\0';
    return (int64_t)(intptr_t)s;
}

int64_t rt_string_eq(int64_t a, int64_t b) {
    if (a == b) return 1;
    if (!is_heap_obj(a) || !is_heap_obj(b)) return 0;
    if (obj_type(a) != OBJ_STRING || obj_type(b) != OBJ_STRING) return 0;
    SplString *sa = as_string(a);
    SplString *sb = as_string(b);
    if (sa->len != sb->len) return 0;
    return memcmp(sa->data, sb->data, sa->len) == 0 ? 1 : 0;
}

/* Get C string from a runtime string value. Returns "" for non-strings. */
static const char *str_cstr(int64_t v) {
    if (is_heap_obj(v) && obj_type(v) == OBJ_STRING)
        return as_string(v)->data;
    return "";
}

static int64_t str_len(int64_t v) {
    if (is_heap_obj(v) && obj_type(v) == OBJ_STRING)
        return as_string(v)->len;
    return 0;
}

/* Create a runtime string from a C string */
static int64_t str_from_cstr(const char *s) {
    if (!s) return 0;
    int64_t len = (int64_t)strlen(s);
    return rt_string_new((int64_t)(intptr_t)s, len);
}

/* ================================================================
 * Array Operations
 * ================================================================ */

int64_t rt_array_new(int64_t hint_cap) {
    SplArray *a = (SplArray *)malloc(sizeof(SplArray));
    a->hdr.obj_type = OBJ_ARRAY;
    a->hdr.extra = 0;
    a->len = 0;
    a->cap = hint_cap > 4 ? hint_cap : 4;
    a->items = (int64_t *)calloc(a->cap, sizeof(int64_t));
    return (int64_t)(intptr_t)a;
}

int64_t rt_array_push(int64_t arr_v, int64_t val) {
    if (!is_heap_obj(arr_v) || obj_type(arr_v) != OBJ_ARRAY) return 0;
    SplArray *a = as_array(arr_v);
    if (a->len >= a->cap) {
        a->cap = a->cap * 2;
        a->items = (int64_t *)realloc(a->items, a->cap * sizeof(int64_t));
    }
    a->items[a->len++] = val;
    return arr_v;
}

int64_t rt_array_get(int64_t arr_v, int64_t idx) {
    if (!is_heap_obj(arr_v) || obj_type(arr_v) != OBJ_ARRAY) return 0;
    SplArray *a = as_array(arr_v);
    if (idx < 0 || idx >= a->len) return 0;
    return a->items[idx];
}

int64_t rt_array_set(int64_t arr_v, int64_t idx, int64_t val) {
    if (!is_heap_obj(arr_v) || obj_type(arr_v) != OBJ_ARRAY) return 0;
    SplArray *a = as_array(arr_v);
    if (idx < 0 || idx >= a->len) return 0;
    a->items[idx] = val;
    return arr_v;
}

int64_t rt_array_pop(int64_t arr_v) {
    if (!is_heap_obj(arr_v) || obj_type(arr_v) != OBJ_ARRAY) return 0;
    SplArray *a = as_array(arr_v);
    if (a->len == 0) return 0;
    return a->items[--a->len];
}

int64_t rt_array_clear(int64_t arr_v) {
    if (!is_heap_obj(arr_v) || obj_type(arr_v) != OBJ_ARRAY) return 0;
    as_array(arr_v)->len = 0;
    return arr_v;
}

int64_t rt_array_len(int64_t arr_v) {
    if (!is_heap_obj(arr_v) || obj_type(arr_v) != OBJ_ARRAY) return 0;
    return as_array(arr_v)->len;
}

/* ================================================================
 * Tuple Operations
 * ================================================================ */

int64_t rt_tuple_new(int64_t len) {
    SplTuple *t = (SplTuple *)malloc(sizeof(SplTuple) + len * sizeof(int64_t));
    t->hdr.obj_type = OBJ_TUPLE;
    t->hdr.extra = 0;
    t->len = len;
    memset(t->items, 0, len * sizeof(int64_t));
    return (int64_t)(intptr_t)t;
}

int64_t rt_tuple_set(int64_t tup_v, int64_t idx, int64_t val) {
    if (!is_heap_obj(tup_v) || obj_type(tup_v) != OBJ_TUPLE) return 0;
    SplTuple *t = as_tuple(tup_v);
    if (idx >= 0 && idx < t->len) t->items[idx] = val;
    return tup_v;
}

int64_t rt_tuple_get(int64_t tup_v, int64_t idx) {
    if (!is_heap_obj(tup_v) || obj_type(tup_v) != OBJ_TUPLE) return 0;
    SplTuple *t = as_tuple(tup_v);
    if (idx < 0 || idx >= t->len) return 0;
    return t->items[idx];
}

int64_t rt_tuple_len(int64_t v) {
    if (!is_heap_obj(v)) return 0;
    int t = obj_type(v);
    if (t == OBJ_TUPLE) return as_tuple(v)->len;
    if (t == OBJ_ARRAY) return as_array(v)->len;
    if (t == OBJ_STRING) return as_string(v)->len;
    return 0;
}

/* ================================================================
 * Dict Operations
 * ================================================================ */

static uint64_t hash_string(int64_t key) {
    const char *s = str_cstr(key);
    uint64_t h = 14695981039346656037ULL;
    while (*s) {
        h ^= (uint8_t)*s++;
        h *= 1099511628211ULL;
    }
    return h;
}

int64_t rt_dict_new(int64_t hint_cap) {
    SplDict *d = (SplDict *)malloc(sizeof(SplDict));
    d->hdr.obj_type = OBJ_DICT;
    d->hdr.extra = 0;
    d->len = 0;
    d->cap = hint_cap > 8 ? hint_cap : 8;
    /* Round up to power of 2 */
    int64_t c = 8;
    while (c < d->cap) c *= 2;
    d->cap = c;
    d->entries = (DictEntry *)calloc(d->cap, sizeof(DictEntry));
    return (int64_t)(intptr_t)d;
}

static void dict_resize(SplDict *d) {
    int64_t old_cap = d->cap;
    DictEntry *old = d->entries;
    d->cap = old_cap * 2;
    d->entries = (DictEntry *)calloc(d->cap, sizeof(DictEntry));
    d->len = 0;
    for (int64_t i = 0; i < old_cap; i++) {
        if (old[i].used == 1) {
            /* Re-insert */
            uint64_t h = hash_string(old[i].key);
            int64_t idx = (int64_t)(h & (uint64_t)(d->cap - 1));
            while (d->entries[idx].used == 1) {
                idx = (idx + 1) & (d->cap - 1);
            }
            d->entries[idx].key = old[i].key;
            d->entries[idx].value = old[i].value;
            d->entries[idx].used = 1;
            d->len++;
        }
    }
    free(old);
}

static int64_t dict_ensure_string_key(int64_t key) {
    if (!is_heap_obj(key) || obj_type(key) != OBJ_STRING) {
        char buf[32];
        snprintf(buf, sizeof(buf), "%ld", (long)key);
        return rt_string_new((int64_t)(intptr_t)buf, strlen(buf));
    }
    return key;
}

int64_t rt_dict_set(int64_t dict_v, int64_t key, int64_t val) {
    if (!is_heap_obj(dict_v) || obj_type(dict_v) != OBJ_DICT) return 0;
    int64_t orig_key = key;
    key = dict_ensure_string_key(key);
    if (key != orig_key) {
        fprintf(stderr, "[DICT_SET] key was converted! orig=%ld (heap=%d, otype=%d) → new=%ld\n",
                (long)orig_key, is_heap_obj(orig_key), is_heap_obj(orig_key) ? obj_type(orig_key) : -1, (long)key);
    }
    SplDict *d = as_dict(dict_v);
    if (d->len * 2 >= d->cap) dict_resize(d);
    uint64_t h = hash_string(key);
    int64_t idx = (int64_t)(h & (uint64_t)(d->cap - 1));
    while (d->entries[idx].used == 1) {
        if (rt_string_eq(d->entries[idx].key, key)) {
            d->entries[idx].value = val;
            return dict_v;
        }
        idx = (idx + 1) & (d->cap - 1);
    }
    d->entries[idx].key = key;
    d->entries[idx].value = val;
    d->entries[idx].used = 1;
    d->len++;
    return dict_v;
}

int64_t rt_dict_get(int64_t dict_v, int64_t key) {
    if (!is_heap_obj(dict_v) || obj_type(dict_v) != OBJ_DICT) return 0;
    key = dict_ensure_string_key(key);
    SplDict *d = as_dict(dict_v);
    if (d->len == 0) return 0;
    uint64_t h = hash_string(key);
    int64_t idx = (int64_t)(h & (uint64_t)(d->cap - 1));
    int64_t start = idx;
    do {
        if (d->entries[idx].used == 0) return 0;
        if (d->entries[idx].used == 1 && rt_string_eq(d->entries[idx].key, key))
            return d->entries[idx].value;
        idx = (idx + 1) & (d->cap - 1);
    } while (idx != start);
    return 0;
}

int64_t rt_dict_len(int64_t dict_v) {
    if (!is_heap_obj(dict_v) || obj_type(dict_v) != OBJ_DICT) return 0;
    return as_dict(dict_v)->len;
}

int64_t rt_dict_clear(int64_t dict_v) {
    if (!is_heap_obj(dict_v) || obj_type(dict_v) != OBJ_DICT) return 0;
    SplDict *d = as_dict(dict_v);
    memset(d->entries, 0, d->cap * sizeof(DictEntry));
    d->len = 0;
    return dict_v;
}

int64_t rt_dict_keys(int64_t dict_v) {
    if (!is_heap_obj(dict_v) || obj_type(dict_v) != OBJ_DICT) return rt_array_new(0);
    SplDict *d = as_dict(dict_v);
    int64_t arr = rt_array_new(d->len);
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].used == 1) rt_array_push(arr, d->entries[i].key);
    }
    return arr;
}

int64_t rt_dict_values(int64_t dict_v) {
    if (!is_heap_obj(dict_v) || obj_type(dict_v) != OBJ_DICT) return rt_array_new(0);
    SplDict *d = as_dict(dict_v);
    int64_t arr = rt_array_new(d->len);
    for (int64_t i = 0; i < d->cap; i++) {
        if (d->entries[i].used == 1) rt_array_push(arr, d->entries[i].value);
    }
    return arr;
}

/* ================================================================
 * Object Operations
 * ================================================================ */

static int __rt_obj_debug_count = 0;
int64_t rt_object_new(int64_t type_id, int64_t field_count) {
    int64_t actual_field_count = field_count;
    SplObject *o = (SplObject *)malloc(sizeof(SplObject) + actual_field_count * sizeof(int64_t));
    o->hdr.obj_type = OBJ_OBJECT;
    o->hdr.extra = (int32_t)type_id;
    o->field_count = actual_field_count;
    memset(o->fields, 0, actual_field_count * sizeof(int64_t));
    return (int64_t)(intptr_t)o;
}

/* Debug helper to inspect a value */
void __debug_inspect(const char *label, int64_t val) {
    if (val == 0) {
        fprintf(stderr, "[DEBUG] %s = nil (0)\n", label);
    } else if (!is_heap_obj(val)) {
        fprintf(stderr, "[DEBUG] %s = integer %ld\n", label, (long)val);
    } else {
        int t = obj_type(val);
        const char *type_names[] = {"?", "STRING", "ARRAY", "DICT", "OBJECT", "CLOSURE", "TUPLE", "ENUM"};
        const char *tname = (t >= 0 && t <= 7) ? type_names[t] : "UNKNOWN";
        if (t == OBJ_OBJECT) {
            SplObject *o = as_object(val);
            fprintf(stderr, "[DEBUG] %s = OBJECT(type_id=%d, fields=%ld) @ %p\n",
                    label, o->hdr.extra, (long)o->field_count, (void*)(intptr_t)val);
        } else if (t == OBJ_ARRAY) {
            SplArray *a = as_array(val);
            fprintf(stderr, "[DEBUG] %s = ARRAY(len=%ld, cap=%ld) @ %p\n",
                    label, (long)a->len, (long)a->cap, (void*)(intptr_t)val);
        } else if (t == OBJ_DICT) {
            SplDict *d = as_dict(val);
            fprintf(stderr, "[DEBUG] %s = DICT(len=%ld, cap=%ld) @ %p\n",
                    label, (long)d->len, (long)d->cap, (void*)(intptr_t)val);
        } else if (t == OBJ_STRING) {
            SplString *s = as_string(val);
            fprintf(stderr, "[DEBUG] %s = STRING(len=%ld, \"%.40s\") @ %p\n",
                    label, (long)s->len, s->data, (void*)(intptr_t)val);
        } else {
            fprintf(stderr, "[DEBUG] %s = %s @ %p\n", label, tname, (void*)(intptr_t)val);
        }
    }
}

int64_t rt_object_field_get(int64_t obj_v, int64_t field_idx) {
    if (!is_heap_obj(obj_v) || obj_type(obj_v) != OBJ_OBJECT) return 0;
    SplObject *o = as_object(obj_v);
    // Generated C uses byte offsets (0, 8, 16, 24...) not field indices (0, 1, 2, 3...)
    int64_t idx = field_idx / (int64_t)sizeof(int64_t);
    if (idx < 0 || idx >= o->field_count) return 0;
    return o->fields[idx];
}

int64_t rt_object_field_set(int64_t obj_v, int64_t field_idx, int64_t val) {
    if (!is_heap_obj(obj_v) || obj_type(obj_v) != OBJ_OBJECT) return 0;
    SplObject *o = as_object(obj_v);
    // Generated C uses byte offsets (0, 8, 16, 24...) not field indices (0, 1, 2, 3...)
    int64_t idx = field_idx / (int64_t)sizeof(int64_t);
    if (idx < 0 || idx >= o->field_count) return 0;
    o->fields[idx] = val;
    return obj_v;
}

/* ================================================================
 * Closure Operations
 * ================================================================ */

int64_t rt_closure_new(int64_t func_ptr, int64_t capture_count) {
    SplClosure *c = (SplClosure *)malloc(sizeof(SplClosure) + capture_count * sizeof(int64_t));
    c->hdr.obj_type = OBJ_CLOSURE;
    c->hdr.extra = 0;
    c->func_ptr = func_ptr;
    c->capture_count = capture_count;
    memset(c->captures, 0, capture_count * sizeof(int64_t));
    return (int64_t)(intptr_t)c;
}

int64_t rt_closure_set_capture(int64_t clo_v, int64_t idx, int64_t val) {
    if (!is_heap_obj(clo_v) || obj_type(clo_v) != OBJ_CLOSURE) return 0;
    SplClosure *c = as_closure(clo_v);
    if (idx >= 0 && idx < c->capture_count) c->captures[idx] = val;
    return clo_v;
}

int64_t rt_closure_get_capture(int64_t clo_v, int64_t idx) {
    if (!is_heap_obj(clo_v) || obj_type(clo_v) != OBJ_CLOSURE) return 0;
    SplClosure *c = as_closure(clo_v);
    if (idx < 0 || idx >= c->capture_count) return 0;
    return c->captures[idx];
}

int64_t rt_closure_func_ptr(int64_t clo_v) {
    if (!is_heap_obj(clo_v) || obj_type(clo_v) != OBJ_CLOSURE) return 0;
    return as_closure(clo_v)->func_ptr;
}

/* ================================================================
 * Enum Operations
 * ================================================================ */

int64_t rt_enum_new(int64_t type_id, int64_t discriminant, int64_t payload) {
    (void)type_id;
    SplEnum *e = (SplEnum *)malloc(sizeof(SplEnum));
    e->hdr.obj_type = OBJ_ENUM;
    e->hdr.extra = (int32_t)type_id;
    e->discriminant = discriminant;
    e->payload = payload;
    return (int64_t)(intptr_t)e;
}

int64_t rt_enum_discriminant(int64_t v) {
    if (!is_heap_obj(v)) return v; /* plain int used as discriminant */
    if (obj_type(v) == OBJ_ENUM) return as_enum(v)->discriminant;
    if (obj_type(v) == OBJ_TUPLE && as_tuple(v)->len >= 1)
        return as_tuple(v)->items[0]; /* (tag, payload) convention */
    return 0;
}

int64_t rt_enum_payload(int64_t v) {
    if (!is_heap_obj(v)) return 0;
    if (obj_type(v) == OBJ_ENUM) return as_enum(v)->payload;
    if (obj_type(v) == OBJ_TUPLE && as_tuple(v)->len >= 2)
        return as_tuple(v)->items[1]; /* (tag, payload) convention */
    return v;
}

/* ================================================================
 * Value Constructors
 * ================================================================ */

int64_t rt_value_int(int64_t v) { return v; }
int64_t rt_value_float(double v) { union { double d; int64_t i; } u; u.d = v; return u.i; }
int64_t rt_value_bool(int64_t v) { return v ? 1 : 0; }
int64_t rt_value_nil(void) { return 0; }
int64_t rt_value_as_int(int64_t v) { return v; }

/* ================================================================
 * Index Operations (generic)
 * ================================================================ */

int64_t rt_index_get(int64_t collection, int64_t idx) {
    if (!is_heap_obj(collection)) return 0;
    int t = obj_type(collection);
    if (t == OBJ_ARRAY) return rt_array_get(collection, idx);
    if (t == OBJ_TUPLE) return rt_tuple_get(collection, idx);
    if (t == OBJ_DICT) {
        /* If idx is a heap string, do key lookup directly */
        if (is_heap_obj(idx)) {
            return rt_dict_get(collection, idx);
        }
        /* Integer index: try key lookup first (for Dict<i64, V> patterns),
           then fall back to positional access (for `for k,v in dict:` iteration) */
        int64_t key_result = rt_dict_get(collection, idx);
        if (key_result != 0) {
            return key_result;
        }
        /* Key not found — fall back to positional indexing, return [key, value] pair */
        SplDict *d = as_dict(collection);
        int64_t pos = 0;
        for (int64_t i = 0; i < d->cap; i++) {
            if (d->entries[i].used == 1) {
                if (pos == idx) {
                    int64_t pair = rt_array_new(2);
                    rt_array_push(pair, d->entries[i].key);
                    rt_array_push(pair, d->entries[i].value);
                    return pair;
                }
                pos++;
            }
        }
        return 0;
    }
    if (t == OBJ_STRING) {
        SplString *s = as_string(collection);
        if (idx < 0 || idx >= s->len) return 0;
        return rt_string_new((int64_t)(intptr_t)(s->data + idx), 1);
    }
    return 0;
}

int64_t rt_index_set(int64_t collection, int64_t idx, int64_t val) {
    if (!is_heap_obj(collection)) return 0;
    int t = obj_type(collection);
    if (t == OBJ_ARRAY) return rt_array_set(collection, idx, val);
    if (t == OBJ_DICT) return rt_dict_set(collection, idx, val);
    return 0;
}

int64_t rt_contains(int64_t collection, int64_t item) {
    if (!is_heap_obj(collection)) return 0;
    int t = obj_type(collection);
    if (t == OBJ_ARRAY) {
        SplArray *a = as_array(collection);
        for (int64_t i = 0; i < a->len; i++) {
            if (a->items[i] == item || rt_string_eq(a->items[i], item)) return 1;
        }
        return 0;
    }
    if (t == OBJ_DICT) {
        return rt_dict_get(collection, item) != 0 ? 1 : 0;
    }
    if (t == OBJ_STRING) {
        const char *haystack = str_cstr(collection);
        const char *needle = str_cstr(item);
        return strstr(haystack, needle) != NULL ? 1 : 0;
    }
    return 0;
}

int64_t rt_slice(int64_t collection, int64_t start, int64_t end, int64_t step) {
    (void)step;
    if (!is_heap_obj(collection)) return 0;
    int t = obj_type(collection);
    if (t == OBJ_ARRAY) {
        SplArray *a = as_array(collection);
        if (start < 0) start = a->len + start;
        if (end < 0) end = a->len + end;
        if (start < 0) start = 0;
        if (end > a->len) end = a->len;
        int64_t result = rt_array_new(end - start);
        for (int64_t i = start; i < end; i++) {
            rt_array_push(result, a->items[i]);
        }
        return result;
    }
    if (t == OBJ_STRING) {
        SplString *s = as_string(collection);
        if (start < 0) start = s->len + start;
        if (end < 0) end = s->len + end;
        if (start < 0) start = 0;
        if (end > s->len) end = s->len;
        if (start >= end) return rt_string_new(0, 0);
        return rt_string_new((int64_t)(intptr_t)(s->data + start), end - start);
    }
    return 0;
}

/* ================================================================
 * Print Operations
 * ================================================================ */

static void print_value(int64_t v, FILE *out) {
    if (v == 0) {
        fprintf(out, "nil");
    } else if (is_heap_obj(v) && obj_type(v) == OBJ_STRING) {
        fprintf(out, "%s", as_string(v)->data);
    } else {
        fprintf(out, "%ld", (long)v);
    }
}

void rt_print_str(int64_t ptr, int64_t len) {
    if (is_heap_obj(ptr) && obj_type(ptr) == OBJ_STRING) {
        fwrite(as_string(ptr)->data, 1, as_string(ptr)->len, stdout);
    } else if (ptr != 0) {
        fwrite((const char *)(intptr_t)ptr, 1, len, stdout);
    }
}

void rt_println_str(int64_t ptr, int64_t len) {
    rt_print_str(ptr, len);
    putchar('\n');
}

void rt_eprint_str(int64_t ptr, int64_t len) {
    if (is_heap_obj(ptr) && obj_type(ptr) == OBJ_STRING) {
        fwrite(as_string(ptr)->data, 1, as_string(ptr)->len, stderr);
    } else if (ptr != 0) {
        fwrite((const char *)(intptr_t)ptr, 1, len, stderr);
    }
}

void rt_eprintln_str(int64_t ptr, int64_t len) {
    rt_eprint_str(ptr, len);
    fputc('\n', stderr);
}

void rt_print_value(int64_t v) { print_value(v, stdout); }
void rt_println_value(int64_t v) { print_value(v, stdout); putchar('\n'); }
void rt_eprint_value(int64_t v) { print_value(v, stderr); }
void rt_eprintln_value(int64_t v) { print_value(v, stderr); fputc('\n', stderr); }

void rt_capture_stdout_start(void) { /* noop in bootstrap */ }
void rt_capture_stderr_start(void) { /* noop in bootstrap */ }

/* ================================================================
 * File I/O
 * ================================================================ */

__attribute__((weak)) int64_t rt_file_read_text(int64_t path_v) {
    const char *path = str_cstr(path_v);
    FILE *f = fopen(path, "rb");
    if (!f) return 0;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    char *buf = (char *)malloc(sz + 1);
    fread(buf, 1, sz, f);
    buf[sz] = '\0';
    fclose(f);
    int64_t result = rt_string_new((int64_t)(intptr_t)buf, sz);
    free(buf);
    return result;
}

__attribute__((weak)) int64_t rt_file_write(int64_t path_v, int64_t content_v) {
    const char *path = str_cstr(path_v);
    const char *content = str_cstr(content_v);
    int64_t len = str_len(content_v);
    FILE *f = fopen(path, "wb");
    if (!f) return 0;
    fwrite(content, 1, len, f);
    fclose(f);
    return 1;
}

int64_t rt_file_write_text(int64_t path_v, int64_t content_v) {
    return rt_file_write(path_v, content_v);
}

__attribute__((weak)) int64_t rt_file_exists(int64_t path_v) {
    const char *path = str_cstr(path_v);
    return access(path, F_OK) == 0 ? 1 : 0;
}

int64_t rt_dir_exists(int64_t path_v) {
    const char *path = str_cstr(path_v);
    struct stat st;
    return (stat(path, &st) == 0 && S_ISDIR(st.st_mode)) ? 1 : 0;
}

__attribute__((weak)) int64_t rt_dir_list(int64_t path_v) {
    const char *path = str_cstr(path_v);
    int64_t arr = rt_array_new(8);
    DIR *d = opendir(path);
    if (!d) return arr;
    struct dirent *ent;
    while ((ent = readdir(d)) != NULL) {
        if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) continue;
        rt_array_push(arr, str_from_cstr(ent->d_name));
    }
    closedir(d);
    return arr;
}

__attribute__((weak)) int64_t rt_dir_create(int64_t path_v, int64_t recursive) {
    const char *path = str_cstr(path_v);
    if (recursive) {
        char *tmp = strdup(path);
        for (char *p = tmp + 1; *p; p++) {
            if (*p == '/') { *p = 0; mkdir(tmp, 0755); *p = '/'; }
        }
        int r = mkdir(tmp, 0755);
        free(tmp);
        return (r == 0 || errno == EEXIST) ? 1 : 0;
    }
    return (mkdir(path, 0755) == 0 || errno == EEXIST) ? 1 : 0;
}

int64_t rt_dir_create_all(int64_t path_v) {
    return rt_dir_create(path_v, 1);
}

int64_t rt_dir_remove(int64_t path_v) {
    const char *path = str_cstr(path_v);
    return rmdir(path) == 0 ? 1 : 0;
}

int64_t rt_path_join(int64_t a_v, int64_t b_v) {
    const char *a = str_cstr(a_v);
    const char *b = str_cstr(b_v);
    size_t la = strlen(a), lb = strlen(b);
    char *buf = (char *)malloc(la + lb + 2);
    if (la > 0 && a[la-1] == '/') {
        sprintf(buf, "%s%s", a, b);
    } else {
        sprintf(buf, "%s/%s", a, b);
    }
    int64_t result = str_from_cstr(buf);
    free(buf);
    return result;
}

int64_t rt_path_parent(int64_t path_v) {
    const char *path = str_cstr(path_v);
    char *tmp = strdup(path);
    char *parent = dirname(tmp);
    int64_t result = str_from_cstr(parent);
    free(tmp);
    return result;
}

int64_t rt_path_filename(int64_t path_v) {
    const char *path = str_cstr(path_v);
    char *tmp = strdup(path);
    char *name = basename(tmp);
    int64_t result = str_from_cstr(name);
    free(tmp);
    return result;
}

int64_t rt_path_extension(int64_t path_v) {
    const char *path = str_cstr(path_v);
    const char *dot = strrchr(path, '.');
    if (!dot || dot == path) return str_from_cstr("");
    return str_from_cstr(dot + 1);
}

int64_t rt_path_absolute(int64_t path_v) {
    const char *path = str_cstr(path_v);
    char buf[4096];
    if (realpath(path, buf)) return str_from_cstr(buf);
    return path_v;
}

int64_t rt_path_normalize(int64_t path_v) {
    return rt_path_absolute(path_v);
}

int64_t rt_file_read_bytes(int64_t path_v) {
    return rt_file_read_text(path_v);
}

int64_t rt_file_read_lines(int64_t path_v) {
    int64_t text = rt_file_read_text(path_v);
    if (text == 0) return rt_array_new(0);
    const char *s = str_cstr(text);
    int64_t arr = rt_array_new(32);
    const char *start = s;
    for (const char *p = s; ; p++) {
        if (*p == '\n' || *p == '\0') {
            int64_t line = rt_string_new((int64_t)(intptr_t)start, p - start);
            rt_array_push(arr, line);
            if (*p == '\0') break;
            start = p + 1;
        }
    }
    return arr;
}

int64_t rt_file_write_bytes(int64_t path_v, int64_t data_v) {
    return rt_file_write(path_v, data_v);
}

int64_t rt_file_append_text(int64_t path_v, int64_t content_v) {
    const char *path = str_cstr(path_v);
    const char *content = str_cstr(content_v);
    int64_t len = str_len(content_v);
    FILE *f = fopen(path, "ab");
    if (!f) return 0;
    fwrite(content, 1, len, f);
    fclose(f);
    return 1;
}

int64_t rt_file_atomic_write(int64_t path_v, int64_t content_v) {
    return rt_file_write(path_v, content_v);
}

int64_t rt_file_move(int64_t src_v, int64_t dst_v) {
    return rename(str_cstr(src_v), str_cstr(dst_v)) == 0 ? 1 : 0;
}

int64_t rt_file_modified(int64_t path_v) {
    struct stat st;
    if (stat(str_cstr(path_v), &st) != 0) return 0;
    return (int64_t)st.st_mtime;
}

int64_t rt_file_modified_time(int64_t path_v) {
    return rt_file_modified(path_v);
}

int64_t rt_file_mmap_read_text(int64_t path_v) {
    return rt_file_read_text(path_v);
}

int64_t rt_file_mmap_read_bytes(int64_t path_v) {
    return rt_file_read_text(path_v);
}

int64_t rt_file_hash(int64_t path_v) {
    int64_t content = rt_file_read_text(path_v);
    if (content == 0) return 0;
    return (int64_t)hash_string(content);
}

int64_t rt_file_hash_sha256(int64_t path_v) {
    /* Stub: return a hash string representation */
    return rt_file_hash(path_v);
}

int64_t rt_list_dir_recursive(int64_t path_v) {
    /* Simple non-recursive version for bootstrap */
    return rt_dir_list(path_v);
}

/* ================================================================
 * Environment / Process
 * ================================================================ */

/* argc/argv provided by generated C's main() via __saved_argc/__saved_argv */

int64_t rt_args_get(int64_t idx) {
    extern int __saved_argc;
    extern char** __saved_argv;
    if (idx < 0 || idx >= __saved_argc) return 0;
    return str_from_cstr(__saved_argv[idx]);
}

__attribute__((weak)) int64_t rt_env_get(int64_t key_v) {
    const char *key = str_cstr(key_v);
    const char *val = getenv(key);
    return val ? str_from_cstr(val) : 0;
}

__attribute__((weak)) int64_t rt_env_set(int64_t key_v, int64_t val_v) {
    setenv(str_cstr(key_v), str_cstr(val_v), 1);
    return 1;
}

int64_t rt_env_remove(int64_t key_v) {
    unsetenv(str_cstr(key_v));
    return 1;
}

int64_t rt_env_vars(void) {
    extern char **environ;
    int64_t arr = rt_array_new(32);
    for (char **e = environ; *e; e++) {
        rt_array_push(arr, str_from_cstr(*e));
    }
    return arr;
}

int64_t rt_env_cwd(void) {
    char buf[4096];
    if (getcwd(buf, sizeof(buf))) return str_from_cstr(buf);
    return str_from_cstr(".");
}

int64_t rt_env_home(void) {
    const char *h = getenv("HOME");
    return h ? str_from_cstr(h) : str_from_cstr("/tmp");
}

int64_t rt_process_run(int64_t cmd_v, int64_t args_v) {
    const char *cmd = str_cstr(cmd_v);
    (void)args_v;
    return (int64_t)system(cmd);
}

int64_t rt_process_output(int64_t cmd_v) {
    const char *cmd = str_cstr(cmd_v);
    char buf[65536];
    FILE *p = popen(cmd, "r");
    if (!p) return str_from_cstr("");
    size_t n = fread(buf, 1, sizeof(buf) - 1, p);
    buf[n] = '\0';
    pclose(p);
    return str_from_cstr(buf);
}

int64_t rt_process_run_timeout(int64_t cmd_v, int64_t args_v, int64_t timeout_ms) {
    (void)timeout_ms;
    return rt_process_run(cmd_v, args_v);
}

int64_t rt_process_run_with_limits(int64_t cmd_v, int64_t args_v, int64_t timeout_ms, int64_t max_mem) {
    (void)timeout_ms; (void)max_mem;
    return rt_process_run(cmd_v, args_v);
}

int64_t rt_process_spawn(int64_t cmd_v, int64_t args_v) {
    (void)args_v;
    pid_t pid = fork();
    if (pid == 0) {
        execl("/bin/sh", "sh", "-c", str_cstr(cmd_v), NULL);
        _exit(127);
    }
    return (int64_t)pid;
}

int64_t rt_shell(int64_t cmd_v) {
    return (int64_t)system(str_cstr(cmd_v));
}

int64_t rt_exec(int64_t cmd_v) {
    return (int64_t)system(str_cstr(cmd_v));
}

int64_t rt_execute_native(int64_t path_v, int64_t args_v) {
    (void)args_v;
    return (int64_t)system(str_cstr(path_v));
}

void rt_exit(int64_t code) {
    exit((int)code);
}

int64_t rt_cpu_count(void) {
    return (int64_t)sysconf(_SC_NPROCESSORS_ONLN);
}

void rt_sleep_secs(int64_t secs) {
    sleep((unsigned)secs);
}

/* ================================================================
 * Math
 * ================================================================ */

int64_t rt_math_ceil(int64_t v) { union{int64_t i;double d;}u; u.i=v; return (int64_t)ceil(u.d); }
int64_t rt_math_floor(int64_t v) { union{int64_t i;double d;}u; u.i=v; return (int64_t)floor(u.d); }
int64_t rt_math_log(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=log(u.d); return u.i; }
int64_t rt_math_log2(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=log2(u.d); return u.i; }
int64_t rt_math_log10(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=log10(u.d); return u.i; }
int64_t rt_math_asin(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=asin(u.d); return u.i; }
int64_t rt_math_acos(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=acos(u.d); return u.i; }
int64_t rt_math_atan(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=atan(u.d); return u.i; }
int64_t rt_math_atan2(int64_t a, int64_t b) {
    union{int64_t i;double d;} ua,ub,ur;
    ua.i=a; ub.i=b; ur.d=atan2(ua.d,ub.d); return ur.i;
}
int64_t rt_math_sinh(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=sinh(u.d); return u.i; }
int64_t rt_math_cosh(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=cosh(u.d); return u.i; }
int64_t rt_math_tanh(int64_t v) { union{int64_t i;double d;}u; u.i=v; u.d=tanh(u.d); return u.i; }

/* ================================================================
 * Time
 * ================================================================ */

int64_t rt_time_now(void) {
    return (int64_t)time(NULL);
}

int64_t rt_time_millis(void) {
    struct timeval tv;
    gettimeofday(&tv, NULL);
    return (int64_t)(tv.tv_sec * 1000 + tv.tv_usec / 1000);
}

int64_t rt_time_now_unix_millis(void) { return rt_time_millis(); }

int64_t rt_time_now_iso(void) {
    time_t t = time(NULL);
    struct tm *tm = gmtime(&t);
    char buf[64];
    strftime(buf, sizeof(buf), "%Y-%m-%dT%H:%M:%SZ", tm);
    return str_from_cstr(buf);
}

int64_t rt_time_year(int64_t ts) { time_t t=(time_t)ts; return gmtime(&t)->tm_year+1900; }
int64_t rt_time_month(int64_t ts) { time_t t=(time_t)ts; return gmtime(&t)->tm_mon+1; }
int64_t rt_time_day(int64_t ts) { time_t t=(time_t)ts; return gmtime(&t)->tm_mday; }
int64_t rt_time_hour(int64_t ts) { time_t t=(time_t)ts; return gmtime(&t)->tm_hour; }
int64_t rt_time_minute(int64_t ts) { time_t t=(time_t)ts; return gmtime(&t)->tm_min; }
int64_t rt_time_second(int64_t ts) { time_t t=(time_t)ts; return gmtime(&t)->tm_sec; }

int64_t rt_timestamp_parse(int64_t s) { (void)s; return rt_time_now(); }
int64_t rt_timestamp_from_iso(int64_t s) { (void)s; return rt_time_now(); }
int64_t rt_timestamp_to_iso(int64_t ts) { return rt_time_now_iso(); }
int64_t rt_timestamp_to_string(int64_t ts) { return rt_time_now_iso(); }
int64_t rt_timestamp_diff_seconds(int64_t a, int64_t b) { return a - b; }

/* ================================================================
 * Random
 * ================================================================ */

static int rand_inited = 0;
static void ensure_rand(void) { if (!rand_inited) { srand(time(NULL)); rand_inited = 1; } }

int64_t rt_random_randint(int64_t lo, int64_t hi) {
    ensure_rand();
    if (hi <= lo) return lo;
    return lo + rand() % (hi - lo + 1);
}

int64_t rt_random_uniform(void) {
    ensure_rand();
    union { double d; int64_t i; } u;
    u.d = (double)rand() / RAND_MAX;
    return u.i;
}

int64_t rt_uuid_v4(void) {
    ensure_rand();
    char buf[40];
    snprintf(buf, sizeof(buf), "%08x-%04x-4%03x-%04x-%012lx",
        rand(), rand()&0xffff, rand()&0xfff, (rand()&0x3fff)|0x8000, (long)rand());
    return str_from_cstr(buf);
}

/* ================================================================
 * Logging
 * ================================================================ */

static int64_t log_global_level = 3; /* INFO */

int64_t rt_log_get_global_level(void) { return log_global_level; }
int64_t rt_log_set_global_level(int64_t level) { log_global_level = level; return 0; }
int64_t rt_log_get_scope_level(int64_t scope) { (void)scope; return log_global_level; }
int64_t rt_log_set_scope_level(int64_t scope, int64_t level) { (void)scope; (void)level; return 0; }
int64_t rt_log_is_enabled(int64_t scope, int64_t level) { (void)scope; return level >= log_global_level; }
int64_t rt_log_emit(int64_t scope, int64_t level, int64_t msg) {
    if (level >= log_global_level) {
        fprintf(stderr, "[LOG %ld] %s\n", (long)level, str_cstr(msg));
    }
    return 0;
}
int64_t rt_log_clear_scope_levels(void) { return 0; }

/* ================================================================
 * Volatile / Barrier (stubs)
 * ================================================================ */

int64_t rt_read_volatile_i64(int64_t addr) { return *(volatile int64_t*)(intptr_t)addr; }
void rt_write_volatile_i64(int64_t addr, int64_t val) { *(volatile int64_t*)(intptr_t)addr = val; }
void rt_memory_barrier(void) { __sync_synchronize(); }
void rt_load_barrier(void) { __sync_synchronize(); }
void rt_store_barrier(void) { __sync_synchronize(); }

int64_t rt_volatile_read_u8(int64_t addr) { return *(volatile uint8_t*)(intptr_t)addr; }
int64_t rt_volatile_read_u16(int64_t addr) { return *(volatile uint16_t*)(intptr_t)addr; }
int64_t rt_volatile_read_u32(int64_t addr) { return *(volatile uint32_t*)(intptr_t)addr; }
int64_t rt_volatile_read_u64(int64_t addr) { return *(volatile int64_t*)(intptr_t)addr; }
void rt_volatile_write_u8(int64_t addr, int64_t val) { *(volatile uint8_t*)(intptr_t)addr = (uint8_t)val; }
void rt_volatile_write_u16(int64_t addr, int64_t val) { *(volatile uint16_t*)(intptr_t)addr = (uint16_t)val; }
void rt_volatile_write_u32(int64_t addr, int64_t val) { *(volatile uint32_t*)(intptr_t)addr = (uint32_t)val; }
void rt_volatile_write_u64(int64_t addr, int64_t val) { *(volatile int64_t*)(intptr_t)addr = val; }

/* ================================================================
 * Misc runtime stubs
 * ================================================================ */

int64_t rt_get_host_target_code(void) {
#if defined(__x86_64__)
    return str_from_cstr("x86_64-linux-gnu");
#elif defined(__aarch64__)
    return str_from_cstr("aarch64-linux-gnu");
#else
    return str_from_cstr("unknown-linux-gnu");
#endif
}

int64_t rt_cli_handle_compile(int64_t args) { (void)args; return 0; }
int64_t rt_indirect_call(int64_t fn, int64_t args) { (void)fn; (void)args; return 0; }

/* Doctest stubs */
int64_t doctest_read_file(int64_t path) { return rt_file_read_text(path); }
int64_t doctest_path_exists(int64_t path) { return rt_file_exists(path); }
int64_t doctest_is_file(int64_t path) {
    struct stat st;
    return (stat(str_cstr(path), &st) == 0 && S_ISREG(st.st_mode)) ? 1 : 0;
}
int64_t doctest_is_dir(int64_t path) { return rt_dir_exists(path); }
int64_t doctest_walk_directory(int64_t path, int64_t ext, int64_t recursive) {
    (void)ext; (void)recursive;
    return rt_dir_list(path);
}
int64_t doctest_path_has_extension(int64_t path, int64_t ext) {
    const char *p = str_cstr(path);
    const char *e = str_cstr(ext);
    size_t pl = strlen(p), el = strlen(e);
    if (el > pl) return 0;
    return strcmp(p + pl - el, e) == 0 ? 1 : 0;
}
int64_t doctest_path_contains(int64_t path, int64_t substr) {
    return strstr(str_cstr(path), str_cstr(substr)) != NULL ? 1 : 0;
}

/* Contract checking */
void simple_contract_check(int64_t cond, int64_t kind, int64_t name_ptr, int64_t name_len) {
    (void)kind; (void)name_ptr; (void)name_len;
    if (!cond) {
        fprintf(stderr, "Contract violation\n");
        abort();
    }
}
void simple_contract_check_msg(int64_t cond, int64_t kind, int64_t name_ptr, int64_t name_len,
                               int64_t msg_ptr, int64_t msg_len) {
    (void)kind; (void)name_ptr; (void)name_len; (void)msg_ptr; (void)msg_len;
    if (!cond) {
        fprintf(stderr, "Contract violation\n");
        abort();
    }
}

/* Optional check */
int64_t __spl_optional_check(int64_t v) { return v != 0 ? 1 : 0; }

/* Pointer operations (stubs using plain int64_t) */
int64_t rt_unique_new(int64_t val) { int64_t *p = (int64_t*)malloc(8); *p = val; return (int64_t)(intptr_t)p; }
int64_t rt_unique_get(int64_t ptr) { return *(int64_t*)(intptr_t)ptr; }
int64_t rt_unique_set(int64_t ptr, int64_t val) { *(int64_t*)(intptr_t)ptr = val; return 0; }
void rt_unique_free(int64_t ptr) { free((void*)(intptr_t)ptr); }
int64_t rt_unique_needs_trace(int64_t ptr) { (void)ptr; return 0; }

int64_t rt_shared_new(int64_t val) { return rt_unique_new(val); }
int64_t rt_shared_get(int64_t ptr) { return rt_unique_get(ptr); }
int64_t rt_shared_clone(int64_t ptr) { (void)ptr; return ptr; }
int64_t rt_shared_ref_count(int64_t ptr) { (void)ptr; return 1; }
int64_t rt_shared_release(int64_t ptr) { (void)ptr; return 0; }
int64_t rt_shared_needs_trace(int64_t ptr) { (void)ptr; return 0; }
int64_t rt_shared_downgrade(int64_t ptr) { return ptr; }

int64_t rt_weak_new(int64_t a, int64_t b) { (void)b; return a; }
int64_t rt_weak_upgrade(int64_t ptr) { return ptr; }
int64_t rt_weak_is_valid(int64_t ptr) { return ptr != 0; }
void rt_weak_free(int64_t ptr) { (void)ptr; }

int64_t rt_handle_new(int64_t val) { return rt_unique_new(val); }
int64_t rt_handle_get(int64_t ptr) { return rt_unique_get(ptr); }
int64_t rt_handle_set(int64_t ptr, int64_t val) { return rt_unique_set(ptr, val); }
void rt_handle_free(int64_t ptr) { rt_unique_free(ptr); }
int64_t rt_handle_is_valid(int64_t ptr) { return ptr != 0; }

int64_t rt_alloc(int64_t size) { return (int64_t)(intptr_t)calloc(1, size); }
void rt_free(int64_t ptr, int64_t size) { (void)size; free((void*)(intptr_t)ptr); }
int64_t rt_ptr_to_value(int64_t ptr) { return ptr; }
int64_t rt_value_to_ptr(int64_t val) { return val; }

/* Async/Actor/Generator/Channel stubs */
int64_t rt_wait(int64_t v) { return v; }
int64_t rt_future_new(int64_t a, int64_t b) { (void)a; (void)b; return 0; }
int64_t rt_future_await(int64_t f) { (void)f; return 0; }
int64_t rt_future_is_ready(int64_t f) { (void)f; return 1; }
int64_t rt_future_get_result(int64_t f) { (void)f; return 0; }
int64_t rt_future_all(int64_t a) { (void)a; return 0; }
int64_t rt_future_race(int64_t a) { (void)a; return 0; }
int64_t rt_future_resolve(int64_t a) { (void)a; return 0; }
int64_t rt_future_reject(int64_t a) { (void)a; return 0; }
int64_t rt_actor_spawn(int64_t a, int64_t b) { (void)a; (void)b; return 0; }
void rt_actor_send(int64_t a, int64_t m) { (void)a; (void)m; }
int64_t rt_actor_recv(void) { return 0; }
int64_t rt_actor_join(int64_t a) { (void)a; return 0; }
int64_t rt_actor_id(int64_t a) { (void)a; return 0; }
int64_t rt_actor_is_alive(int64_t a) { (void)a; return 0; }
int64_t rt_channel_new(void) { return 0; }
int64_t rt_channel_send(int64_t c, int64_t v) { (void)c; (void)v; return 0; }
int64_t rt_channel_recv(int64_t c) { (void)c; return 0; }
int64_t rt_channel_try_recv(int64_t c) { (void)c; return 0; }
int64_t rt_channel_recv_timeout(int64_t c, int64_t t) { (void)c; (void)t; return 0; }
void rt_channel_close(int64_t c) { (void)c; }
int64_t rt_channel_is_closed(int64_t c) { (void)c; return 1; }
int64_t rt_channel_id(int64_t c) { (void)c; return 0; }
void rt_channel_free(int64_t c) { (void)c; }
int64_t rt_executor_set_mode(int64_t m) { (void)m; return 0; }
int64_t rt_executor_get_mode(void) { return 0; }
void rt_executor_start(void) {}
void rt_executor_set_workers(int64_t n) { (void)n; }
int64_t rt_executor_poll(void) { return 0; }
int64_t rt_executor_poll_all(void) { return 0; }
int64_t rt_executor_pending_count(void) { return 0; }
void rt_executor_shutdown(void) {}
int64_t rt_executor_is_manual(void) { return 0; }
int64_t rt_thread_spawn_isolated(int64_t a, int64_t b) { (void)a; (void)b; return 0; }
int64_t rt_thread_spawn_isolated2(int64_t a, int64_t b, int64_t c) { (void)a; (void)b; (void)c; return 0; }
int64_t rt_thread_join(int64_t t) { (void)t; return 0; }
int64_t rt_thread_is_done(int64_t t) { (void)t; return 1; }
int64_t rt_thread_id(int64_t t) { (void)t; return 0; }
void rt_thread_free(int64_t t) { (void)t; }
__attribute__((weak)) int64_t rt_thread_available_parallelism(void) { return rt_cpu_count(); }
void rt_thread_sleep(int64_t ms) { usleep(ms * 1000); }
void rt_thread_yield(void) { sched_yield(); }
int64_t rt_generator_new(int64_t a, int64_t b, int64_t c) { (void)a; (void)b; (void)c; return 0; }
int64_t rt_generator_next(int64_t g) { (void)g; return 0; }
int64_t rt_generator_get_state(int64_t g) { (void)g; return 0; }
void rt_generator_set_state(int64_t g, int64_t s) { (void)g; (void)s; }
void rt_generator_store_slot(int64_t g, int64_t i, int64_t v) { (void)g; (void)i; (void)v; }
int64_t rt_generator_load_slot(int64_t g, int64_t i) { (void)g; (void)i; return 0; }
int64_t rt_generator_get_ctx(int64_t g) { (void)g; return 0; }
void rt_generator_mark_done(int64_t g) { (void)g; }
int64_t rt_interp_call(int64_t name, int64_t len, int64_t argc, int64_t argv) {
    (void)name; (void)len; (void)argc; (void)argv; return 0;
}
int64_t rt_interp_eval(int64_t expr) { (void)expr; return 0; }
int64_t rt_function_not_found(int64_t name, int64_t len) {
    fprintf(stderr, "Function not found: %.*s\n", (int)len, (const char*)(intptr_t)name);
    return 0;
}
int64_t rt_method_not_found(int64_t recv, int64_t name, int64_t len, int64_t argc) {
    (void)recv; (void)argc;
    fprintf(stderr, "Method not found: %.*s\n", (int)len, (const char*)(intptr_t)name);
    return 0;
}

/* Contract violation */
int64_t rt_contract_violation_new(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) {
    (void)a; (void)b; (void)c; (void)d; (void)e; return 0;
}
int64_t rt_contract_violation_kind(int64_t v) { (void)v; return 0; }
int64_t rt_contract_violation_func_name(int64_t v) { (void)v; return str_from_cstr(""); }
int64_t rt_contract_violation_message(int64_t v) { (void)v; return str_from_cstr(""); }
int64_t rt_is_contract_violation(int64_t v) { (void)v; return 0; }
void rt_contract_violation_free(int64_t v) { (void)v; }

/* Exec manager — weak symbols so generated C implementations take priority */
__attribute__((weak)) int64_t rt_exec_manager_create(int64_t backend) { (void)backend; return 0; }
__attribute__((weak)) int64_t rt_exec_manager_compile(int64_t handle, int64_t mir_data) { (void)handle; (void)mir_data; return 0; }
__attribute__((weak)) int64_t rt_exec_manager_execute(int64_t handle, int64_t name, int64_t args) { (void)handle; (void)name; (void)args; return 0; }
__attribute__((weak)) int64_t rt_exec_manager_has_function(int64_t handle, int64_t name) { (void)handle; (void)name; return 0; }
__attribute__((weak)) void rt_exec_manager_cleanup(int64_t handle) { (void)handle; }

/* ================================================================
 * __spl_* Helper Functions
 * ================================================================ */

/* Value-to-string conversion */
int64_t __spl_to_string(int64_t v) {
    if (v == 0) return str_from_cstr("nil");
    if (is_heap_obj(v) && obj_type(v) == OBJ_STRING) return v;
    char buf[64];
    snprintf(buf, sizeof(buf), "%ld", (long)v);
    return str_from_cstr(buf);
}

int64_t __spl_string_concat(int64_t a, int64_t b) {
    return rt_string_concat(__spl_to_string(a), __spl_to_string(b));
}

/* __spl_add: runtime-typed Add — string concat if either is a string, else integer add */
int64_t __spl_add(int64_t a, int64_t b) {
    if ((is_heap_obj(a) && obj_type(a) == OBJ_STRING) ||
        (is_heap_obj(b) && obj_type(b) == OBJ_STRING)) {
        return rt_string_concat(__spl_to_string(a), __spl_to_string(b));
    }
    return a + b;
}

/* Print */
int64_t __spl_print(int64_t v) {
    if (is_heap_obj(v) && obj_type(v) == OBJ_STRING) {
        printf("%s\n", as_string(v)->data);
    } else if (v == 0) {
        printf("nil\n");
    } else {
        printf("%ld\n", (long)v);
    }
    return 0;
}

int64_t __spl_eprint(int64_t v) {
    if (is_heap_obj(v) && obj_type(v) == OBJ_STRING) {
        fprintf(stderr, "%s\n", as_string(v)->data);
    } else if (v == 0) {
        fprintf(stderr, "nil\n");
    } else {
        fprintf(stderr, "%ld\n", (long)v);
    }
    return 0;
}

/* Panic */
int64_t __spl_panic(int64_t msg) {
    fprintf(stderr, "PANIC: %s\n", str_cstr(msg));
    abort();
    return 0;
}

/* Dict */
int64_t __spl_dict_new(void) { return rt_dict_new(8); }

/* Null coalesce */
int64_t __spl_null_coalesce(int64_t a, int64_t b) { return a != 0 ? a : b; }

/* Range */
int64_t __spl_range(int64_t start, int64_t end) {
    int64_t arr = rt_array_new(end - start > 0 ? end - start : 4);
    for (int64_t i = start; i < end; i++) {
        rt_array_push(arr, i);
    }
    return arr;
}

/* Slice */
int64_t __spl_slice(int64_t collection, int64_t start, int64_t end) {
    return rt_slice(collection, start, end, 1);
}

/* Type-of */
int64_t __spl_type_of(int64_t v) {
    if (v == 0) return str_from_cstr("nil");
    if (!is_heap_obj(v)) return str_from_cstr("int");
    switch (obj_type(v)) {
        case OBJ_STRING: return str_from_cstr("text");
        case OBJ_ARRAY: return str_from_cstr("array");
        case OBJ_DICT: return str_from_cstr("dict");
        case OBJ_OBJECT: return str_from_cstr("object");
        case OBJ_CLOSURE: return str_from_cstr("closure");
        case OBJ_TUPLE: return str_from_cstr("tuple");
        case OBJ_ENUM: return str_from_cstr("enum");
        default: return str_from_cstr("unknown");
    }
}

/* ================================================================
 * __spl_method_* Dispatch Functions
 *
 * These handle method calls like obj.len(), obj.push(x), etc.
 * The generated C emits calls to __spl_method_X(receiver, args...).
 * ================================================================ */

/* Generic method dispatch: many methods just delegate to rt_* */
int64_t __spl_method_len(int64_t recv) {
    if (!is_heap_obj(recv)) return 0;
    switch (obj_type(recv)) {
        case OBJ_ARRAY:  return rt_array_len(recv);
        case OBJ_DICT:   return rt_dict_len(recv);
        case OBJ_STRING: return as_string(recv)->len;
        case OBJ_TUPLE:  return rt_tuple_len(recv);
        default:         return 0;
    }
}
int64_t __spl_method_push(int64_t recv, int64_t val) { return rt_array_push(recv, val); }
int64_t __spl_method_pop(int64_t recv) { return rt_array_pop(recv); }
int64_t __spl_method_keys(int64_t recv) { return rt_dict_keys(recv); }
int64_t __spl_method_values(int64_t recv) { return rt_dict_values(recv); }
int64_t __spl_method_get(int64_t recv, int64_t key) { return rt_index_get(recv, key); }
int64_t __spl_method_contains_key(int64_t recv, int64_t key) { return rt_contains(recv, key); }

int64_t __spl_method_is_empty(int64_t recv) { return __spl_method_len(recv) == 0 ? 1 : 0; }
int64_t __spl_method_is_none(int64_t recv) { return recv == 0 ? 1 : 0; }
int64_t __spl_method_is_ok(int64_t recv) {
    if (is_heap_obj(recv) && obj_type(recv) == OBJ_TUPLE)
        return rt_tuple_get(recv, 0) == 0 ? 1 : 0;
    return recv != 0 ? 1 : 0;
}
int64_t __spl_method_is_err(int64_t recv) { return !__spl_method_is_ok(recv); }
int64_t __spl_method_unwrap(int64_t recv) {
    if (recv == 0) {
        void *caller = __builtin_return_address(0);
        void *caller2 = __builtin_return_address(1);
        void *caller3 = __builtin_return_address(2);
        fprintf(stderr, "unwrap on nil (caller: %p, %p, %p)\n", caller, caller2, caller3);
        abort();
    }
    if (is_heap_obj(recv) && obj_type(recv) == OBJ_TUPLE && as_tuple(recv)->len >= 2) {
        return rt_tuple_get(recv, 1);
    }
    /* Some(x) is compiled as rt_object_new(0, 1) with field[0] = x.
       Unwrap extracts the inner value. */
    if (is_heap_obj(recv) && obj_type(recv) == OBJ_OBJECT) {
        SplObject *o = as_object(recv);
        if (o->field_count == 1) {
            return o->fields[0];
        }
    }
    return recv;
}
int64_t __spl_method_unwrap_err(int64_t recv) {
    if (is_heap_obj(recv) && obj_type(recv) == OBJ_TUPLE && as_tuple(recv)->len >= 2) {
        return rt_tuple_get(recv, 1);
    }
    return 0;
}

/* String methods */
int64_t __spl_method_lower(int64_t s) {
    if (!is_heap_obj(s) || obj_type(s) != OBJ_STRING) return s;
    SplString *src = as_string(s);
    SplString *dst = (SplString *)malloc(sizeof(SplString) + src->len + 1);
    dst->hdr.obj_type = OBJ_STRING; dst->hdr.extra = 0; dst->len = src->len;
    for (int64_t i = 0; i < src->len; i++) dst->data[i] = tolower(src->data[i]);
    dst->data[src->len] = '\0';
    return (int64_t)(intptr_t)dst;
}

int64_t __spl_method_upper(int64_t s) {
    if (!is_heap_obj(s) || obj_type(s) != OBJ_STRING) return s;
    SplString *src = as_string(s);
    SplString *dst = (SplString *)malloc(sizeof(SplString) + src->len + 1);
    dst->hdr.obj_type = OBJ_STRING; dst->hdr.extra = 0; dst->len = src->len;
    for (int64_t i = 0; i < src->len; i++) dst->data[i] = toupper(src->data[i]);
    dst->data[src->len] = '\0';
    return (int64_t)(intptr_t)dst;
}

int64_t __spl_method_to_upper(int64_t s) { return __spl_method_upper(s); }

int64_t __spl_method_trim(int64_t s) {
    if (!is_heap_obj(s) || obj_type(s) != OBJ_STRING) return s;
    const char *data = as_string(s)->data;
    int64_t len = as_string(s)->len;
    int64_t start = 0, end = len;
    while (start < end && isspace(data[start])) start++;
    while (end > start && isspace(data[end-1])) end--;
    return rt_string_new((int64_t)(intptr_t)(data + start), end - start);
}

int64_t __spl_method_contains(int64_t s, int64_t sub) {
    return strstr(str_cstr(s), str_cstr(sub)) != NULL ? 1 : 0;
}

int64_t __spl_method_starts_with(int64_t s, int64_t prefix) {
    const char *ss = str_cstr(s), *pp = str_cstr(prefix);
    size_t pl = strlen(pp);
    return strncmp(ss, pp, pl) == 0 ? 1 : 0;
}

int64_t __spl_method_ends_with(int64_t s, int64_t suffix) {
    const char *ss = str_cstr(s), *pp = str_cstr(suffix);
    size_t sl = strlen(ss), pl = strlen(pp);
    if (pl > sl) return 0;
    return strcmp(ss + sl - pl, pp) == 0 ? 1 : 0;
}

int64_t __spl_method_replace(int64_t s, int64_t from, int64_t to) {
    const char *src = str_cstr(s);
    const char *old_s = str_cstr(from);
    const char *new_s = str_cstr(to);
    size_t old_len = strlen(old_s), new_len = strlen(new_s);
    if (old_len == 0) return s;

    /* Count occurrences */
    int count = 0;
    const char *p = src;
    while ((p = strstr(p, old_s))) { count++; p += old_len; }
    if (count == 0) return s;

    size_t src_len = strlen(src);
    size_t result_len = src_len + count * (new_len - old_len);
    char *buf = (char *)malloc(result_len + 1);
    char *dest = buf;
    p = src;
    while (*p) {
        if (strncmp(p, old_s, old_len) == 0) {
            memcpy(dest, new_s, new_len);
            dest += new_len;
            p += old_len;
        } else {
            *dest++ = *p++;
        }
    }
    *dest = '\0';
    int64_t result = str_from_cstr(buf);
    free(buf);
    return result;
}

int64_t __spl_method_split(int64_t s, int64_t sep) {
    const char *src = str_cstr(s);
    const char *delim = str_cstr(sep);
    int64_t arr = rt_array_new(8);
    size_t dl = strlen(delim);
    if (dl == 0) {
        /* Split each character */
        for (const char *p = src; *p; p++) {
            rt_array_push(arr, rt_string_new((int64_t)(intptr_t)p, 1));
        }
        return arr;
    }
    const char *start = src;
    while (1) {
        const char *found = strstr(start, delim);
        if (!found) {
            rt_array_push(arr, str_from_cstr(start));
            break;
        }
        rt_array_push(arr, rt_string_new((int64_t)(intptr_t)start, found - start));
        start = found + dl;
    }
    return arr;
}

/* Arity-suffixed versions for generated C macro dispatch */
int64_t __spl_method_split_2(int64_t s, int64_t sep) {
    return __spl_method_split(s, sep);
}

int64_t __spl_method_split_3(int64_t s, int64_t sep, int64_t limit) {
    (void)limit;
    return __spl_method_split(s, sep);
}

int64_t __spl_method_join(int64_t recv, int64_t sep) {
    if (!is_heap_obj(recv) || obj_type(recv) != OBJ_ARRAY) return str_from_cstr("");
    SplArray *a = as_array(recv);
    const char *sep_s = str_cstr(sep);
    size_t sep_len = strlen(sep_s);
    /* Estimate total length */
    size_t total = 0;
    for (int64_t i = 0; i < a->len; i++) {
        total += str_len(a->items[i]);
        if (i > 0) total += sep_len;
    }
    char *buf = (char *)malloc(total + 1);
    char *p = buf;
    for (int64_t i = 0; i < a->len; i++) {
        if (i > 0 && sep_len > 0) { memcpy(p, sep_s, sep_len); p += sep_len; }
        const char *s = str_cstr(a->items[i]);
        size_t sl = strlen(s);
        memcpy(p, s, sl);
        p += sl;
    }
    *p = '\0';
    int64_t result = str_from_cstr(buf);
    free(buf);
    return result;
}

int64_t __spl_method_index_of(int64_t recv, int64_t sub) {
    const char *s = str_cstr(recv);
    const char *n = str_cstr(sub);
    const char *found = strstr(s, n);
    return found ? (int64_t)(found - s) : -1;
}

int64_t __spl_method_find(int64_t recv, int64_t sub) {
    return __spl_method_index_of(recv, sub);
}

int64_t __spl_method_substring(int64_t recv, int64_t start, int64_t end) {
    return rt_slice(recv, start, end, 1);
}

int64_t __spl_method_slice(int64_t recv, int64_t start, int64_t end) {
    return rt_slice(recv, start, end, 1);
}

int64_t __spl_method_repeat(int64_t recv, int64_t count) {
    const char *s = str_cstr(recv);
    size_t sl = strlen(s);
    if (count <= 0 || sl == 0) return str_from_cstr("");
    size_t total = sl * count;
    char *buf = (char *)malloc(total + 1);
    for (int64_t i = 0; i < count; i++) memcpy(buf + i * sl, s, sl);
    buf[total] = '\0';
    int64_t result = str_from_cstr(buf);
    free(buf);
    return result;
}

int64_t __spl_method_bytes(int64_t recv) {
    if (!is_heap_obj(recv) || obj_type(recv) != OBJ_STRING) return rt_array_new(0);
    SplString *s = as_string(recv);
    int64_t arr = rt_array_new(s->len);
    for (int64_t i = 0; i < s->len; i++) {
        rt_array_push(arr, (int64_t)(uint8_t)s->data[i]);
    }
    return arr;
}

int64_t __spl_method_ord(int64_t recv) {
    const char *s = str_cstr(recv);
    return s[0] ? (int64_t)(uint8_t)s[0] : 0;
}

int64_t __spl_method_is_alphabetic(int64_t recv) {
    const char *s = str_cstr(recv);
    return *s && isalpha(*s) ? 1 : 0;
}

int64_t __spl_method_is_alphanumeric(int64_t recv) {
    const char *s = str_cstr(recv);
    return *s && isalnum(*s) ? 1 : 0;
}

int64_t __spl_method_is_whitespace(int64_t recv) {
    const char *s = str_cstr(recv);
    return *s && isspace(*s) ? 1 : 0;
}

/* Numeric conversion methods */
int64_t __spl_method_to_i64(int64_t recv) {
    if (is_heap_obj(recv) && obj_type(recv) == OBJ_STRING)
        return strtol(as_string(recv)->data, NULL, 10);
    return recv;
}
int64_t __spl_method_to_int(int64_t recv) { return __spl_method_to_i64(recv); }

int64_t __spl_method_to_f64(int64_t recv) {
    if (is_heap_obj(recv) && obj_type(recv) == OBJ_STRING) {
        union { double d; int64_t i; } u;
        u.d = strtod(as_string(recv)->data, NULL);
        return u.i;
    }
    return recv;
}
int64_t __spl_method_to_float_or(int64_t recv, int64_t default_val) {
    (void)default_val;
    return __spl_method_to_f64(recv);
}

int64_t __spl_method_i64(int64_t recv) { return recv; }
int64_t __spl_method_f64(int64_t recv) { return recv; }
int64_t __spl_method_bool(int64_t recv) { return recv != 0 ? 1 : 0; }
int64_t __spl_method_text(int64_t recv) { return __spl_to_string(recv); }

int64_t __spl_method_to_hex(int64_t recv) {
    char buf[32];
    snprintf(buf, sizeof(buf), "%lx", (unsigned long)recv);
    return str_from_cstr(buf);
}

int64_t __spl_method_type_name(int64_t recv) { return __spl_type_of(recv); }

/* Map and enumerate for arrays */
int64_t __spl_method_map(int64_t recv, int64_t func) {
    if (!is_heap_obj(recv) || obj_type(recv) != OBJ_ARRAY) return rt_array_new(0);
    SplArray *a = as_array(recv);
    int64_t result = rt_array_new(a->len);
    int64_t fptr = rt_closure_func_ptr(func);
    if (fptr) {
        typedef int64_t (*fn1)(int64_t);
        fn1 f = (fn1)(intptr_t)fptr;
        for (int64_t i = 0; i < a->len; i++) {
            rt_array_push(result, f(a->items[i]));
        }
    } else {
        for (int64_t i = 0; i < a->len; i++) {
            rt_array_push(result, a->items[i]);
        }
    }
    return result;
}

int64_t __spl_method_enumerate(int64_t recv) {
    if (!is_heap_obj(recv) || obj_type(recv) != OBJ_ARRAY) return rt_array_new(0);
    SplArray *a = as_array(recv);
    int64_t result = rt_array_new(a->len);
    for (int64_t i = 0; i < a->len; i++) {
        int64_t pair = rt_tuple_new(2);
        rt_tuple_set(pair, 0, i);
        rt_tuple_set(pair, 1, a->items[i]);
        rt_array_push(result, pair);
    }
    return result;
}

/* Methods that create enum/struct variants (return a tagged representation) */
/* These are used for pattern construction like Type.Variant(...) */
/* We use a simple approach: return an enum with discriminant = hash of variant name */

static int64_t variant_enum(const char *name, int64_t payload) {
    uint64_t h = 14695981039346656037ULL;
    while (*name) { h ^= (uint8_t)*name++; h *= 1099511628211ULL; }
    return rt_enum_new(0, (int64_t)(h & 0xFFFF), payload);
}

/* Generate all remaining __spl_method_* as variant constructors or identity stubs */
#define SPL_METHOD_VARIANT_1(name) \
    int64_t __spl_method_##name(int64_t recv) { return variant_enum(#name, recv); }
#define SPL_METHOD_VARIANT_2(name) \
    int64_t __spl_method_##name(int64_t recv, int64_t arg1) { (void)recv; return variant_enum(#name, arg1); }

/* Enum variant constructors (take receiver which is the type, return enum) */
SPL_METHOD_VARIANT_1(ActorType)
SPL_METHOD_VARIANT_1(Aggregate)
SPL_METHOD_VARIANT_1(Alloc)
SPL_METHOD_VARIANT_1(Arg)
SPL_METHOD_VARIANT_1(Array)
SPL_METHOD_VARIANT_1(AsmAssert)
SPL_METHOD_VARIANT_1(Assign)
SPL_METHOD_VARIANT_1(Await)
SPL_METHOD_VARIANT_1(BinOp)
SPL_METHOD_VARIANT_1(Bool)
SPL_METHOD_VARIANT_1(BoolLit)
SPL_METHOD_VARIANT_1(Break)
SPL_METHOD_VARIANT_1(Call)
SPL_METHOD_VARIANT_1(CallIndirect)
SPL_METHOD_VARIANT_1(Cast)
SPL_METHOD_VARIANT_1(Const)
SPL_METHOD_VARIANT_1(Continue)
SPL_METHOD_VARIANT_1(Copy)
SPL_METHOD_VARIANT_1(CUDA)
SPL_METHOD_VARIANT_1(CudaPtx)
SPL_METHOD_VARIANT_1(Downcast)
SPL_METHOD_VARIANT_1(Expr)
SPL_METHOD_VARIANT_1(Field)
SPL_METHOD_VARIANT_1(Float)
SPL_METHOD_VARIANT_1(FloatLit)
SPL_METHOD_VARIANT_1(For)
SPL_METHOD_VARIANT_1(FuncPtr)
SPL_METHOD_VARIANT_1(Function)
SPL_METHOD_VARIANT_1(Generator)
SPL_METHOD_VARIANT_1(GetElementPtr)
SPL_METHOD_VARIANT_1(GetField)
SPL_METHOD_VARIANT_1(Goto)
SPL_METHOD_VARIANT_1(If)
SPL_METHOD_VARIANT_1(Index)
SPL_METHOD_VARIANT_1(Infer)
SPL_METHOD_VARIANT_1(InlineAsm)
SPL_METHOD_VARIANT_1(Int)
SPL_METHOD_VARIANT_1(IntLit)
SPL_METHOD_VARIANT_1(Json)
SPL_METHOD_VARIANT_1(Let)
SPL_METHOD_VARIANT_1(Literal)
SPL_METHOD_VARIANT_1(Load)
SPL_METHOD_VARIANT_1(Loop)
SPL_METHOD_VARIANT_1(Move)
SPL_METHOD_VARIANT_1(Named)
SPL_METHOD_VARIANT_1(Opaque)
SPL_METHOD_VARIANT_1(Optional)
SPL_METHOD_VARIANT_1(PipeForward)
SPL_METHOD_VARIANT_1(Promise)
SPL_METHOD_VARIANT_1(Ptr)
SPL_METHOD_VARIANT_1(Raw)
SPL_METHOD_VARIANT_1(Receive)
SPL_METHOD_VARIANT_1(Ref)
SPL_METHOD_VARIANT_1(Regex)
SPL_METHOD_VARIANT_1(Return)
SPL_METHOD_VARIANT_1(Send)
SPL_METHOD_VARIANT_1(SetField)
SPL_METHOD_VARIANT_1(Shell)
SPL_METHOD_VARIANT_1(Spawn)
SPL_METHOD_VARIANT_1(Sql)
SPL_METHOD_VARIANT_1(Store)
SPL_METHOD_VARIANT_1(Str)
SPL_METHOD_VARIANT_1(StringLit)
SPL_METHOD_VARIANT_1(Switch)
SPL_METHOD_VARIANT_1(Throw)
SPL_METHOD_VARIANT_1(Tuple)
SPL_METHOD_VARIANT_1(UnaryOp)
SPL_METHOD_VARIANT_1(Var)
SPL_METHOD_VARIANT_1(While)
SPL_METHOD_VARIANT_1(With)
SPL_METHOD_VARIANT_1(Yield)

/* Methods that take extra args */
int64_t __spl_method_add_import(int64_t recv, int64_t imp) { (void)recv; return imp; }
int64_t __spl_method_backend_kind(int64_t recv) { return recv; }
int64_t __spl_method_begin_namespace(int64_t recv, int64_t name) { (void)recv; return name; }
int64_t __spl_method_blocks_contains_key(int64_t recv, int64_t key) { return rt_contains(recv, key); }
int64_t __spl_method_blocks_remove(int64_t recv, int64_t key) { (void)key; return recv; }
int64_t __spl_method_build(int64_t recv) { return recv; }
int64_t __spl_method_compile_module(int64_t recv, int64_t mod) { (void)recv; return mod; }
int64_t __spl_method_compatibility_build(int64_t recv) { return recv; }
int64_t __spl_method_create(int64_t recv) { return recv; }
int64_t __spl_method_create_32bit(int64_t recv) { return recv; }
int64_t __spl_method_create_64bit(int64_t recv) { return recv; }
int64_t __spl_method_create_baremetal(int64_t recv) { return recv; }
int64_t __spl_method_create_for_target(int64_t recv, int64_t target) { (void)target; return recv; }
int64_t __spl_method_create_wasm(int64_t recv) { return recv; }
int64_t __spl_method_default(int64_t recv) { return recv; }
int64_t __spl_method_default_backend(int64_t recv) { return recv; }
int64_t __spl_method_description(int64_t recv) { return __spl_to_string(recv); }
int64_t __spl_method_emit_blank(int64_t recv) { return recv; }
int64_t __spl_method_emit_comment(int64_t recv, int64_t comment) { (void)comment; return recv; }
int64_t __spl_method_emit_library_header(int64_t recv) { return recv; }
int64_t __spl_method_emit_module_header(int64_t recv) { return recv; }
int64_t __spl_method_empty(int64_t recv) { (void)recv; return rt_array_new(0); }
int64_t __spl_method_end_namespace(int64_t recv) { return recv; }
int64_t __spl_method_entry(int64_t recv, int64_t key) { return rt_dict_get(recv, key); }
int64_t __spl_method__examples_push(int64_t recv, int64_t ex) { return rt_array_push(recv, ex); }
int64_t __spl_method_gpu_output(int64_t recv) { return recv; }
int64_t __spl_method_interpreted(int64_t recv) { return recv; }
int64_t __spl_method_lexer_mode(int64_t recv) { return recv; }
int64_t __spl_method_loss(int64_t recv) { return recv; }
int64_t __spl_method_lower_module(int64_t recv, int64_t mod) { (void)mod; return recv; }
int64_t __spl_method_math(int64_t recv) { return recv; }
int64_t __spl_method_merge(int64_t recv, int64_t other) { (void)other; return recv; }
int64_t __spl_method_message_contains(int64_t recv, int64_t sub) { return __spl_method_contains(recv, sub); }
int64_t __spl_method_new(int64_t recv) { return recv; }
int64_t __spl_method_nograd(int64_t recv) { return recv; }
int64_t __spl_method_object(int64_t recv) { return recv; }
int64_t __spl_method_operands_len(int64_t recv) { return rt_tuple_len(recv); }
int64_t __spl_method_parse(int64_t recv, int64_t src) { (void)src; return recv; }
int64_t __spl_method_ptr(int64_t recv) { return recv; }
int64_t __spl_method_registry_register(int64_t recv, int64_t item) { return rt_array_push(recv, item); }
int64_t __spl_method_registry_unregister(int64_t recv, int64_t item) { (void)item; return recv; }
int64_t __spl_method_stats_record_pass_run(int64_t recv, int64_t name) { (void)name; return recv; }
int64_t __spl_method_supports_target(int64_t recv, int64_t target) { (void)target; return 1; }
int64_t __spl_method_syntax_features(int64_t recv) { return recv; }
int64_t __spl_method_test(int64_t recv) { return recv; }
int64_t __spl_method_text_with_header(int64_t recv) { return __spl_to_string(recv); }
int64_t __spl_method_to_compiled_module(int64_t recv) { return recv; }
int64_t __spl_method_to_lean_spec(int64_t recv) { return recv; }
int64_t __spl_method_unit(int64_t recv) { (void)recv; return 0; }
int64_t __spl_method_validation(int64_t recv) { return recv; }
int64_t __spl_method_with_note(int64_t recv, int64_t note) { (void)note; return recv; }
int64_t __spl_method_with_optimization(int64_t recv, int64_t opt) { (void)opt; return recv; }
int64_t __spl_method_with_suggestion(int64_t recv, int64_t sug) { (void)sug; return recv; }
int64_t __spl_method_with_target(int64_t recv, int64_t target) { (void)target; return recv; }
int64_t __spl_method_actual_msg_contains(int64_t recv, int64_t sub) { return __spl_method_contains(recv, sub); }

/* ================================================================
 * main() entry point
 * ================================================================ */

/* Forward declarations of the compiled Simple functions */
int64_t simple_main(void);
int64_t __module_init(void);

/* Generated C provides its own main() storing argc/argv in __saved_argc/__saved_argv */
extern int __saved_argc;
extern char** __saved_argv;

/* sys_get_args — returns array of command-line args */
int64_t sys_get_args(void) {
    int64_t arr = rt_array_new(__saved_argc);
    for (int i = 0; i < __saved_argc; i++) {
        rt_array_push(arr, str_from_cstr(__saved_argv[i]));
    }
    return arr;
}
