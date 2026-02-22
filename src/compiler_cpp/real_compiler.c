#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#ifdef _MSC_VER
#define strdup _strdup
#endif

// === Simple Runtime Helpers ===
// Embedded in generated C code by shared MIR C backend (CCodegenAdapter)
// All functions are static to avoid link conflicts and allow dead code elimination.

// --- String Operations ---

static long long simple_strlen(const char* s) {
    if (!s) return 0;
    return (long long)strlen(s);
}

static char* simple_substring(const char* s, long long start, long long end) {
    if (!s) return strdup("");
    long long slen = (long long)strlen(s);
    if (start < 0) start = 0;
    if (end > slen) end = slen;
    if (start >= end) return strdup("");
    long long len = end - start;
    char* result = (char*)malloc(len + 1);
    memcpy(result, s + start, len);
    result[len] = '\0';
    return result;
}

static int simple_contains(const char* s, const char* needle) {
    if (!s || !needle) return 0;
    return strstr(s, needle) != NULL;
}

static int simple_starts_with(const char* s, const char* prefix) {
    if (!s || !prefix) return 0;
    return strncmp(s, prefix, strlen(prefix)) == 0;
}

static int simple_ends_with(const char* s, const char* suffix) {
    if (!s || !suffix) return 0;
    long long slen = strlen(s);
    long long suflen = strlen(suffix);
    if (suflen > slen) return 0;
    return strcmp(s + slen - suflen, suffix) == 0;
}

static char* simple_trim(const char* s) {
    if (!s) return strdup("");
    while (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r') s++;
    long long len = strlen(s);
    while (len > 0 && (s[len-1] == ' ' || s[len-1] == '\t' || s[len-1] == '\n' || s[len-1] == '\r')) len--;
    char* result = (char*)malloc(len + 1);
    memcpy(result, s, len);
    result[len] = '\0';
    return result;
}

static long long simple_index_of(const char* s, const char* needle) {
    if (!s || !needle) return -1;
    const char* found = strstr(s, needle);
    if (!found) return -1;
    return (long long)(found - s);
}

static long long simple_last_index_of(const char* s, const char* needle) {
    if (!s || !needle) return -1;
    long long needle_len = strlen(needle);
    long long slen = strlen(s);
    if (needle_len > slen) return -1;
    for (long long i = slen - needle_len; i >= 0; i--) {
        if (strncmp(s + i, needle, needle_len) == 0) {
            return i;
        }
    }
    return -1;
}

static char* simple_replace(const char* s, const char* old_str, const char* new_str) {
    if (!s) return strdup("");
    if (!old_str || !new_str || strlen(old_str) == 0) return strdup(s);
    long long old_len = strlen(old_str);
    long long new_len = strlen(new_str);
    // Count occurrences
    long long count = 0;
    const char* tmp = s;
    while ((tmp = strstr(tmp, old_str)) != NULL) { count++; tmp += old_len; }
    if (count == 0) return strdup(s);
    // Build result
    long long result_len = strlen(s) + count * (new_len - old_len);
    char* result = (char*)malloc(result_len + 1);
    char* dst = result;
    while (*s) {
        if (strncmp(s, old_str, old_len) == 0) {
            memcpy(dst, new_str, new_len);
            dst += new_len;
            s += old_len;
        } else {
            *dst++ = *s++;
        }
    }
    *dst = '\0';
    return result;
}

// --- Dynamic String Array ---

typedef struct {
    const char** items;
    long long len;
    long long cap;
} SimpleStringArray;

static SimpleStringArray simple_new_string_array(void) {
    SimpleStringArray arr;
    arr.items = (const char**)malloc(16 * sizeof(const char*));
    arr.len = 0;
    arr.cap = 16;
    return arr;
}

static void simple_string_push(SimpleStringArray* arr, const char* s) {
    if (arr->len >= arr->cap) {
        arr->cap *= 2;
        arr->items = (const char**)realloc(arr->items, arr->cap * sizeof(const char*));
    }
    arr->items[arr->len] = strdup(s ? s : "");
    arr->len++;
}

static const char* simple_string_pop(SimpleStringArray* arr) {
    if (arr->len == 0) return "";
    arr->len--;
    return arr->items[arr->len];
}

static int simple_str_array_contains(SimpleStringArray arr, const char* needle) {
    for (long long i = 0; i < arr.len; i++) {
        if (arr.items[i] && needle && strcmp(arr.items[i], needle) == 0) return 1;
    }
    return 0;
}

static char* simple_string_join(SimpleStringArray* arr, const char* delim) {
    if (arr->len == 0) return strdup("");
    long long delim_len = strlen(delim);
    long long total = 0;
    for (long long i = 0; i < arr->len; i++) {
        total += strlen(arr->items[i]);
        if (i < arr->len - 1) total += delim_len;
    }
    char* result = (char*)malloc(total + 1);
    char* dst = result;
    for (long long i = 0; i < arr->len; i++) {
        long long item_len = strlen(arr->items[i]);
        memcpy(dst, arr->items[i], item_len);
        dst += item_len;
        if (i < arr->len - 1) {
            memcpy(dst, delim, delim_len);
            dst += delim_len;
        }
    }
    *dst = '\0';
    return result;
}

static SimpleStringArray simple_split(const char* s, const char* delim) {
    SimpleStringArray arr = simple_new_string_array();
    if (!s) return arr;
    if (!delim || strlen(delim) == 0) {
        simple_string_push(&arr, s);
        return arr;
    }
    long long delim_len = strlen(delim);
    const char* start = s;
    const char* found;
    while ((found = strstr(start, delim)) != NULL) {
        long long len = found - start;
        char* part = (char*)malloc(len + 1);
        memcpy(part, start, len);
        part[len] = '\0';
        simple_string_push(&arr, part);
        free(part);
        start = found + delim_len;
    }
    simple_string_push(&arr, start);
    return arr;
}

// --- Dynamic Integer Array ---

typedef struct {
    long long* items;
    long long len;
    long long cap;
} SimpleIntArray;

static SimpleIntArray simple_new_int_array(void) {
    SimpleIntArray arr;
    arr.items = (long long*)malloc(16 * sizeof(long long));
    arr.len = 0;
    arr.cap = 16;
    return arr;
}

static void simple_int_push(SimpleIntArray* arr, long long val) {
    if (arr->len >= arr->cap) {
        arr->cap *= 2;
        arr->items = (long long*)realloc(arr->items, arr->cap * sizeof(long long));
    }
    arr->items[arr->len] = val;
    arr->len++;
}

static long long simple_int_pop(SimpleIntArray* arr) {
    if (arr->len == 0) return 0;
    arr->len--;
    return arr->items[arr->len];
}

// --- Array of String Arrays (for [[text]]) ---

typedef struct {
    SimpleStringArray* items;
    long long len;
    long long cap;
} SimpleStringArrayArray;

static SimpleStringArrayArray simple_new_string_array_array(void) {
    SimpleStringArrayArray arr;
    arr.items = (SimpleStringArray*)malloc(16 * sizeof(SimpleStringArray));
    arr.len = 0;
    arr.cap = 16;
    return arr;
}

static void simple_string_array_push(SimpleStringArrayArray* arr, SimpleStringArray val) {
    if (arr->len >= arr->cap) {
        arr->cap *= 2;
        arr->items = (SimpleStringArray*)realloc(arr->items, arr->cap * sizeof(SimpleStringArray));
    }
    arr->items[arr->len] = val;
    arr->len++;
}

// --- Array of Int Arrays (for [[i64]]) ---

typedef struct {
    SimpleIntArray* items;
    long long len;
    long long cap;
} SimpleIntArrayArray;

static SimpleIntArrayArray simple_new_int_array_array(void) {
    SimpleIntArrayArray arr;
    arr.items = (SimpleIntArray*)malloc(16 * sizeof(SimpleIntArray));
    arr.len = 0;
    arr.cap = 16;
    return arr;
}

static void simple_int_array_push(SimpleIntArrayArray* arr, SimpleIntArray val) {
    if (arr->len >= arr->cap) {
        arr->cap *= 2;
        arr->items = (SimpleIntArray*)realloc(arr->items, arr->cap * sizeof(SimpleIntArray));
    }
    arr->items[arr->len] = val;
    arr->len++;
}

// --- Dynamic Struct Array (void* based, for [StructName] types) ---

typedef struct {
    void** items;
    long long len;
    long long cap;
} SimpleStructArray;

static SimpleStructArray simple_new_struct_array(void) {
    SimpleStructArray arr;
    arr.items = NULL;
    arr.len = 0;
    arr.cap = 0;
    return arr;
}

static void simple_struct_push(SimpleStructArray* arr, void* item) {
    if (arr->len >= arr->cap) {
        arr->cap = arr->cap == 0 ? 8 : arr->cap * 2;
        arr->items = (void**)realloc(arr->items, arr->cap * sizeof(void*));
    }
    arr->items[arr->len++] = item;
}

static SimpleStructArray simple_struct_array_copy_push(SimpleStructArray src, void* item) {
    SimpleStructArray dst;
    dst.cap = src.len + 1;
    if (dst.cap < 8) dst.cap = 8;
    dst.items = (void**)malloc(dst.cap * sizeof(void*));
    for (long long i = 0; i < src.len; i++) {
        dst.items[i] = src.items[i];
    }
    dst.len = src.len;
    dst.items[dst.len++] = item;
    return dst;
}

static SimpleIntArray simple_int_array_copy_push(SimpleIntArray src, long long item) {
    SimpleIntArray dst;
    dst.cap = src.len + 1;
    if (dst.cap < 8) dst.cap = 8;
    dst.items = (long long*)malloc(dst.cap * sizeof(long long));
    memcpy(dst.items, src.items, src.len * sizeof(long long));
    dst.len = src.len;
    dst.items[dst.len++] = item;
    return dst;
}

static SimpleStringArray simple_string_array_copy_push(SimpleStringArray src, const char* item) {
    SimpleStringArray dst;
    dst.cap = src.len + 1;
    if (dst.cap < 8) dst.cap = 8;
    dst.items = (const char**)malloc(dst.cap * sizeof(const char*));
    for (long long i = 0; i < src.len; i++) {
        dst.items[i] = src.items[i];
    }
    dst.len = src.len;
    dst.items[dst.len++] = strdup(item ? item : "");
    return dst;
}

// --- String Helpers ---

static char* simple_str_concat(const char* a, const char* b) {
    if (!a) a = "";
    if (!b) b = "";
    long long alen = strlen(a);
    long long blen = strlen(b);
    char* result = (char*)malloc(alen + blen + 1);
    memcpy(result, a, alen);
    memcpy(result + alen, b, blen);
    result[alen + blen] = '\0';
    return result;
}

static char* simple_char_at(const char* s, long long idx) {
    if (!s) return strdup("");
    long long slen = strlen(s);
    if (idx < 0) idx = slen + idx;
    if (idx < 0 || idx >= slen) return strdup("");
    char result[2];
    result[0] = s[idx];
    result[1] = '\0';
    return strdup(result);
}

// --- File I/O ---

static char* simple_file_read(const char* path) {
    FILE* f = fopen(path, "r");
    if (!f) return strdup("");
    fseek(f, 0, SEEK_END);
    long long len = ftell(f);
    fseek(f, 0, SEEK_SET);
    char* buf = (char*)malloc(len + 1);
    long long read_len = fread(buf, 1, len, f);
    buf[read_len] = '\0';
    fclose(f);
    return buf;
}

static int simple_file_write(const char* path, const char* content) {
    FILE* f = fopen(path, "w");
    if (!f) return 0;
    fputs(content ? content : "", f);
    fclose(f);
    return 1;
}

static int simple_file_exists(const char* path) {
    FILE* f = fopen(path, "r");
    if (f) { fclose(f); return 1; }
    return 0;
}

// --- Process ---

static long long simple_shell(const char* cmd) {
    return (long long)system(cmd);
}

// --- String formatting helper (sprintf wrapper) ---

static char* simple_format_long(const char* fmt_before, long long value, const char* fmt_after) {
    char buf[256];
    snprintf(buf, sizeof(buf), "%s%lld%s", fmt_before ? fmt_before : "", value, fmt_after ? fmt_after : "");
    return strdup(buf);
}

static char* simple_format_str(const char* fmt_before, const char* value, const char* fmt_after) {
    long long total = strlen(fmt_before ? fmt_before : "") + strlen(value ? value : "") + strlen(fmt_after ? fmt_after : "") + 1;
    char* buf = (char*)malloc(total);
    snprintf(buf, total, "%s%s%s", fmt_before ? fmt_before : "", value ? value : "", fmt_after ? fmt_after : "");
    return buf;
}

// --- Int to String helper ---

static char* simple_int_to_str(long long value) {
    static char buf[32];
    snprintf(buf, sizeof(buf), "%lld", value);
    return buf;
}

// --- Dictionary (linear-scan hash table with string keys) ---

#define SIMPLE_DICT_INIT_CAP 32
#define SIMPLE_DICT_TYPE_INT 0
#define SIMPLE_DICT_TYPE_STR 1
#define SIMPLE_DICT_TYPE_PTR 2

typedef struct {
    const char* key;
    int type_tag;
    union {
        long long int_val;
        const char* str_val;
        void* ptr_val;
    } value;
} SimpleDictEntry;

typedef struct {
    SimpleDictEntry* entries;
    long long len;
    long long cap;
} SimpleDict;

static SimpleDict* simple_dict_new(void) {
    SimpleDict* d = (SimpleDict*)malloc(sizeof(SimpleDict));
    d->entries = (SimpleDictEntry*)calloc(SIMPLE_DICT_INIT_CAP, sizeof(SimpleDictEntry));
    d->len = 0;
    d->cap = SIMPLE_DICT_INIT_CAP;
    return d;
}

static long long simple_dict_find(SimpleDict* d, const char* key) {
    if (!d || !key) return -1;
    for (long long i = 0; i < d->len; i++) {
        if (d->entries[i].key && strcmp(d->entries[i].key, key) == 0) {
            return i;
        }
    }
    return -1;
}

static void simple_dict_set_int(SimpleDict* d, const char* key, long long value) {
    if (!d || !key) return;
    long long idx = simple_dict_find(d, key);
    if (idx >= 0) {
        d->entries[idx].type_tag = SIMPLE_DICT_TYPE_INT;
        d->entries[idx].value.int_val = value;
        return;
    }
    if (d->len >= d->cap) {
        d->cap *= 2;
        d->entries = (SimpleDictEntry*)realloc(d->entries, d->cap * sizeof(SimpleDictEntry));
    }
    d->entries[d->len].key = strdup(key);
    d->entries[d->len].type_tag = SIMPLE_DICT_TYPE_INT;
    d->entries[d->len].value.int_val = value;
    d->len++;
}

static void simple_dict_set_str(SimpleDict* d, const char* key, const char* value) {
    if (!d || !key) return;
    long long idx = simple_dict_find(d, key);
    if (idx >= 0) {
        d->entries[idx].type_tag = SIMPLE_DICT_TYPE_STR;
        d->entries[idx].value.str_val = value ? strdup(value) : strdup("");
        return;
    }
    if (d->len >= d->cap) {
        d->cap *= 2;
        d->entries = (SimpleDictEntry*)realloc(d->entries, d->cap * sizeof(SimpleDictEntry));
    }
    d->entries[d->len].key = strdup(key);
    d->entries[d->len].type_tag = SIMPLE_DICT_TYPE_STR;
    d->entries[d->len].value.str_val = value ? strdup(value) : strdup("");
    d->len++;
}

static void simple_dict_set_ptr(SimpleDict* d, const char* key, void* value) {
    if (!d || !key) return;
    long long idx = simple_dict_find(d, key);
    if (idx >= 0) {
        d->entries[idx].type_tag = SIMPLE_DICT_TYPE_PTR;
        d->entries[idx].value.ptr_val = value;
        return;
    }
    if (d->len >= d->cap) {
        d->cap *= 2;
        d->entries = (SimpleDictEntry*)realloc(d->entries, d->cap * sizeof(SimpleDictEntry));
    }
    d->entries[d->len].key = strdup(key);
    d->entries[d->len].type_tag = SIMPLE_DICT_TYPE_PTR;
    d->entries[d->len].value.ptr_val = value;
    d->len++;
}

static const char* simple_dict_get(SimpleDict* d, const char* key) {
    if (!d || !key) return NULL;
    long long idx = simple_dict_find(d, key);
    if (idx < 0) return NULL;
    if (d->entries[idx].type_tag == SIMPLE_DICT_TYPE_STR) {
        return d->entries[idx].value.str_val;
    }
    // For int values, convert to string
    if (d->entries[idx].type_tag == SIMPLE_DICT_TYPE_INT) {
        return simple_int_to_str(d->entries[idx].value.int_val);
    }
    return NULL;
}

static long long simple_dict_get_int(SimpleDict* d, const char* key) {
    if (!d || !key) return 0;
    long long idx = simple_dict_find(d, key);
    if (idx < 0) return 0;
    return d->entries[idx].value.int_val;
}

static void* simple_dict_get_ptr(SimpleDict* d, const char* key) {
    if (!d || !key) return NULL;
    long long idx = simple_dict_find(d, key);
    if (idx < 0) return NULL;
    return d->entries[idx].value.ptr_val;
}

static int simple_dict_contains(SimpleDict* d, const char* key) {
    return simple_dict_find(d, key) >= 0;
}

static long long simple_dict_len(SimpleDict* d) {
    if (!d) return 0;
    return d->len;
}

static SimpleStringArray simple_dict_keys(SimpleDict* d) {
    SimpleStringArray arr = simple_new_string_array();
    if (!d) return arr;
    for (long long i = 0; i < d->len; i++) {
        if (d->entries[i].key) {
            simple_string_push(&arr, d->entries[i].key);
        }
    }
    return arr;
}

static void simple_dict_remove(SimpleDict* d, const char* key) {
    if (!d || !key) return;
    long long idx = simple_dict_find(d, key);
    if (idx < 0) return;
    // Shift entries down
    for (long long i = idx; i < d->len - 1; i++) {
        d->entries[i] = d->entries[i + 1];
    }
    d->len--;
}

// --- Option Type ---

typedef struct {
    int has_value;
    int type_tag; // 0=int, 1=str, 2=ptr
    union {
        long long int_val;
        const char* str_val;
        void* ptr_val;
    };
} SimpleOption;

static SimpleOption simple_none(void) {
    SimpleOption o;
    o.has_value = 0;
    o.type_tag = 0;
    o.int_val = 0;
    return o;
}

static SimpleOption simple_some_int(long long val) {
    SimpleOption o;
    o.has_value = 1;
    o.type_tag = 0;
    o.int_val = val;
    return o;
}

static SimpleOption simple_some_str(const char* val) {
    SimpleOption o;
    o.has_value = 1;
    o.type_tag = 1;
    o.str_val = val ? val : "";
    return o;
}

static SimpleOption simple_some_ptr(void* val) {
    SimpleOption o;
    o.has_value = 1;
    o.type_tag = 2;
    o.ptr_val = val;
    return o;
}

static int simple_option_has(SimpleOption o) {
    return o.has_value;
}

static long long simple_option_unwrap_int(SimpleOption o) {
    return o.int_val;
}

static const char* simple_option_unwrap_str(SimpleOption o) {
    if (o.has_value && o.type_tag == 1) return o.str_val;
    return "";
}

static void* simple_option_unwrap_ptr(SimpleOption o) {
    if (o.has_value && o.type_tag == 2) return o.ptr_val;
    return NULL;
}

// --- Result Type ---

typedef struct {
    int is_ok;
    int type_tag; // 0=int, 1=str, 2=ptr
    union {
        long long ok_int;
        const char* ok_str;
        void* ok_ptr;
    };
    union {
        long long err_int;
        const char* err_str;
        void* err_ptr;
    };
} SimpleResult;

static SimpleResult simple_result_ok_int(long long val) {
    SimpleResult r;
    r.is_ok = 1;
    r.type_tag = 0;
    r.ok_int = val;
    r.err_int = 0;
    return r;
}

static SimpleResult simple_result_ok_str(const char* val) {
    SimpleResult r;
    r.is_ok = 1;
    r.type_tag = 1;
    r.ok_str = val ? val : "";
    r.err_str = NULL;
    return r;
}

static SimpleResult simple_result_err_str(const char* val) {
    SimpleResult r;
    r.is_ok = 0;
    r.type_tag = 1;
    r.ok_str = NULL;
    r.err_str = val ? val : "";
    return r;
}

// --- Tuple Types ---

typedef struct {
    void* _0;
    void* _1;
} SimpleTuple2;

typedef struct {
    void* _0;
    void* _1;
    void* _2;
} SimpleTuple3;

// === End Simple Runtime Helpers ===


// --- Forward Declarations ---

// === Runtime Function Implementations ===
// Self-contained: no external runtime dependency

#include <dirent.h>

const char* rt_file_read_text(const char* path) {
    if (!path) return NULL;
    FILE* f = fopen(path, "r");
    if (!f) return NULL;
    fseek(f, 0, SEEK_END);
    long sz = ftell(f);
    fseek(f, 0, SEEK_SET);
    char* buf = (char*)malloc(sz + 1);
    size_t nread = fread(buf, 1, sz, f);
    buf[nread] = 0;
    fclose(f);
    return buf;
}

int rt_file_write_text(const char* path, const char* content) {
    if (!path) return 0;
    FILE* f = fopen(path, "w");
    if (!f) return 0;
    if (content) fputs(content, f);
    fclose(f);
    return 1;
}

long long rt_process_run(const char* cmd) {
    if (!cmd) return -1;
    return (long long)system(cmd);
}

// Capture argc/argv via /proc/self/cmdline (Linux)
static int _shim_argc = 0;
static char** _shim_argv = NULL;

__attribute__((constructor))
static void _shim_capture_args(void) {
    FILE* f = fopen("/proc/self/cmdline", "r");
    if (!f) return;
    char buf[65536];
    size_t n = fread(buf, 1, sizeof(buf) - 1, f);
    fclose(f);
    buf[n] = 0;
    int count = 0;
    for (size_t i = 0; i < n; i++) {
        if (buf[i] == 0) count++;
    }
    _shim_argc = count;
    _shim_argv = (char**)malloc(count * sizeof(char*));
    size_t pos = 0;
    for (int i = 0; i < count; i++) {
        _shim_argv[i] = strdup(buf + pos);
        pos += strlen(buf + pos) + 1;
    }
}

SimpleStringArray rt_cli_get_args(void) {
    SimpleStringArray arr;
    arr.items = (const char**)malloc((_shim_argc + 1) * sizeof(const char*));
    arr.len = _shim_argc;
    arr.cap = _shim_argc + 1;
    for (int i = 0; i < _shim_argc; i++) {
        arr.items[i] = _shim_argv[i];
    }
    return arr;
}

const char* trim(const char* s);
int starts_with(const char* s, const char* prefix);
int ends_with(const char* s, const char* suffix);
int contains(const char* s, const char* needle);
long long str_len(const char* s);
const char* substr(const char* s, long long start, long long end);
const char* substr_from(const char* s, long long start);
long long find_str(const char* s, const char* needle);
const char* replace_str(const char* s, const char* old, const char* new_val);
int is_digit(const char* ch);
int is_alpha(const char* ch);
int is_alnum(const char* ch);
SimpleStringArray parse_fn_sig(const char* line);
const char* translate_print(const char* line);
const char* translate_expr(const char* expr);
const char* translate_var_decl(const char* line);
const char* translate_return(const char* line);
const char* generate_c(const char* source);

const char* trim(const char* s) {
    return simple_trim(s);
}

int starts_with(const char* s, const char* prefix) {
    return simple_starts_with(s, prefix);
}

int ends_with(const char* s, const char* suffix) {
    return simple_ends_with(s, suffix);
}

int contains(const char* s, const char* needle) {
    return simple_contains(s, needle);
}

long long str_len(const char* s) {
    return simple_strlen(s);
}

const char* substr(const char* s, long long start, long long end) {
    return simple_substring(s, start, end);
}

const char* substr_from(const char* s, long long start) {
    return simple_substring(s, start, simple_strlen(s));
}

long long find_str(const char* s, const char* needle) {
    return simple_index_of(s, needle);
}

const char* replace_str(const char* s, const char* old, const char* new_val) {
    return simple_replace(s, old, new_val);
}

int is_digit(const char* ch) {
    if (!ch || !*ch) return 0;
    return (ch[0] >= '0' && ch[0] <= '9') ? 1 : 0;
}

int is_alpha(const char* ch) {
    if (!ch || !*ch) return 0;
    if (ch[0] >= 'a' && ch[0] <= 'z') return 1;
    if (ch[0] >= 'A' && ch[0] <= 'Z') return 1;
    if (ch[0] == '_') return 1;
    return 0;
}

int is_alnum(const char* ch) {
    if (is_digit(ch)) return 1;
    return is_alpha(ch);
}

/* Convert a Simple type string to the corresponding C type */
static const char* stype_to_c(const char* stype) {
    if (!stype || !*stype) return "long long";
    long long len = (long long)strlen(stype);
    /* Strip trailing ? (optional type) */
    if (len > 0 && stype[len-1] == '?') {
        char* stripped = (char*)malloc(len);
        memcpy(stripped, stype, len-1);
        stripped[len-1] = '\0';
        const char* res = stype_to_c(stripped);
        free(stripped);
        return res;
    }
    /* Primitive types */
    if (strcmp(stype, "i64") == 0 || strcmp(stype, "int") == 0 || strcmp(stype, "Int") == 0) return "long long";
    if (strcmp(stype, "i32") == 0) return "int";
    if (strcmp(stype, "i8") == 0 || strcmp(stype, "u8") == 0) return "int";
    if (strcmp(stype, "f64") == 0 || strcmp(stype, "float") == 0 || strcmp(stype, "Float") == 0) return "double";
    if (strcmp(stype, "f32") == 0) return "float";
    if (strcmp(stype, "bool") == 0 || strcmp(stype, "Bool") == 0) return "int";
    if (strcmp(stype, "void") == 0) return "void";
    if (strcmp(stype, "text") == 0 || strcmp(stype, "str") == 0 || strcmp(stype, "String") == 0) return "const char*";
    /* Array types */
    if (strcmp(stype, "[text]") == 0 || strcmp(stype, "[str]") == 0) return "SimpleStringArray";
    if (strcmp(stype, "[i64]") == 0 || strcmp(stype, "[int]") == 0 || strcmp(stype, "[bool]") == 0) return "SimpleIntArray";
    if (strcmp(stype, "[[text]]") == 0 || strcmp(stype, "[[str]]") == 0) return "SimpleStringArrayArray";
    if (strcmp(stype, "[[i64]]") == 0 || strcmp(stype, "[[int]]") == 0) return "SimpleIntArrayArray";
    /* [StructName] → SimpleStructArray */
    if (len > 2 && stype[0] == '[' && stype[len-1] == ']') {
        if (stype[1] >= 'A' && stype[1] <= 'Z') return "SimpleStructArray";
    }
    /* Generic types with <> (Option<T>, Result<T,E>, Dict<K,V>, etc.) → long long */
    if (strstr(stype, "<") != NULL) return "long long";
    /* Bare struct/class name (uppercase first char) → use as-is */
    if (stype[0] >= 'A' && stype[0] <= 'Z') return stype;
    return "long long";
}

/* Split param string by comma, skipping commas inside <> brackets */
static SimpleStringArray split_params_toplevel(const char* s) {
    SimpleStringArray result = simple_new_string_array();
    if (!s) return result;
    long long len = (long long)strlen(s);
    long long start = 0;
    int depth = 0;
    for (long long i = 0; i <= len; i++) {
        char c = (i < len) ? s[i] : '\0';
        if (c == '<') { depth++; continue; }
        if (c == '>') { depth--; continue; }
        if (c == '\0' || (c == ',' && depth == 0)) {
            long long plen = i - start;
            char* part = (char*)malloc(plen + 1);
            memcpy(part, s + start, plen);
            part[plen] = '\0';
            simple_string_push(&result, simple_trim(part));
            free(part);
            start = i + 1;
        }
    }
    return result;
}

/* Find the matching close paren, tracking nested () and <> */
static long long find_close_paren_from(const char* line, long long open_pos) {
    long long len = (long long)strlen(line);
    int depth = 1;
    int angle = 0;
    for (long long i = open_pos + 1; i < len; i++) {
        char c = line[i];
        if (c == '<') { angle++; continue; }
        if (c == '>') { angle--; continue; }
        if (angle > 0) continue;
        if (c == '(') depth++;
        else if (c == ')') {
            depth--;
            if (depth == 0) return i;
        }
    }
    return -1;
}

/* Mangle names that conflict with C keywords or stdlib */
static const char* mangle_name(const char* name) {
    if (!name || !*name) return name;
    if (strcmp(name, "exit") == 0) return "simple_exit";
    if (strcmp(name, "error") == 0) return "simple_error";
    if (strcmp(name, "default") == 0) return "default_";
    if (strcmp(name, "short") == 0) return "short_";
    if (strcmp(name, "long") == 0) return "long_";
    if (strcmp(name, "int") == 0) return "int_";
    if (strcmp(name, "float") == 0) return "float_";
    if (strcmp(name, "double") == 0) return "double_";
    if (strcmp(name, "char") == 0) return "char_";
    if (strcmp(name, "void") == 0) return "void_";
    if (strcmp(name, "auto") == 0) return "auto_";
    if (strcmp(name, "register") == 0) return "register_";
    if (strcmp(name, "volatile") == 0) return "volatile_";
    if (strcmp(name, "extern") == 0) return "extern_";
    if (strcmp(name, "static") == 0) return "static_";
    if (strcmp(name, "const") == 0) return "const_";
    if (strcmp(name, "signed") == 0) return "signed_";
    if (strcmp(name, "unsigned") == 0) return "unsigned_";
    if (strcmp(name, "union") == 0) return "union_";
    if (strcmp(name, "enum") == 0) return "enum_";
    if (strcmp(name, "typedef") == 0) return "typedef_";
    if (strcmp(name, "sizeof") == 0) return "sizeof_";
    if (strcmp(name, "switch") == 0) return "switch_";
    if (strcmp(name, "case") == 0) return "case_";
    if (strcmp(name, "goto") == 0) return "goto_";
    if (strcmp(name, "inline") == 0) return "inline_";
    if (strcmp(name, "restrict") == 0) return "restrict_";
    if (strcmp(name, "bool") == 0) return "bool_";
    if (strcmp(name, "true") == 0) return "true_";
    if (strcmp(name, "false") == 0) return "false_";
    if (strcmp(name, "text") == 0) return "text_";
    return name;
}

SimpleStringArray parse_fn_sig(const char* line) {
    SimpleStringArray result = simple_new_string_array();
    long long fn_start = find_str(line, "fn ") + 3;
    long long paren = find_str(line, "(");
    if (paren < 0) {
        simple_string_push(&result, "unknown");
        simple_string_push(&result, "void unknown(void)");
        simple_string_push(&result, "void unknown(void);");
        return result;
    }
    const char* name = mangle_name(trim(substr(line, fn_start, paren)));
    long long arrow = find_str(line, " -> ");
    const char* ret_type = "long long";
    if (arrow >= 0) {
        const char* ret_raw = trim(substr(line, arrow + 4, str_len(line) - 1));
        ret_type = stype_to_c(ret_raw);
    } else {
        /* No return type → void */
        ret_type = "void";
    }
    long long close = find_close_paren_from(line, paren);
    if (close < 0) close = find_str(line, ")");
    const char* c_params = "void";
    if (close > paren + 1) {
        const char* raw_params = trim(substr(line, paren + 1, close));
        SimpleStringArray params_out = simple_new_string_array();
        SimpleStringArray parts = split_params_toplevel(raw_params);
        for (long long _idx_p = 0; _idx_p < parts.len; _idx_p++) { const char* p = parts.items[_idx_p];
            const char* pt = trim(p);
            if (!pt || !*pt) continue;
            /* Skip ~keyword-only marker */
            if (pt[0] == '~') pt = trim(substr_from(pt, 1));
            long long colon = find_str(pt, ":");
            if (colon >= 0) {
                const char* pname = mangle_name(trim(substr(pt, 0, colon)));
                const char* ptype = trim(substr_from(pt, colon + 1));
                const char* ctype = stype_to_c(ptype);
                simple_string_push(&params_out, simple_str_concat(ctype, simple_str_concat(" ", pname)));
            } else {
                simple_string_push(&params_out, simple_str_concat("long long ", mangle_name(pt)));
            }
        }
        c_params = simple_string_join(&params_out, ", ");
    }
    const char* sig = simple_str_concat(ret_type, simple_str_concat(" ", simple_str_concat(name, simple_str_concat("(", simple_str_concat(c_params, ")")))));
    simple_string_push(&result, name);
    simple_string_push(&result, sig);
    simple_string_push(&result, simple_str_concat(sig, ";"));
    return result;
}

const char* translate_print(const char* line) {
    const char* rest = trim(substr_from(line, 6));
    if (starts_with(rest, "\"") && ends_with(rest, "\"")) {
        const char* inner = substr(rest, 1, str_len(rest) - 1);
        if (contains(inner, "{")) {
            // String interpolation: build printf with %s for string vars, %lld for ints
            const char* fmt = "";
            const char* args_str = "";
            long long i = 0;
            long long ilen = str_len(inner);
            while (i < ilen) {
                const char* ch = substr(inner, i, i + 1);
                if (strcmp(ch, "{") == 0) {
                    long long end_brace = i + 1;
                    while (end_brace < ilen) {
                        if (strcmp(substr(inner, end_brace, end_brace + 1), "}") == 0) {
                            break;
                        }
                        end_brace = end_brace + 1;
                    }
                    const char* var_expr = substr(inner, i + 1, end_brace);
                    // Use %s for all interpolated values (convert to string at runtime)
                    fmt = simple_str_concat(fmt, "%s");
                    // For field access like flags.backend, pass directly as string
                    args_str = simple_str_concat(args_str, simple_str_concat(", ", translate_expr(var_expr)));
                    i = end_brace + 1;
                } else if (strcmp(ch, "%") == 0) {
                    // Escape % in printf format
                    fmt = simple_str_concat(fmt, "%%");
                    i = i + 1;
                } else {
                    fmt = simple_str_concat(fmt, ch);
                    i = i + 1;
                }
            }
            return simple_str_concat("printf(\"", simple_str_concat(fmt, simple_str_concat("\\n\"", simple_str_concat(args_str, ");"))));
        }
        return simple_str_concat("printf(\"%s\\n\", ", simple_str_concat(rest, ");"));
    }
    // Variable or expression
    return simple_str_concat("printf(\"%lld\\n\", (long long)(", simple_str_concat(rest, "));"));
}

// --- Helper: check if expression looks like a string type ---
static int expr_is_string(const char* expr) {
    if (starts_with(expr, "\"")) return 1;
    // Known string-returning functions/patterns
    if (contains(expr, "env_get(")) return 1;
    if (contains(expr, "get_version(")) return 1;
    if (contains(expr, "get_cli_args(")) return 1;
    if (contains(expr, "read_sdn_run_config(")) return 1;
    if (contains(expr, "simple_str_concat(")) return 1;
    if (contains(expr, "simple_substring(")) return 1;
    if (contains(expr, "simple_format_")) return 1;
    return 0;
}

const char* translate_expr(const char* expr) {
    const char* e = trim(expr);
    if (str_len(e) == 0) return e;

    if (strcmp(e, "true") == 0) return "1";
    if (strcmp(e, "false") == 0) return "0";
    if (strcmp(e, "nil") == 0) return "NULL";
    if (strcmp(e, "pass_do_nothing") == 0 || strcmp(e, "pass_dn") == 0 ||
        strcmp(e, "pass_todo") == 0 || strcmp(e, "pass") == 0) return "((void)0)";
    if (strcmp(e, "self") == 0) return "self";  /* will be handled by struct context */
    if (starts_with(e, "\"")) return e;

    /* Strip numeric separators: 1_000_000 → 1000000 */
    if (is_digit(e) || (str_len(e) > 2 && e[0] == '0' && (e[1] == 'x' || e[1] == 'X' || e[1] == 'b' || e[1] == 'B' || e[1] == 'o' || e[1] == 'O'))) {
        if (simple_contains(e, "_")) {
            e = simple_replace(e, "_", "");
        }
    }

    // Parenthesized expression
    if (starts_with(e, "(") && ends_with(e, ")")) {
        const char* inner = trim(substr(e, 1, str_len(e) - 1));
        return simple_str_concat("(", simple_str_concat(translate_expr(inner), ")"));
    }

    // not X → !(X)
    if (starts_with(e, "not ")) {
        const char* rest = trim(substr_from(e, 4));
        return simple_str_concat("!(", simple_str_concat(translate_expr(rest), ")"));
    }

    // "and" / "or" — find the LAST occurrence to handle left-associativity
    // Null coalescing: x ?? default → ((x) != NULL ? (x) : (default))
    {
        long long qq_pos = find_str(e, " ?? ");
        if (qq_pos >= 0) {
            const char* left = trim(substr(e, 0, qq_pos));
            const char* right = trim(substr_from(e, qq_pos + 4));
            const char* tl = translate_expr(left);
            const char* tr = translate_expr(right);
            return simple_str_concat("((", simple_str_concat(tl, simple_str_concat(") ? (", simple_str_concat(tl, simple_str_concat(") : (", simple_str_concat(tr, "))"))))));
        }
    }
    // Split on " and " / " or " (lowest precedence first: or, then and)
    {
        // Find last " or "
        long long last_or = -1;
        long long search_from = 0;
        while (1) {
            long long pos = find_str(substr_from(e, search_from), " or ");
            if (pos < 0) break;
            last_or = search_from + pos;
            search_from = last_or + 4;
        }
        if (last_or >= 0) {
            const char* left = trim(substr(e, 0, last_or));
            const char* right = trim(substr_from(e, last_or + 4));
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" || ", simple_str_concat(translate_expr(right), ")"))));
        }
    }
    {
        // Find last " and "
        long long last_and = -1;
        long long search_from = 0;
        while (1) {
            long long pos = find_str(substr_from(e, search_from), " and ");
            if (pos < 0) break;
            last_and = search_from + pos;
            search_from = last_and + 5;
        }
        if (last_and >= 0) {
            const char* left = trim(substr(e, 0, last_and));
            const char* right = trim(substr_from(e, last_and + 5));
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" && ", simple_str_concat(translate_expr(right), ")"))));
        }
    }

    // String equality: x == "str" → strcmp(x, "str") == 0
    {
        long long eq_pos = find_str(e, " == ");
        if (eq_pos >= 0) {
            const char* left = trim(substr(e, 0, eq_pos));
            const char* right = trim(substr_from(e, eq_pos + 4));
            if (starts_with(right, "\"") || starts_with(left, "\"") ||
                strcmp(right, "NULL") == 0 || strcmp(right, "nil") == 0) {
                const char* tl = translate_expr(left);
                const char* tr = translate_expr(right);
                if (strcmp(tr, "NULL") == 0) {
                    return simple_str_concat("(", simple_str_concat(tl, " == NULL)"));
                }
                return simple_str_concat("(strcmp(", simple_str_concat(tl,
                    simple_str_concat(", ", simple_str_concat(tr, ") == 0)"))));
            }
            // Numeric comparison
            const char* tl = translate_expr(left);
            const char* tr = translate_expr(right);
            return simple_str_concat("(", simple_str_concat(tl,
                simple_str_concat(" == ", simple_str_concat(tr, ")"))));
        }
    }
    {
        long long neq_pos = find_str(e, " != ");
        if (neq_pos >= 0) {
            const char* left = trim(substr(e, 0, neq_pos));
            const char* right = trim(substr_from(e, neq_pos + 4));
            if (starts_with(right, "\"") || starts_with(left, "\"") ||
                strcmp(right, "NULL") == 0 || strcmp(right, "nil") == 0) {
                const char* tl = translate_expr(left);
                const char* tr = translate_expr(right);
                if (strcmp(tr, "NULL") == 0) {
                    return simple_str_concat("(", simple_str_concat(tl, " != NULL)"));
                }
                return simple_str_concat("(strcmp(", simple_str_concat(tl,
                    simple_str_concat(", ", simple_str_concat(tr, ") != 0)"))));
            }
            const char* tl = translate_expr(left);
            const char* tr = translate_expr(right);
            return simple_str_concat("(", simple_str_concat(tl,
                simple_str_concat(" != ", simple_str_concat(tr, ")"))));
        }
    }

    // Comparison operators: < > <= >=
    {
        long long pos = find_str(e, " < ");
        if (pos >= 0) {
            const char* left = trim(substr(e, 0, pos));
            const char* right = trim(substr_from(e, pos + 3));
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" < ", simple_str_concat(translate_expr(right), ")"))));
        }
    }
    {
        long long pos = find_str(e, " > ");
        if (pos >= 0) {
            const char* left = trim(substr(e, 0, pos));
            const char* right = trim(substr_from(e, pos + 3));
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" > ", simple_str_concat(translate_expr(right), ")"))));
        }
    }
    {
        long long pos = find_str(e, " <= ");
        if (pos >= 0) {
            const char* left = trim(substr(e, 0, pos));
            const char* right = trim(substr_from(e, pos + 4));
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" <= ", simple_str_concat(translate_expr(right), ")"))));
        }
    }
    {
        long long pos = find_str(e, " >= ");
        if (pos >= 0) {
            const char* left = trim(substr(e, 0, pos));
            const char* right = trim(substr_from(e, pos + 4));
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" >= ", simple_str_concat(translate_expr(right), ")"))));
        }
    }

    // Method calls: obj.method(args) — only if dot appears before any open paren
    {
        long long dot = find_str(e, ".");
        long long first_paren = find_str(e, "(");
        // Only handle as method/field if dot is before any paren (or no paren at all)
        if (dot >= 0 && (first_paren < 0 || dot < first_paren)) {
            const char* obj = trim(substr(e, 0, dot));
            const char* method_part = substr_from(e, dot + 1);

            // .len() → simple_strlen(obj) for strings, arr.len for arrays
            if (strcmp(method_part, "len()") == 0) {
                const char* tobj = translate_expr(obj);
                /* Heuristic: array-like names use .len */
                if (contains(obj, "args") || contains(obj, "parts") || contains(obj, "lines") ||
                    contains(obj, "items") || contains(obj, "files") || contains(obj, "list")) {
                    return simple_str_concat(tobj, ".len");
                }
                /* Heuristic: if obj looks like string, use simple_strlen */
                if (expr_is_string(obj) || starts_with(obj, "\"") ||
                    contains(obj, "name") || contains(obj, "path") || contains(obj, "text") ||
                    contains(obj, "line") || contains(obj, "msg") || contains(obj, "str") ||
                    contains(obj, "cmd") || contains(obj, "output") || contains(obj, "content") ||
                    contains(obj, "source") || contains(obj, "code") || contains(obj, "file") ||
                    contains(obj, "key") || contains(obj, "value") || contains(obj, "result") ||
                    contains(obj, "desc") || contains(obj, "prefix") || contains(obj, "suffix") ||
                    contains(obj, "input") || contains(obj, "version") || contains(obj, "url") ||
                    contains(obj, "label") || contains(obj, "title") || contains(obj, "format") ||
                    contains(obj, "simple_") || contains(obj, "trim") || contains(obj, "replace")) {
                    return simple_str_concat("simple_strlen(", simple_str_concat(tobj, ")"));
                }
                return simple_str_concat(tobj, ".len");
            }
            // .trim() → simple_trim(obj)
            if (strcmp(method_part, "trim()") == 0) {
                return simple_str_concat("simple_trim(", simple_str_concat(translate_expr(obj), ")"));
            }
            // .split("x") → simple_split(obj, "x")
            if (starts_with(method_part, "split(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 6, str_len(method_part) - 1);
                return simple_str_concat("simple_split(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .index_of("x") → simple_index_of(obj, "x")
            if (starts_with(method_part, "index_of(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 9, str_len(method_part) - 1);
                return simple_str_concat("simple_index_of(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .last_index_of("x") → simple_last_index_of(obj, "x")
            if (starts_with(method_part, "last_index_of(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 14, str_len(method_part) - 1);
                return simple_str_concat("simple_last_index_of(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .substring(a, b) → simple_substring(obj, a, b)
            if (starts_with(method_part, "substring(") && ends_with(method_part, ")")) {
                const char* args_str = substr(method_part, 10, str_len(method_part) - 1);
                return simple_str_concat("simple_substring(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(args_str, ")"))));
            }
            // .join("x") → simple_string_join(&obj, "x")
            if (starts_with(method_part, "join(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 5, str_len(method_part) - 1);
                return simple_str_concat("simple_string_join(&", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .pop() → simple_string_pop(&obj) / simple_int_pop(&obj)
            if (strcmp(method_part, "pop()") == 0) {
                return simple_str_concat("simple_string_pop(&", simple_str_concat(translate_expr(obj), ")"));
            }
            // .starts_with("x") → simple_starts_with(obj, "x")
            if (starts_with(method_part, "starts_with(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 12, str_len(method_part) - 1);
                return simple_str_concat("simple_starts_with(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .ends_with("x") → simple_ends_with(obj, "x")
            if (starts_with(method_part, "ends_with(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 10, str_len(method_part) - 1);
                return simple_str_concat("simple_ends_with(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .contains("x") → simple_contains(obj, "x")
            if (starts_with(method_part, "contains(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 9, str_len(method_part) - 1);
                if (contains(obj, "args") || contains(obj, "parts") || contains(obj, "lines") ||
                    contains(obj, "items") || contains(obj, "files") || contains(obj, "list")) {
                    return simple_str_concat("simple_str_array_contains(", simple_str_concat(
                        translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
                }
                return simple_str_concat("simple_contains(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .to_int() → atoll(obj)
            if (strcmp(method_part, "to_int()") == 0) {
                return simple_str_concat("atoll(", simple_str_concat(translate_expr(obj), ")"));
            }
            // .push(x) → simple_string_push(&obj, x)
            if (starts_with(method_part, "push(") && ends_with(method_part, ")")) {
                const char* arg = substr(method_part, 5, str_len(method_part) - 1);
                return simple_str_concat("simple_string_push(&", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(translate_expr(arg), ")"))));
            }
            // .replace("a", "b") → simple_replace(obj, "a", "b")
            if (starts_with(method_part, "replace(") && ends_with(method_part, ")")) {
                const char* args_str = substr(method_part, 8, str_len(method_part) - 1);
                return simple_str_concat("simple_replace(", simple_str_concat(
                    translate_expr(obj), simple_str_concat(", ", simple_str_concat(args_str, ")"))));
            }
            // Generic field access: obj.field → obj.field (pass through)
            long long paren = find_str(method_part, "(");
            if (paren < 0) {
                // Field access
                return simple_str_concat(translate_expr(obj), simple_str_concat(".", method_part));
            }
        }
    }

    // Subscript: arr[i] or arr[N:]
    {
        long long bracket = find_str(e, "[");
        if (bracket > 0 && ends_with(e, "]")) {
            const char* obj = trim(substr(e, 0, bracket));
            const char* rest_b = substr(e, bracket + 1, str_len(e) - 1);
            // Slice: arr[N:]
            long long colon = find_str(rest_b, ":");
            if (colon >= 0 && str_len(trim(substr_from(rest_b, colon + 1))) == 0) {
                const char* start_idx = trim(substr(rest_b, 0, colon));
                const char* tobj = translate_expr(obj);
                // Heuristic: if var name contains "args" or "result" → array slice, else string slice
                if (contains(obj, "args") || contains(obj, "result") || contains(obj, "lines") ||
                    contains(obj, "parts") || contains(obj, "filtered") || contains(obj, "program") ||
                    contains(obj, "test") || contains(obj, "build")) {
                    return simple_str_concat("simple_string_array_slice(", simple_str_concat(tobj,
                        simple_str_concat(", ", simple_str_concat(translate_expr(start_idx), ")"))));
                } else {
                    // String slice
                    return simple_str_concat("simple_substr_from(", simple_str_concat(tobj,
                        simple_str_concat(", ", simple_str_concat(translate_expr(start_idx), ")"))));
                }
            }
            // Simple subscript: arr[i]
            const char* idx = trim(rest_b);
            const char* tobj = translate_expr(obj);
            return simple_str_concat(tobj, simple_str_concat(".items[", simple_str_concat(translate_expr(idx), "]")));
        }
    }

    // String concatenation: a + b (where one side is string)
    {
        long long plus_pos = find_str(e, " + ");
        if (plus_pos >= 0) {
            const char* left = trim(substr(e, 0, plus_pos));
            const char* right = trim(substr_from(e, plus_pos + 3));
            int l_is_str = starts_with(left, "\"");
            int r_is_str = starts_with(right, "\"");
            if (l_is_str || r_is_str) {
                return simple_str_concat("simple_str_concat(", simple_str_concat(
                    translate_expr(left), simple_str_concat(", ", simple_str_concat(translate_expr(right), ")"))));
            }
            // Arithmetic
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" + ", simple_str_concat(translate_expr(right), ")"))));
        }
    }

    // Subtraction
    {
        long long pos = find_str(e, " - ");
        if (pos >= 0) {
            const char* left = trim(substr(e, 0, pos));
            const char* right = trim(substr_from(e, pos + 3));
            return simple_str_concat("(", simple_str_concat(translate_expr(left),
                simple_str_concat(" - ", simple_str_concat(translate_expr(right), ")"))));
        }
    }

    // Name-based string heuristic for common text-like locals
    if (contains(name, "path") || contains(name, "dir") || contains(name, "file") ||
        contains(name, "name") || contains(name, "content") || contains(name, "output") ||
        contains(name, "manifest") || contains(name, "spec") || contains(name, "branch") ||
        contains(name, "tag") || contains(name, "constraint") || contains(name, "section") ||
        contains(name, "url") || contains(name, "text")) {
        return simple_str_concat("const char* ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    // Struct construction: Name(field: val, ...)
    {
        long long paren = find_str(e, "(");
        if (paren > 0 && contains(e, ": ") && ends_with(e, ")")) {
            const char* sname = substr(e, 0, paren);
            const char* first_ch = substr(sname, 0, 1);
            // Check uppercase first letter
            if (first_ch[0] >= 'A' && first_ch[0] <= 'Z') {
                const char* args_raw = substr(e, paren + 1, str_len(e) - 1);
                // Convert "field: val, ..." to ".field = val, ..."
                SimpleStringArray parts = simple_split(args_raw, ",");
                const char* c_fields = "";
                for (long long pi = 0; pi < parts.len; pi++) {
                    const char* part = trim(parts.items[pi]);
                    long long colon = find_str(part, ": ");
                    if (colon >= 0) {
                        const char* fname = trim(substr(part, 0, colon));
                        const char* fval = trim(substr_from(part, colon + 2));
                        if (pi > 0) c_fields = simple_str_concat(c_fields, ", ");
                        c_fields = simple_str_concat(c_fields, simple_str_concat(".", simple_str_concat(fname, simple_str_concat(" = ", translate_expr(fval)))));
                    } else {
                        if (pi > 0) c_fields = simple_str_concat(c_fields, ", ");
                        c_fields = simple_str_concat(c_fields, translate_expr(part));
                    }
                }
                return simple_str_concat("(", simple_str_concat(sname, simple_str_concat("){", simple_str_concat(c_fields, "}"))));
            }
        }
    }

    // Function call with arguments: name(arg1, arg2, ...)
    {
        long long paren = find_str(e, "(");
        if (paren > 0 && ends_with(e, ")")) {
            const char* fn_name = substr(e, 0, paren);
            // Check it's a valid identifier
            int valid = 1;
            for (long long vi = 0; vi < str_len(fn_name); vi++) {
                const char* vc = substr(fn_name, vi, vi + 1);
                if (!(is_alnum(vc) || strcmp(vc, "_") == 0 || strcmp(vc, ".") == 0)) {
                    valid = 0;
                    break;
                }
            }
            if (valid && !contains(e, ": ")) {
                fn_name = mangle_name(fn_name);
                // Translate each argument
                const char* args_raw = substr(e, paren + 1, str_len(e) - 1);
                if (str_len(trim(args_raw)) == 0) {
                    return simple_str_concat(fn_name, "()");
                }
                // Simple comma split (doesn't handle nested parens perfectly)
                SimpleStringArray args = simple_split(args_raw, ", ");
                const char* translated_args = "";
                for (long long ai = 0; ai < args.len; ai++) {
                    if (ai > 0) translated_args = simple_str_concat(translated_args, ", ");
                    translated_args = simple_str_concat(translated_args, translate_expr(trim(args.items[ai])));
                }
                return simple_str_concat(fn_name, simple_str_concat("(", simple_str_concat(translated_args, ")")));
            }
        }
    }

    // Empty array literal []
    if (strcmp(e, "[]") == 0) {
        return "simple_new_string_array()";
    }
    // Array literal [first] or [a, b, ...] — basic support
    if (starts_with(e, "[") && ends_with(e, "]")) {
        const char* inner = trim(substr(e, 1, str_len(e) - 1));
        if (str_len(inner) == 0) return "simple_new_string_array()";
        return "simple_new_string_array() /* TODO: array literal */";
    }

    /* Apply name mangling to bare identifiers */
    return mangle_name(e);
}

// Translate a condition (used in if/elif/while) — applies translate_expr
const char* translate_condition(const char* cond) {
    return translate_expr(cond);
}

const char* translate_var_decl(const char* line) {
    long long is_val = starts_with(line, "val ");
    const char* rest = "";
    if (is_val) {
        rest = trim(substr_from(line, 4));
    } else {
        rest = trim(substr_from(line, 4));
    }
    long long eq = find_str(rest, " = ");
    if (eq < 0) {
        return simple_str_concat("/* unsupported: ", simple_str_concat(line, " */"));
    }
    const char* raw_name = trim(substr(rest, 0, eq));
    long long name_colon = find_str(raw_name, ":");
    if (name_colon >= 0) {
        raw_name = trim(substr(raw_name, 0, name_colon));
    }
    const char* name = mangle_name(raw_name);
    const char* value = trim(substr_from(rest, eq + 3));
    const char* c_val = translate_expr(value);
    const char* qualifier = is_val ? "const " : "";

    // Detect type from value
    if (starts_with(value, "\"")) {
        return simple_str_concat("const char* ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    if (strcmp(value, "true") == 0 || strcmp(value, "false") == 0) {
        return simple_str_concat("int ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    if (strcmp(value, "nil") == 0) {
        return simple_str_concat("const char* ", simple_str_concat(name, " = NULL;"));
    }
    if (strcmp(value, "[]") == 0 || starts_with(value, "[") || contains(value, ".split(")) {
        return simple_str_concat("SimpleStringArray ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    // Function calls that return strings
    if (contains(value, "env_get(") || contains(value, "get_version(") ||
        contains(value, "get_file_stem(") ||
        contains(value, "read_sdn_run_config(") || contains(value, "get_cli_args(") ||
        contains(value, "cli_get_args(") || contains(value, "rt_cli_get_args(") ||
        contains(value, "sys_get_args(") || contains(value, "get_args(") ||
        contains(value, "context_generate(") || contains(value, "context_stats(")) {
        // CLI arg getters return array
        if (contains(value, "get_cli_args(") || contains(value, "cli_get_args(") ||
            contains(value, "rt_cli_get_args(") || contains(value, "sys_get_args(") ||
            contains(value, "get_args(")) {
            return simple_str_concat("SimpleStringArray ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
        }
        return simple_str_concat("const char* ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    // Struct construction: Name(field: val, ...)
    {
        long long paren = find_str(value, "(");
        if (paren > 0 && contains(value, ": ")) {
            const char* before = substr(value, 0, paren);
            // Check if first char is uppercase (struct constructor)
            const char* first_ch = substr(before, 0, 1);
            if (strcmp(first_ch, "G") == 0 || strcmp(first_ch, "D") == 0 ||
                strcmp(first_ch, "S") == 0 || strcmp(first_ch, "T") == 0 ||
                strcmp(first_ch, "C") == 0 || strcmp(first_ch, "P") == 0 ||
                strcmp(first_ch, "R") == 0 || strcmp(first_ch, "A") == 0 ||
                strcmp(first_ch, "B") == 0 || strcmp(first_ch, "E") == 0 ||
                strcmp(first_ch, "F") == 0 || strcmp(first_ch, "H") == 0 ||
                strcmp(first_ch, "I") == 0 || strcmp(first_ch, "J") == 0 ||
                strcmp(first_ch, "K") == 0 || strcmp(first_ch, "L") == 0 ||
                strcmp(first_ch, "M") == 0 || strcmp(first_ch, "N") == 0 ||
                strcmp(first_ch, "O") == 0 || strcmp(first_ch, "Q") == 0 ||
                strcmp(first_ch, "U") == 0 || strcmp(first_ch, "V") == 0 ||
                strcmp(first_ch, "W") == 0 || strcmp(first_ch, "X") == 0 ||
                strcmp(first_ch, "Y") == 0 || strcmp(first_ch, "Z") == 0) {
                return simple_str_concat(before, simple_str_concat(" ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";")))));
            }
        }
    }
    // Function calls that return strings by pattern
    if (contains(value, "filter_internal_flags(") ||
        contains(value, "parse_global_flags(")) {
        // parse_global_flags returns GlobalFlags struct
        if (contains(value, "parse_global_flags(")) {
            return simple_str_concat("GlobalFlags ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
        }
        // filter_internal_flags returns array
        return simple_str_concat("SimpleStringArray ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    // Slice → check if target is array or string
    if (contains(value, "[") && contains(value, ":]")) {
        // Extract the object name before '['
        long long br = find_str(value, "[");
        const char* slice_obj = trim(substr(value, 0, br));
        // Array names heuristic
        if (contains(slice_obj, "args") || contains(slice_obj, "filtered") ||
            contains(slice_obj, "result") || contains(slice_obj, "lines") ||
            contains(slice_obj, "parts") || contains(slice_obj, "program") ||
            contains(slice_obj, "test") || contains(slice_obj, "build") ||
            contains(slice_obj, "items")) {
            return simple_str_concat("SimpleStringArray ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
        }
        // String slice
        return simple_str_concat("const char* ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    // Subscript access on arrays → string
    if (contains(value, "[") && contains(value, "]") && !starts_with(value, "[")) {
        return simple_str_concat("const char* ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    return simple_str_concat("long long ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
}

const char* translate_return(const char* line) {
    const char* rest = trim(substr_from(line, 7));
    return simple_str_concat("return ", simple_str_concat(translate_expr(rest), ";"));
}

// Fix non-void functions: ensure last statement is a return
void fix_fn_body_return(SimpleStringArray* body, const char* sig) {
    // If function is void, skip
    if (starts_with(sig, "void ")) return;
    // Find last non-brace, non-empty line
    for (long long i = body->len - 1; i >= 0; i--) {
        const char* line = trim(body->items[i]);
        if (strcmp(line, "}") == 0 || strcmp(line, "") == 0) continue;
        // If it already has return, we're good
        if (starts_with(line, "return ")) return;
        // If it's a statement (ends with ;) and looks like a function call, add return
        if (ends_with(line, ";") && !starts_with(line, "if ") && !starts_with(line, "for ") &&
            !starts_with(line, "while ") && !starts_with(line, "}")) {
            // Replace "    stmt;" with "    return stmt;"
            // But we need to preserve the original indentation
            const char* orig = body->items[i];
            long long indent_end = 0;
            while (indent_end < str_len(orig) && strcmp(substr(orig, indent_end, indent_end + 1), " ") == 0) indent_end++;
            const char* indent_str = substr(orig, 0, indent_end);
            body->items[i] = simple_str_concat(indent_str, simple_str_concat("return ", line));
        }
        return;
    }
}

const char* generate_c(const char* source) {
    const char* c_runtime = "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <stdint.h>\n#include <stdbool.h>\n#include <math.h>\n#include <unistd.h>\n#include <time.h>\n#include <sys/stat.h>\n\n#define nil NULL\n#define pass_do_nothing ((void)0)\n#define pass_dn ((void)0)\n#define pass_todo ((void)0)\n\n"
        "#pragma GCC diagnostic ignored \"-Wdeprecated-non-prototype\"\n"
        "#pragma GCC diagnostic ignored \"-Wparentheses-equality\"\n"
        "#pragma GCC diagnostic ignored \"-Wunused-value\"\n\n";
    c_runtime = simple_str_concat(c_runtime, "static long long simple_strlen(const char* s) { return s ? (long long)strlen(s) : 0; }\n\n");
    c_runtime = simple_str_concat(c_runtime, "static char* simple_str_concat(const char* a, const char* b) {\n");
    c_runtime = simple_str_concat(c_runtime, "    if (!a) a = \"\"; if (!b) b = \"\";\n");
    c_runtime = simple_str_concat(c_runtime, "    size_t la = strlen(a), lb = strlen(b);\n");
    c_runtime = simple_str_concat(c_runtime, "    char* r = (char*)malloc(la + lb + 1);\n");
    c_runtime = simple_str_concat(c_runtime, "    memcpy(r, a, la); memcpy(r + la, b, lb); r[la+lb] = 0;\n");
    c_runtime = simple_str_concat(c_runtime, "    return r;\n}\n\n");
    c_runtime = simple_str_concat(c_runtime, "static int simple_starts_with(const char* s, const char* p) { if (!s||!p) return 0; return strncmp(s,p,strlen(p))==0; }\n");
    c_runtime = simple_str_concat(c_runtime, "static int simple_ends_with(const char* s, const char* x) { if(!s||!x) return 0; size_t sl=strlen(s),xl=strlen(x); return sl>=xl && strcmp(s+sl-xl,x)==0; }\n");
    c_runtime = simple_str_concat(c_runtime, "static int simple_contains(const char* s, const char* n) { if(!s||!n) return 0; return strstr(s,n)!=NULL; }\n");
    c_runtime = simple_str_concat(c_runtime, "static char* simple_replace(const char* s, const char* o, const char* n) {\n");
    c_runtime = simple_str_concat(c_runtime, "    if(!s) return strdup(\"\"); if(!o||!n||!*o) return strdup(s);\n");
    c_runtime = simple_str_concat(c_runtime, "    size_t ol=strlen(o),nl=strlen(n); const char*p=s; char*r=malloc(strlen(s)*2+1); char*d=r;\n");
    c_runtime = simple_str_concat(c_runtime, "    while(*p){if(strncmp(p,o,ol)==0){memcpy(d,n,nl);d+=nl;p+=ol;}else{*d++=*p++;}}\n");
    c_runtime = simple_str_concat(c_runtime, "    *d=0; return r;\n}\n\n");
    // String array type
    c_runtime = simple_str_concat(c_runtime, "typedef struct { const char** items; long long len; long long cap; } SimpleStringArray;\n");
    c_runtime = simple_str_concat(c_runtime, "static SimpleStringArray simple_new_string_array(void) { SimpleStringArray a; a.items=(const char**)malloc(16*sizeof(const char*)); a.len=0; a.cap=16; return a; }\n");
    c_runtime = simple_str_concat(c_runtime, "static void simple_string_push(SimpleStringArray* a, const char* s) { if(a->len>=a->cap){a->cap*=2;a->items=(const char**)realloc(a->items,a->cap*sizeof(const char*));} a->items[a->len++]=strdup(s?s:\"\"); }\n");
    c_runtime = simple_str_concat(c_runtime, "static SimpleStringArray simple_string_array_slice(SimpleStringArray a, long long start) { SimpleStringArray r=simple_new_string_array(); for(long long i=start;i<a.len;i++) simple_string_push(&r,a.items[i]); return r; }\n\n");
    // Format helpers
    c_runtime = simple_str_concat(c_runtime, "static char* simple_format_long(const char* b, long long v, const char* a) { char buf[256]; snprintf(buf,256,\"%s%lld%s\",b?b:\"\",v,a?a:\"\"); return strdup(buf); }\n");
    c_runtime = simple_str_concat(c_runtime, "static char* simple_format_str(const char* b, const char* v, const char* a) { size_t t=strlen(b?b:\"\")+strlen(v?v:\"\")+strlen(a?a:\"\")+1; char*r=malloc(t); snprintf(r,t,\"%s%s%s\",b?b:\"\",v?v:\"\",a?a:\"\"); return r; }\n");
    c_runtime = simple_str_concat(c_runtime, "static char* simple_int_to_str(long long v) { char b[32]; snprintf(b,32,\"%lld\",v); return strdup(b); }\n");
    c_runtime = simple_str_concat(c_runtime, "static const char* simple_substr_from(const char* s, long long start) { if(!s) return \"\"; long long l=strlen(s); if(start>=l) return \"\"; return strdup(s+start); }\n\n");
    // Integer array type (for [i64])
    c_runtime = simple_str_concat(c_runtime, "typedef struct { long long* items; long long len; long long cap; } SimpleIntArray;\n");
    c_runtime = simple_str_concat(c_runtime, "static SimpleIntArray simple_new_int_array(void) { SimpleIntArray a; a.items=(long long*)malloc(16*sizeof(long long)); a.len=0; a.cap=16; return a; }\n");
    c_runtime = simple_str_concat(c_runtime, "static void simple_int_push(SimpleIntArray* a, long long v) { if(a->len>=a->cap){a->cap*=2;a->items=(long long*)realloc(a->items,a->cap*sizeof(long long));} a->items[a->len++]=v; }\n");
    c_runtime = simple_str_concat(c_runtime, "static long long simple_int_get(SimpleIntArray a, long long i) { return a.items[i]; }\n\n");
    // Array of string arrays (for [[text]])
    c_runtime = simple_str_concat(c_runtime, "typedef struct { SimpleStringArray* items; long long len; long long cap; } SimpleStringArrayArray;\n");
    c_runtime = simple_str_concat(c_runtime, "static SimpleStringArrayArray simple_new_string_array_array(void) { SimpleStringArrayArray a; a.items=(SimpleStringArray*)malloc(8*sizeof(SimpleStringArray)); a.len=0; a.cap=8; return a; }\n");
    c_runtime = simple_str_concat(c_runtime, "static void simple_str_arr_push(SimpleStringArrayArray* a, SimpleStringArray v) { if(a->len>=a->cap){a->cap*=2;a->items=(SimpleStringArray*)realloc(a->items,a->cap*sizeof(SimpleStringArray));} a->items[a->len++]=v; }\n\n");
    // Array of int arrays (for [[i64]])
    c_runtime = simple_str_concat(c_runtime, "typedef struct { SimpleIntArray* items; long long len; long long cap; } SimpleIntArrayArray;\n");
    c_runtime = simple_str_concat(c_runtime, "static SimpleIntArrayArray simple_new_int_array_array(void) { SimpleIntArrayArray a; a.items=(SimpleIntArray*)malloc(8*sizeof(SimpleIntArray)); a.len=0; a.cap=8; return a; }\n\n");
    // Struct array type (for [StructName])
    c_runtime = simple_str_concat(c_runtime, "typedef struct { void** items; long long len; long long cap; } SimpleStructArray;\n");
    c_runtime = simple_str_concat(c_runtime, "static SimpleStructArray simple_new_struct_array(void) { SimpleStructArray a; a.items=NULL; a.len=0; a.cap=0; return a; }\n");
    c_runtime = simple_str_concat(c_runtime, "static void simple_struct_push(SimpleStructArray* a, void* v) { if(a->len>=a->cap){a->cap=a->cap?a->cap*2:8;a->items=(void**)realloc(a->items,a->cap*sizeof(void*));} a->items[a->len++]=v; }\n\n");
    // String utility functions
    c_runtime = simple_str_concat(c_runtime, "static char* simple_trim(const char* s) {\n    if(!s) return strdup(\"\");\n    while(*s==' '||*s=='\\t'||*s=='\\n'||*s=='\\r') s++;\n    long long l=strlen(s);\n    while(l>0&&(s[l-1]==' '||s[l-1]=='\\t'||s[l-1]=='\\n'||s[l-1]=='\\r')) l--;\n    char* r=malloc(l+1); memcpy(r,s,l); r[l]=0; return r;\n}\n");
    c_runtime = simple_str_concat(c_runtime, "static long long simple_index_of(const char* s, const char* n) { if(!s||!n) return -1; const char* f=strstr(s,n); return f?(long long)(f-s):-1; }\n");
    c_runtime = simple_str_concat(c_runtime, "static long long simple_last_index_of(const char* s, const char* n) { if(!s||!n) return -1; long long nl=strlen(n),sl=strlen(s); if(nl>sl) return -1; for(long long i=sl-nl;i>=0;i--) if(strncmp(s+i,n,nl)==0) return i; return -1; }\n");
    c_runtime = simple_str_concat(c_runtime, "static char* simple_substring(const char* s, long long a, long long b) { if(!s) return strdup(\"\"); long long l=strlen(s); if(a<0)a=0; if(b>l)b=l; if(a>=b) return strdup(\"\"); long long n=b-a; char*r=malloc(n+1); memcpy(r,s+a,n); r[n]=0; return r; }\n");
    c_runtime = simple_str_concat(c_runtime, "static char* simple_char_at(const char* s, long long i) { if(!s||i<0||i>=(long long)strlen(s)) return strdup(\"\"); char*r=malloc(2); r[0]=s[i]; r[1]=0; return r; }\n");
    c_runtime = simple_str_concat(c_runtime, "static SimpleStringArray simple_split(const char* s, const char* d) {\n    SimpleStringArray a=simple_new_string_array();\n    if(!s) return a; if(!d||!*d){simple_string_push(&a,s);return a;}\n    long long dl=strlen(d); const char*p=s; const char*f;\n    while((f=strstr(p,d))!=NULL){long long n=f-p;char*t=malloc(n+1);memcpy(t,p,n);t[n]=0;simple_string_push(&a,t);free(t);p=f+dl;}\n    simple_string_push(&a,p); return a;\n}\n");
    c_runtime = simple_str_concat(c_runtime, "static char* simple_string_join(SimpleStringArray* a, const char* d) {\n    if(!a||a->len==0) return strdup(\"\"); long long dl=strlen(d),t=0;\n    for(long long i=0;i<a->len;i++){t+=strlen(a->items[i]);if(i<a->len-1)t+=dl;}\n    char*r=malloc(t+1);char*p=r;\n    for(long long i=0;i<a->len;i++){long long l=strlen(a->items[i]);memcpy(p,a->items[i],l);p+=l;if(i<a->len-1){memcpy(p,d,dl);p+=dl;}}\n    *p=0; return r;\n}\n");
    c_runtime = simple_str_concat(c_runtime, "static const char* simple_string_pop(SimpleStringArray* a) { if(a->len==0) return \"\"; return a->items[--a->len]; }\n");
    c_runtime = simple_str_concat(c_runtime, "static long long simple_int_pop(SimpleIntArray* a) { if(a->len==0) return 0; return a->items[--a->len]; }\n\n");
    SimpleStringArray lines = simple_split(source, "\n");
    SimpleStringArray struct_defs = simple_new_string_array();
    SimpleStringArray struct_names = simple_new_string_array();
    SimpleStringArray fwd_decls = simple_new_string_array();
    SimpleStringArray func_defs = simple_new_string_array();
    SimpleStringArray main_lines = simple_new_string_array();
    SimpleStringArray extern_funcs = simple_new_string_array();

    // --- First pass: collect struct/class definitions ---
    {
        int in_struct = 0;
        const char* struct_name = "";
        const char* struct_body = "";
        for (long long si = 0; si < lines.len; si++) {
            const char* sl = trim(lines.items[si]);
            if ((starts_with(sl, "struct ") || starts_with(sl, "class ")) && ends_with(sl, ":")) {
                if (in_struct && str_len(struct_name) > 0) {
                    // Emit previous struct
                    const char* td = simple_str_concat("typedef struct {\n", simple_str_concat(struct_body, simple_str_concat("} ", simple_str_concat(struct_name, ";\n"))));
                    simple_string_push(&struct_defs, td);
                    simple_string_push(&struct_names, struct_name);
                }
                /* Handle both "struct Name:" and "class Name:" */
                if (starts_with(sl, "class ")) {
                    struct_name = trim(substr(sl, 6, str_len(sl) - 1));
                } else {
                    struct_name = trim(substr(sl, 7, str_len(sl) - 1));
                }
                struct_body = "";
                in_struct = 1;
            } else if (in_struct) {
                // Check if line is indented (part of struct body)
                if (starts_with(lines.items[si], "    ") && !starts_with(sl, "fn ") && !starts_with(sl, "me ") && !starts_with(sl, "static ")) {
                    // Strip inline comments
                    const char* sl_nc = sl;
                    { long long hash = find_str(sl_nc, "#");
                      if (hash >= 0) sl_nc = trim(substr(sl_nc, 0, hash)); }
                    long long colon = find_str(sl_nc, ":");
                    if (colon > 0 && !starts_with(sl_nc, "#")) {
                        const char* fname = trim(substr(sl_nc, 0, colon));
                        const char* ftype = trim(substr_from(sl_nc, colon + 1));
                        const char* ctype = stype_to_c(ftype);
                        struct_body = simple_str_concat(struct_body, simple_str_concat("    ", simple_str_concat(ctype, simple_str_concat(" ", simple_str_concat(fname, ";\n")))));
                    }
                } else {
                    // End of struct
                    if (str_len(struct_name) > 0) {
                        const char* td = simple_str_concat("typedef struct {\n", simple_str_concat(struct_body, simple_str_concat("} ", simple_str_concat(struct_name, ";\n"))));
                        simple_string_push(&struct_defs, td);
                        simple_string_push(&struct_names, struct_name);
                    }
                    in_struct = 0;
                }
            }
        }
        if (in_struct && str_len(struct_name) > 0) {
            const char* td = simple_str_concat("typedef struct {\n", simple_str_concat(struct_body, simple_str_concat("} ", simple_str_concat(struct_name, ";\n"))));
            simple_string_push(&struct_defs, td);
            simple_string_push(&struct_names, struct_name);
        }
    }

    // --- Collect extern function imports (handles multi-line) ---
    {
        int in_use = 0;
        const char* use_accum = "";
        for (long long ei = 0; ei < lines.len; ei++) {
            const char* el = lines.items[ei];
            const char* tl = trim(el);
            if (starts_with(tl, "use ")) {
                use_accum = tl;
                in_use = 1;
            } else if (in_use && starts_with(el, "    ")) {
                // Continuation line of multi-line use
                use_accum = simple_str_concat(use_accum, simple_str_concat(" ", tl));
            } else {
                in_use = 0;
            }
            // Check if we have a complete use statement (has closing paren or brace)
            if (in_use && (contains(use_accum, ")") || contains(use_accum, "}"))) {
                // Find function list in either () or {}
                long long paren = find_str(use_accum, "(");
                long long close = find_str(use_accum, ")");
                if (paren < 0) {
                    paren = find_str(use_accum, "{");
                    close = find_str(use_accum, "}");
                }
                if (paren >= 0 && close > paren) {
                    const char* func_list = substr(use_accum, paren + 1, close);
                    SimpleStringArray funcs = simple_split(func_list, ",");
                    for (long long fi = 0; fi < funcs.len; fi++) {
                        const char* fn = trim(funcs.items[fi]);
                        if (str_len(fn) > 0) {
                            simple_string_push(&extern_funcs, fn);
                        }
                    }
                }
                in_use = 0;
                use_accum = "";
            }
        }
    }
    // Also add 'error' as a known extern (used but not in use statements)
    if (!simple_str_array_contains(extern_funcs, "error"))
        simple_string_push(&extern_funcs, "error");
    if (!simple_str_array_contains(extern_funcs, "jit_native_available"))
        simple_string_push(&extern_funcs, "jit_native_available");

    // --- Pre-process: join continuation lines (multi-line expressions) ---
    {
        SimpleStringArray joined = simple_new_string_array();
        for (long long ji = 0; ji < lines.len; ji++) {
            const char* jl = lines.items[ji];
            const char* jt = trim(jl);
            // Check if this line is a continuation (indented further, not a keyword start)
            if (ji > 0 && str_len(jt) > 0 && !starts_with(jt, "#") &&
                !starts_with(jt, "fn ") && !starts_with(jt, "if ") &&
                !starts_with(jt, "elif ") && !starts_with(jt, "else:") &&
                !starts_with(jt, "while ") && !starts_with(jt, "for ") &&
                !starts_with(jt, "match ") && !starts_with(jt, "case ") &&
                !starts_with(jt, "return ") && !starts_with(jt, "val ") &&
                !starts_with(jt, "var ") && !starts_with(jt, "print ") &&
                !starts_with(jt, "struct ") && !starts_with(jt, "use ") &&
                !starts_with(jt, "import ") && !starts_with(jt, "extern ") &&
                !starts_with(jt, "break") && !starts_with(jt, "continue") &&
                strcmp(jt, "print") != 0) {
                // Check if previous line ends with comma or open paren (continuation)
                const char* prev_trimmed = trim(joined.items[joined.len - 1]);
                if (ends_with(prev_trimmed, ",") || ends_with(prev_trimmed, "(") ||
                    ends_with(prev_trimmed, "and") || ends_with(prev_trimmed, "or")) {
                    // Join to previous line
                    const char* combined = simple_str_concat(joined.items[joined.len - 1], simple_str_concat(" ", jt));
                    joined.items[joined.len - 1] = combined;
                    continue;
                }
            }
            simple_string_push(&joined, jl);
        }
        lines = joined;
    }

    int in_fn = 0;
    int in_main = 0;
    int in_struct_skip = 0;
    int in_match = 0;
    int match_first_case = 0;
    long long match_depth = 0;  /* block_depth at which the match was opened */
    const char* fn_name = "";
    const char* fn_sig = "";
    SimpleStringArray fn_body = simple_new_string_array();
    long long indent_base = 4;
    long long block_depth = 0;   /* track nested if/while/for blocks */
    long long prev_indent = 1;   /* previous line indent level (1 = function body base) */
    for (long long _idx_line = 0; _idx_line < lines.len; _idx_line++) { const char* line = lines.items[_idx_line];
        const char* trimmed = trim(line);
        if (strcmp(trimmed, "") == 0 || starts_with(trimmed, "#")) {
            continue;
        }
        // Strip inline comments (# outside of strings)
        {
            int in_str = 0;
            long long tlen = str_len(trimmed);
            for (long long ci = 0; ci < tlen; ci++) {
                const char* cc = substr(trimmed, ci, ci + 1);
                if (strcmp(cc, "\"") == 0) in_str = !in_str;
                if (!in_str && strcmp(cc, "#") == 0) {
                    trimmed = trim(substr(trimmed, 0, ci));
                    break;
                }
            }
        }
        if (strcmp(trimmed, "") == 0) continue;
        if (starts_with(trimmed, "extern fn ")) {
            continue;
        }
        if (starts_with(trimmed, "use ") || starts_with(trimmed, "import ")) {
            continue;
        }
        // Skip type aliases, newtype, alias declarations
        if (starts_with(trimmed, "type ") || starts_with(trimmed, "alias ") ||
            starts_with(trimmed, "newtype ") || starts_with(trimmed, "export ")) {
            continue;
        }
        // Skip doc comments (lines that look like documentation)
        if (starts_with(trimmed, "Returns ") || starts_with(trimmed, "Example") ||
            starts_with(trimmed, "Args:") || starts_with(trimmed, "Note:") ||
            starts_with(trimmed, "See ") || starts_with(trimmed, "Usage")) {
            continue;
        }
        // Skip struct/class definitions (handled in first pass)
        if ((starts_with(trimmed, "struct ") || starts_with(trimmed, "class ")) && ends_with(trimmed, ":")) {
            in_struct_skip = 1;
            continue;
        }
        if (in_struct_skip) {
            if (starts_with(line, "    ") && !starts_with(trimmed, "fn ") && !starts_with(trimmed, "me ") && !starts_with(trimmed, "static fn ")) {
                continue;  // Skip struct fields
            }
            if (starts_with(trimmed, "me ") || starts_with(trimmed, "static fn ")) {
                continue;  // Skip class methods (me/static fn) for now
            }
            in_struct_skip = 0;
            // Fall through to process this non-struct line
        }
        // Skip standalone 'me' method definitions
        if (starts_with(trimmed, "me ") && ends_with(trimmed, ":")) {
            in_struct_skip = 1;
            continue;
        }
        // Skip enum definitions
        if (starts_with(trimmed, "enum ") && ends_with(trimmed, ":")) {
            in_struct_skip = 1;
            continue;
        }
        // Skip trait definitions
        if (starts_with(trimmed, "trait ") && ends_with(trimmed, ":")) {
            in_struct_skip = 1;
            continue;
        }
        // Skip impl blocks
        if (starts_with(trimmed, "impl ") && ends_with(trimmed, ":")) {
            in_struct_skip = 1;
            continue;
        }
        // Skip 'extend' blocks
        if (starts_with(trimmed, "extend ") && ends_with(trimmed, ":")) {
            in_struct_skip = 1;
            continue;
        }
    // Function definition
        if (starts_with(trimmed, "fn ") && ends_with(trimmed, ":")) {
    // Close previous function
            if (in_fn) {
                /* Close any remaining open blocks */
                while (block_depth > 0) {
                    simple_string_push(&fn_body, "    }");
                    block_depth--;
                }
                fix_fn_body_return(&fn_body, fn_sig);
                const char* fn_code = simple_str_concat(fn_sig, " {\n");
                for (long long _idx_bl = 0; _idx_bl < fn_body.len; _idx_bl++) { const char* bl = fn_body.items[_idx_bl];
                    fn_code = simple_str_concat(fn_code, simple_str_concat(bl, "\n"));
                }
                fn_code = simple_str_concat(fn_code, "}\n");
                simple_string_push(&func_defs, fn_code);
                fn_body = simple_new_string_array();
            }
            if (in_main) {
                /* Close any remaining open blocks in main */
                while (block_depth > 0) {
                    simple_string_push(&main_lines, "    }");
                    block_depth--;
                }
            }
            block_depth = 0;
            prev_indent = 1;
            if (strcmp(trimmed, "fn main() -> i64:") == 0 || strcmp(trimmed, "fn main():") == 0) {
                in_main = 1;
                in_fn = 0;
                continue;
            }
            SimpleStringArray parsed = parse_fn_sig(trimmed);
            fn_name = parsed.items[0];
            fn_sig = parsed.items[1];
            simple_string_push(&fwd_decls, parsed.items[2]);
            in_fn = 1;
            in_main = 0;
            continue;
    // Indented lines (function body)
        }
        long long is_indented = starts_with(line, "    ");
        if (!(is_indented && !(starts_with(line, "\t")))) {
            if (in_fn) {
                while (block_depth > 0) {
                    simple_string_push(&fn_body, "    }");
                    block_depth--;
                }
                fix_fn_body_return(&fn_body, fn_sig);
                const char* fn_code = simple_str_concat(fn_sig, " {\n");
                for (long long _idx_bl = 0; _idx_bl < fn_body.len; _idx_bl++) { const char* bl = fn_body.items[_idx_bl];
                    fn_code = simple_str_concat(fn_code, simple_str_concat(bl, "\n"));
                }
                fn_code = simple_str_concat(fn_code, "}\n");
                simple_string_push(&func_defs, fn_code);
                fn_body = simple_new_string_array();
                in_fn = 0;
            }
            if (in_main) {
                while (block_depth > 0) {
                    simple_string_push(&main_lines, "    }");
                    block_depth--;
                }
                in_main = 0;
            }
            block_depth = 0;
            prev_indent = 1;
            continue;
    // Translate body line
        }
        /* Compute indent level of this line (number of leading spaces / 4) */
        long long cur_indent = 0;
        { long long si = 0;
          while (si < str_len(line) && strcmp(substr(line, si, si + 1), " ") == 0) si++;
          cur_indent = si / 4;
        }
        /* Close blocks when indent decreases — but NOT for elif/else/case which manage their own braces */
        int is_continuation = (starts_with(trimmed, "elif ") || strcmp(trimmed, "else:") == 0 ||
                               (starts_with(trimmed, "case ") && ends_with(trimmed, ":") && in_match));
        if (!is_continuation) {
            while (block_depth > 0 && cur_indent <= prev_indent - 1) {
                const char* close_brace = "    }";
                /* Add extra indent for nested braces */
                for (long long bi = 0; bi < block_depth - 1; bi++) {
                    close_brace = simple_str_concat("    ", close_brace);
                }
                if (in_main) {
                    simple_string_push(&main_lines, close_brace);
                } else if (in_fn) {
                    simple_string_push(&fn_body, close_brace);
                }
                block_depth--;
                prev_indent--;
                /* If we just closed back to the match level, emit match scope closing } */
                if (in_match && block_depth == match_depth) {
                    const char* match_close = "    }";
                    for (long long bi = 0; bi < match_depth; bi++) {
                        match_close = simple_str_concat("    ", match_close);
                    }
                    if (in_main) {
                        simple_string_push(&main_lines, match_close);
                    } else if (in_fn) {
                        simple_string_push(&fn_body, match_close);
                    }
                    in_match = 0;
                }
            }
        } else {
            // For elif/else/case, just adjust depth tracking without emitting braces
            // The elif/else handler emits "} else if" which closes previous block
            if (block_depth > 0) {
                block_depth--;
                prev_indent = cur_indent;
            }
        }
        prev_indent = cur_indent;
        const char* c_line = "";
        if (starts_with(trimmed, "print ")) {
            c_line = translate_print(trimmed);
        } else if (strcmp(trimmed, "print") == 0) {
            c_line = "puts(\"\");";
        } else if (starts_with(trimmed, "val ") || starts_with(trimmed, "var ")) {
            c_line = translate_var_decl(trimmed);
        } else if (starts_with(trimmed, "return ")) {
            c_line = translate_return(trimmed);
        } else if (starts_with(trimmed, "if ") && ends_with(trimmed, ":")) {
            const char* cond = trim(substr(trimmed, 3, str_len(trimmed) - 1));
            c_line = simple_str_concat("if (", simple_str_concat(translate_condition(cond), ") {"));
            block_depth++;
        } else if (strcmp(trimmed, "else:") == 0) {
            c_line = "} else {";
            block_depth++;  /* reopen block */
        } else if (starts_with(trimmed, "elif ") && ends_with(trimmed, ":")) {
            const char* cond = trim(substr(trimmed, 5, str_len(trimmed) - 1));
            c_line = simple_str_concat("} else if (", simple_str_concat(translate_condition(cond), ") {"));
            block_depth++;  /* reopen block */
        } else if (starts_with(trimmed, "while ") && ends_with(trimmed, ":")) {
            const char* cond = trim(substr(trimmed, 6, str_len(trimmed) - 1));
            c_line = simple_str_concat("while (", simple_str_concat(translate_condition(cond), ") {"));
            block_depth++;
        } else if (starts_with(trimmed, "for ") && ends_with(trimmed, ":")) {
            // for x in arr: → for (long long _i_x = 0; _i_x < arr.len; _i_x++) { const char* x = arr.items[_i_x];
            const char* for_body = trim(substr(trimmed, 4, str_len(trimmed) - 1));
            long long in_pos = find_str(for_body, " in ");
            if (in_pos >= 0) {
                const char* var_name = trim(substr(for_body, 0, in_pos));
                const char* arr_expr = trim(substr_from(for_body, in_pos + 4));
                const char* tarr = translate_expr(arr_expr);
                const char* iter_var = simple_str_concat("_i_", var_name);
                c_line = simple_str_concat("for (long long ", simple_str_concat(iter_var,
                    simple_str_concat(" = 0; ", simple_str_concat(iter_var,
                    simple_str_concat(" < ", simple_str_concat(tarr,
                    simple_str_concat(".len; ", simple_str_concat(iter_var,
                    simple_str_concat("++) { const char* ", simple_str_concat(var_name,
                    simple_str_concat(" = ", simple_str_concat(tarr,
                    simple_str_concat(".items[", simple_str_concat(iter_var, "];"))))))))))))));
            } else {
                c_line = "/* TODO: for loop (no 'in') */";
            }
            block_depth++;
        } else if (starts_with(trimmed, "match ") && ends_with(trimmed, ":")) {
            // match expr: → { const char* _match_val = translate_expr(expr);
            const char* match_expr = trim(substr(trimmed, 6, str_len(trimmed) - 1));
            c_line = simple_str_concat("{ const char* _match_val = ", simple_str_concat(translate_expr(match_expr), ";"));
            in_match = 1;
            match_first_case = 1;
            match_depth = block_depth;
            block_depth++;
        } else if (starts_with(trimmed, "case ") && ends_with(trimmed, ":") && in_match) {
            const char* case_body = trim(substr(trimmed, 5, str_len(trimmed) - 1));
            if (strcmp(case_body, "_") == 0) {
                // Default case
                c_line = "} else {";
            } else {
                // Build condition from case values separated by |
                SimpleStringArray case_parts = simple_split(case_body, " | ");
                const char* cond_str = "";
                for (long long cp = 0; cp < case_parts.len; cp++) {
                    const char* cv = trim(case_parts.items[cp]);
                    const char* one_cond = "";
                    if (starts_with(cv, "\"")) {
                        one_cond = simple_str_concat("strcmp(_match_val, ", simple_str_concat(cv, ") == 0"));
                    } else {
                        one_cond = simple_str_concat("strcmp(_match_val, ", simple_str_concat(translate_expr(cv), ") == 0"));
                    }
                    if (cp == 0) {
                        cond_str = one_cond;
                    } else {
                        cond_str = simple_str_concat(cond_str, simple_str_concat(" || ", one_cond));
                    }
                }
                if (match_first_case) {
                    c_line = simple_str_concat("if (", simple_str_concat(cond_str, ") {"));
                    match_first_case = 0;
                } else {
                    c_line = simple_str_concat("} else if (", simple_str_concat(cond_str, ") {"));
                }
            }
            block_depth++;
        } else if (strcmp(trimmed, "continue") == 0) {
            c_line = "continue;";
        } else if (strcmp(trimmed, "break") == 0) {
            c_line = "break;";
        } else {
    // Bare expression (e.g., implicit return or assignment)
            long long eq_pos = find_str(trimmed, " = ");
            if (eq_pos >= 0) {
                const char* lhs = trim(substr(trimmed, 0, eq_pos));
                const char* rhs = trim(substr_from(trimmed, eq_pos + 3));
                c_line = simple_str_concat(lhs, simple_str_concat(" = ", simple_str_concat(translate_expr(rhs), ";")));
            } else {
                /* Check if this looks like a function call statement:
                   identifier( ... ) with no operators before the paren */
                long long first_paren = find_str(trimmed, "(");
                int is_fn_call = 0;
                if (first_paren > 0) {
                    /* Check everything before ( is an identifier (alphanumeric/underscore) */
                    const char* before_paren = trim(substr(trimmed, 0, first_paren));
                    long long bp_len = str_len(before_paren);
                    is_fn_call = (bp_len > 0) ? 1 : 0;
                    for (long long ci = 0; ci < bp_len && is_fn_call; ci++) {
                        const char* cc = substr(before_paren, ci, ci + 1);
                        if (!(is_alnum(cc) || strcmp(cc, "_") == 0 || strcmp(cc, ".") == 0)) {
                            is_fn_call = 0;
                        }
                    }
                }
                // Check if struct construction (uppercase name + named args)
                int is_struct_ctor = 0;
                if (is_fn_call && first_paren > 0) {
                    const char* first_ch = substr(trimmed, 0, 1);
                    if (first_ch[0] >= 'A' && first_ch[0] <= 'Z' && contains(trimmed, ": ")) {
                        is_struct_ctor = 1;
                    }
                }
                if (is_fn_call && !is_struct_ctor) {
                    /* Function call as expression statement */
                    c_line = simple_str_concat(translate_expr(trimmed), ";");
                } else {
                    /* Bare expression — treat as implicit return */
                    c_line = simple_str_concat("return ", simple_str_concat(translate_expr(trimmed), ";"));
                }
            }
        }
        if (strcmp(c_line, "") != 0) {
            if (in_main) {
                simple_string_push(&main_lines, simple_str_concat("    ", c_line));
            } else if (in_fn) {
                simple_string_push(&fn_body, simple_str_concat("    ", c_line));
    // Close last function if open
            }
        }
    }
    /* Close remaining blocks in last function */
    if (in_fn) {
        while (block_depth > 0) {
            simple_string_push(&fn_body, "    }");
            block_depth--;
            if (in_match && block_depth == match_depth) {
                simple_string_push(&fn_body, "    }");
                in_match = 0;
            }
        }
        fix_fn_body_return(&fn_body, fn_sig);
        const char* fn_code = simple_str_concat(fn_sig, " {\n");
        for (long long _idx_bl = 0; _idx_bl < fn_body.len; _idx_bl++) { const char* bl = fn_body.items[_idx_bl];
            fn_code = simple_str_concat(fn_code, simple_str_concat(bl, "\n"));
        }
        fn_code = simple_str_concat(fn_code, "}\n");
        simple_string_push(&func_defs, fn_code);
    }
    /* Close remaining blocks in main */
    if (in_main) {
        while (block_depth > 0) {
            simple_string_push(&main_lines, "    }");
            block_depth--;
            if (in_match && block_depth == match_depth) {
                simple_string_push(&main_lines, "    }");
                in_match = 0;
            }
        }
    }
    // Assemble output
    const char* out = c_runtime;
    // Struct definitions
    for (long long _idx_sd = 0; _idx_sd < struct_defs.len; _idx_sd++) {
        out = simple_str_concat(out, simple_str_concat(struct_defs.items[_idx_sd], "\n"));
    }
    out = simple_str_concat(out, "\n");

    // Extern function stubs — emit stubs for imported functions not defined in this file
    {
        SimpleStringArray emitted_stubs = simple_new_string_array();
        for (long long si = 0; si < extern_funcs.len; si++) {
            const char* fn_orig = extern_funcs.items[si];
            const char* fn = mangle_name(fn_orig);
            // Skip duplicates (check both original and mangled)
            if (simple_str_array_contains(emitted_stubs, fn)) continue;
            simple_string_push(&emitted_stubs, fn);
            simple_string_push(&emitted_stubs, fn_orig);
            // Check if it's already defined as a forward decl (check both names)
            int is_defined = 0;
            for (long long di = 0; di < fwd_decls.len; di++) {
                if (contains(fwd_decls.items[di], simple_str_concat(" ", simple_str_concat(fn, "("))) ||
                    contains(fwd_decls.items[di], simple_str_concat(" ", simple_str_concat(fn_orig, "(")))) {
                    is_defined = 1;
                    break;
                }
            }
            if (!is_defined) {
                // Emit stub with variadic signature
                // Known string-returning functions
                // Emit stub with proper variadic-safe signature
                // Known function signatures (use mangled fn name)
                if (strcmp(fn_orig, "env_get") == 0) {
                    out = simple_str_concat(out, "static const char* env_get(const char* k) { (void)k; return \"\"; }\n");
                } else if (strcmp(fn_orig, "env_set") == 0) {
                    out = simple_str_concat(out, "static void env_set(const char* k, const char* v) { (void)k; (void)v; }\n");
                } else if (strcmp(fn_orig, "error") == 0) {
                    out = simple_str_concat(out, "static void simple_error(const char* cat, const char* msg) { fprintf(stderr, \"%s: %s\\n\", cat, msg); }\n");
                } else if (strcmp(fn_orig, "get_cli_args") == 0 ||
                           strcmp(fn_orig, "cli_get_args") == 0 ||
                           strcmp(fn_orig, "rt_cli_get_args") == 0 ||
                           strcmp(fn_orig, "sys_get_args") == 0 ||
                           strcmp(fn_orig, "get_args") == 0) {
                    out = simple_str_concat(out, simple_str_concat("static SimpleStringArray ", simple_str_concat(fn, "(void) { return simple_new_string_array(); }\n")));
                } else if (strcmp(fn_orig, "cwd") == 0 || strcmp(fn_orig, "read_sdn_run_config") == 0 ||
                           strcmp(fn_orig, "strip_sdn_quotes") == 0) {
                    out = simple_str_concat(out, simple_str_concat("static const char* ", simple_str_concat(fn, "(void) { return \"\"; }\n")));
                } else if (strcmp(fn_orig, "jit_available") == 0 || strcmp(fn_orig, "jit_native_available") == 0 ||
                           strcmp(fn_orig, "check_self_contained") == 0) {
                    out = simple_str_concat(out, simple_str_concat("static int ", simple_str_concat(fn, "(void) { return 0; }\n")));
                } else if (strcmp(fn_orig, "file_exists") == 0 || strcmp(fn_orig, "cli_file_exists") == 0) {
                    out = simple_str_concat(out, simple_str_concat("static int ", simple_str_concat(fn, "(const char* p) { (void)p; return 0; }\n")));
                } else if (strcmp(fn_orig, "load_user_config") == 0 || strcmp(fn_orig, "print_cli_help") == 0) {
                    out = simple_str_concat(out, simple_str_concat("static void ", simple_str_concat(fn, "(void) { }\n")));
                } else if (strcmp(fn_orig, "cli_run_file") == 0) {
                    out = simple_str_concat(out, "static long long cli_run_file(const char* p, SimpleStringArray a, int g, int o) { (void)p;(void)a;(void)g;(void)o; return 0; }\n");
                } else if (strcmp(fn_orig, "cli_run_code") == 0) {
                    out = simple_str_concat(out, "static long long cli_run_code(const char* c, int g, int o) { (void)c;(void)g;(void)o; return 0; }\n");
                } else if (strcmp(fn_orig, "cli_run_repl") == 0) {
                    out = simple_str_concat(out, "static long long cli_run_repl(int g, int o) { (void)g;(void)o; return 0; }\n");
                } else if (strcmp(fn_orig, "context_generate") == 0) {
                    out = simple_str_concat(out, "static const char* context_generate(const char* p, const char* t, const char* f) { (void)p;(void)t;(void)f; return \"\"; }\n");
                } else if (strcmp(fn_orig, "context_stats") == 0) {
                    out = simple_str_concat(out, "static const char* context_stats(const char* p, const char* t) { (void)p;(void)t; return \"\"; }\n");
                } else if (strcmp(fn_orig, "file_write") == 0) {
                    out = simple_str_concat(out, "static int file_write(const char* p, const char* d) { (void)p;(void)d; return 1; }\n");
                } else if (strcmp(fn_orig, "cli_run_tests") == 0 || strcmp(fn_orig, "cli_run_verify") == 0 ||
                           strcmp(fn_orig, "cli_handle_run") == 0) {
                    out = simple_str_concat(out, simple_str_concat("static long long ", simple_str_concat(fn, "(SimpleStringArray a, int g, int o) { (void)a;(void)g;(void)o; return 0; }\n")));
                } else if (strcmp(fn_orig, "cli_watch_file") == 0) {
                    out = simple_str_concat(out, "static long long cli_watch_file(const char* p) { (void)p; return 0; }\n");
                } else if (contains(fn_orig, "cli_run") || contains(fn_orig, "cli_compile") ||
                           contains(fn_orig, "cli_handle") || contains(fn_orig, "cli_constr") ||
                           contains(fn_orig, "cli_info") || contains(fn_orig, "cli_replay") ||
                           contains(fn_orig, "cli_gen") || contains(fn_orig, "cli_todo") ||
                           contains(fn_orig, "cli_watch") || contains(fn_orig, "cli_read") ||
                           contains(fn_orig, "handle_build") || contains(fn_orig, "handle_init") ||
                           contains(fn_orig, "run_check") || contains(fn_orig, "run_arch") ||
                           contains(fn_orig, "run_doc") || contains(fn_orig, "run_stats") ||
                           contains(fn_orig, "run_fix")) {
                    // CLI functions take a SimpleStringArray, return long long
                    out = simple_str_concat(out, simple_str_concat("static long long ", simple_str_concat(fn, "(SimpleStringArray a) { (void)a; return 0; }\n")));
                } else if (contains(fn_orig, "fault_set")) {
                    out = simple_str_concat(out, simple_str_concat("static void ", simple_str_concat(fn, "(long long v) { (void)v; }\n")));
                } else if (contains(fn_orig, "atomic_write")) {
                    out = simple_str_concat(out, simple_str_concat("static void ", simple_str_concat(fn, "(const char* p, const char* d) { (void)p;(void)d; }\n")));
                } else if (strcmp(fn_orig, "exit") == 0) {
                    out = simple_str_concat(out, "static void simple_exit(long long code) { _exit((int)code); }\n");
                } else {
                    // Generic stub - no args
                    out = simple_str_concat(out, simple_str_concat("static long long ", simple_str_concat(fn, "(void) { return 0; }\n")));
                }
            }
        }
    }

    // Forward declarations
    for (long long _idx_fd = 0; _idx_fd < fwd_decls.len; _idx_fd++) { const char* fd = fwd_decls.items[_idx_fd];
        out = simple_str_concat(out, simple_str_concat(fd, "\n"));
    }
    out = simple_str_concat(out, "\n");
    // Function definitions
    for (long long _idx_fdef = 0; _idx_fdef < func_defs.len; _idx_fdef++) { const char* fdef = func_defs.items[_idx_fdef];
        out = simple_str_concat(out, simple_str_concat(fdef, "\n"));
    }
    // Main
    out = simple_str_concat(out, "int main(void) {\n");
    for (long long _idx_ml = 0; _idx_ml < main_lines.len; _idx_ml++) { const char* ml = main_lines.items[_idx_ml];
        out = simple_str_concat(out, simple_str_concat(ml, "\n"));
    }
    out = simple_str_concat(out, "    return 0;\n");
    out = simple_str_concat(out, "}\n");
    return out;
}

int main(void) {
    SimpleStringArray args = rt_cli_get_args();
    if (args.len < 4) {
        puts("Usage: real_compiler <source.spl> <output.c>");
        puts("  Compiles Simple source to C");
        return 1;
    }
    const char* source_file = args.items[2];
    const char* output_file = args.items[3];
    const char* source = rt_file_read_text(source_file);
    if (source == NULL) {
        printf("%s\n",simple_str_concat("Error: cannot read ", source_file));
        return 1;
    }
    printf("%s\n",simple_str_concat("Compiling ", simple_str_concat(source_file, " to C...")));
    const char* c_code = generate_c(source);
    long long wrote = rt_file_write_text(output_file, c_code);
    if (!(wrote)) {
        printf("%s\n",simple_str_concat("Error: cannot write ", output_file));
        return 1;
    }
    printf("%s\n",simple_str_concat("Generated: ", output_file));
    return 0;
    return 0;
}
