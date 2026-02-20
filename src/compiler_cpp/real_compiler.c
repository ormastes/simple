#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#ifdef _MSC_VER
#define strdup _strdup
#endif

// === Simple Runtime Helpers ===
// Embedded in generated C code by c_codegen.spl
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
    char buf[32];
    snprintf(buf, sizeof(buf), "%lld", value);
    return strdup(buf);
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
    o.str_val = val ? strdup(val) : strdup("");
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
    r.ok_str = val ? strdup(val) : strdup("");
    r.err_str = NULL;
    return r;
}

static SimpleResult simple_result_err_str(const char* val) {
    SimpleResult r;
    r.is_ok = 0;
    r.type_tag = 1;
    r.ok_str = NULL;
    r.err_str = val ? strdup(val) : strdup("");
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
    if (ch >= "0" && ch <= "9") {
        return 1;
    }
    return 0;
}

int is_alpha(const char* ch) {
    if (ch >= "a" && ch <= "z") {
        return 1;
    }
    if (ch >= "A" && ch <= "Z") {
        return 1;
    }
    if (strcmp(ch, "_") == 0) {
        return 1;
    }
    return 0;
}

int is_alnum(const char* ch) {
    if (is_digit(ch)) {
        return 1;
    }
    return is_alpha(ch);
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
    const char* name = trim(substr(line, fn_start, paren));
    long long arrow = find_str(line, " -> ");
    const char* ret_type = "long long";
    if (arrow >= 0) {
        const char* ret_raw = trim(substr(line, arrow + 4, str_len(line) - 1));
        if (strcmp(ret_raw, "text") == 0 || strcmp(ret_raw, "str") == 0) {
            ret_type = "const char*";
        } else if (strcmp(ret_raw, "bool") == 0) {
            ret_type = "int";
        } else if (strcmp(ret_raw, "[text]") == 0) {
            ret_type = "SimpleStringArray";
    // Parse params
        }
    }
    long long close = find_str(line, ")");
    const char* c_params = "void";
    if (close > paren + 1) {
        const char* raw_params = trim(substr(line, paren + 1, close));
        SimpleStringArray params_out = simple_new_string_array();
        SimpleStringArray parts = simple_split(raw_params, ",");
        for (long long _idx_p = 0; _idx_p < parts.len; _idx_p++) { const char* p = parts.items[_idx_p];
            const char* pt = trim(p);
            long long colon = find_str(pt, ":");
            if (colon >= 0) {
                const char* pname = trim(substr(pt, 0, colon));
                const char* ptype = trim(substr_from(pt, colon + 1));
                if (strcmp(ptype, "text") == 0 || strcmp(ptype, "str") == 0) {
                    simple_string_push(&params_out, simple_str_concat("const char* ", pname));
                } else if (strcmp(ptype, "bool") == 0) {
                    simple_string_push(&params_out, simple_str_concat("int ", pname));
                } else if (strcmp(ptype, "[text]") == 0) {
                    simple_string_push(&params_out, simple_str_concat("SimpleStringArray ", pname));
                } else if (strcmp(ptype, "[i64]") == 0) {
                    simple_string_push(&params_out, simple_str_concat("SimpleIntArray ", pname));
                } else {
                    simple_string_push(&params_out, simple_str_concat("long long ", pname));
                }
            } else {
                simple_string_push(&params_out, simple_str_concat("long long ", pt));
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
        if (contains(inner, "\{")) {
    // Interpolation: extract variable names
            const char* fmt = "";
            const char* args_str = "";
            long long i = 0;
            long long ilen = str_len(inner);
            while (i < ilen) {
                const char* ch = substr(inner, i, i + 1);
                if (strcmp(ch, "\{") == 0) {
                    long long end_brace = i + 1;
                    while (end_brace < ilen) {
                        if (strcmp(substr(inner, end_brace, end_brace + 1), "}") == 0) {
                            end_brace = end_brace;
                            break;
                        }
                        end_brace = end_brace + 1;
                    }
                    const char* var_name = substr(inner, i + 1, end_brace);
                    fmt = simple_str_concat(fmt, "%lld");
                    args_str = simple_str_concat(args_str, simple_str_concat(", (long long)", var_name));
                    i = end_brace + 1;
                } else {
                    fmt = simple_str_concat(fmt, ch);
                    i = i + 1;
                }
            }
            return simple_str_concat("printf(\"", simple_str_concat(fmt, simple_str_concat("\\n\"", simple_str_concat(args_str, ");"))));
        }
        return simple_str_concat("printf(\"%s\\n\", ", simple_str_concat(rest, ");"));
    // Variable or expression
    }
    return simple_str_concat("printf(\"%lld\\n\", (long long)(", simple_str_concat(rest, "));"));
}

const char* translate_expr(const char* expr) {
    if (strcmp(expr, "true") == 0) {
        return "1";
    }
    if (strcmp(expr, "false") == 0) {
        return "0";
    }
    if (strcmp(expr, "nil") == 0) {
        return "NULL";
    }
    if (starts_with(expr, "\"")) {
        return expr;
    // String concat: "a" + "b"
    }
    long long plus_pos = find_str(expr, " + ");
    if (plus_pos >= 0) {
        const char* left = trim(substr(expr, 0, plus_pos));
        const char* right = trim(substr_from(expr, plus_pos + 3));
        long long l_is_str = starts_with(left, "\"");
        long long r_is_str = starts_with(right, "\"");
        if (l_is_str || r_is_str) {
            return simple_str_concat("simple_str_concat(", simple_str_concat(translate_expr(left), simple_str_concat(", ", simple_str_concat(translate_expr(right), ")"))));
    // Arithmetic
        }
    }
    return expr;
}

const char* translate_var_decl(const char* line) {
    long long is_val = starts_with(line, "val ");
    const char* rest = "";
    if (is_val) {
        rest = trim(substr_from(line, 4));
    } else {
        rest = trim(substr_from(line, 4));
    }
    long long eq = find_str(rest, "=");
    if (eq < 0) {
        return simple_str_concat("/* unsupported: ", simple_str_concat(line, " */"));
    }
    const char* name = trim(substr(rest, 0, eq));
    const char* value = trim(substr_from(rest, eq + 1));
    const char* c_val = translate_expr(value);
    if (starts_with(value, "\"")) {
        return simple_str_concat("const char* ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    if (strcmp(value, "true") == 0 || strcmp(value, "false") == 0) {
        return simple_str_concat("int ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
    }
    return simple_str_concat("long long ", simple_str_concat(name, simple_str_concat(" = ", simple_str_concat(c_val, ";"))));
}

const char* translate_return(const char* line) {
    const char* rest = trim(substr_from(line, 7));
    return simple_str_concat("return ", simple_str_concat(translate_expr(rest), ";"));
}

const char* generate_c(const char* source) {
    const char* c_runtime = "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n#include <stdint.h>\n\n";
    c_runtime = simple_str_concat(c_runtime, "static char* simple_str_concat(const char* a, const char* b) \{\n");
    c_runtime = simple_str_concat(c_runtime, "    size_t la = strlen(a), lb = strlen(b);\n");
    c_runtime = simple_str_concat(c_runtime, "    char* r = (char*)malloc(la + lb + 1);\n");
    c_runtime = simple_str_concat(c_runtime, "    memcpy(r, a, la); memcpy(r + la, b, lb); r[la+lb] = 0;\n");
    c_runtime = simple_str_concat(c_runtime, "    return r;\n}\n\n");
    SimpleStringArray lines = simple_split(source, "\n");
    SimpleStringArray fwd_decls = simple_new_string_array();
    SimpleStringArray func_defs = simple_new_string_array();
    SimpleStringArray main_lines = simple_new_string_array();
    int in_fn = 0;
    int in_main = 0;
    const char* fn_name = "";
    const char* fn_sig = "";
    SimpleStringArray fn_body = simple_new_string_array();
    long long indent_base = 4;
    for (long long _idx_line = 0; _idx_line < lines.len; _idx_line++) { const char* line = lines.items[_idx_line];
        const char* trimmed = trim(line);
        if (strcmp(trimmed, "") == 0 || starts_with(trimmed, "#")) {
            continue;
    // Skip directives
        }
        if (starts_with(trimmed, "extern fn ")) {
            continue;
        }
        if (starts_with(trimmed, "use ") || starts_with(trimmed, "import ")) {
            continue;
    // Function definition
        }
        if (starts_with(trimmed, "fn ") && ends_with(trimmed, ":")) {
    // Close previous function
            if (in_fn) {
                const char* fn_code = simple_str_concat(fn_sig, " \{\n");
                for (long long _idx_bl = 0; _idx_bl < fn_body.len; _idx_bl++) { const char* bl = fn_body.items[_idx_bl];
                    fn_code = simple_str_concat(fn_code, simple_str_concat(bl, "\n"));
                }
                fn_code = simple_str_concat(fn_code, "}\n");
                simple_string_push(&func_defs, fn_code);
                fn_body = simple_new_string_array();
            }
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
                const char* fn_code = simple_str_concat(fn_sig, " \{\n");
                for (long long _idx_bl = 0; _idx_bl < fn_body.len; _idx_bl++) { const char* bl = fn_body.items[_idx_bl];
                    fn_code = simple_str_concat(fn_code, simple_str_concat(bl, "\n"));
                }
                fn_code = simple_str_concat(fn_code, "}\n");
                simple_string_push(&func_defs, fn_code);
                fn_body = simple_new_string_array();
                in_fn = 0;
            }
            if (in_main) {
                in_main = 0;
            }
            continue;
    // Translate body line
        }
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
            c_line = simple_str_concat("if (", simple_str_concat(cond, ") \{"));
        } else if (strcmp(trimmed, "else:") == 0) {
            c_line = "} else \{";
        } else if (starts_with(trimmed, "elif ") && ends_with(trimmed, ":")) {
            const char* cond = trim(substr(trimmed, 5, str_len(trimmed) - 1));
            c_line = simple_str_concat("} else if (", simple_str_concat(cond, ") \{"));
        } else if (starts_with(trimmed, "while ") && ends_with(trimmed, ":")) {
            const char* cond = trim(substr(trimmed, 6, str_len(trimmed) - 1));
            c_line = simple_str_concat("while (", simple_str_concat(cond, ") \{"));
        } else if (starts_with(trimmed, "for ") && ends_with(trimmed, ":")) {
            c_line = "/* TODO: for loop */";
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
                c_line = simple_str_concat("/* ", simple_str_concat(trimmed, " */;"));
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
    if (in_fn) {
        const char* fn_code = simple_str_concat(fn_sig, " \{\n");
        for (long long _idx_bl = 0; _idx_bl < fn_body.len; _idx_bl++) { const char* bl = fn_body.items[_idx_bl];
            fn_code = simple_str_concat(fn_code, simple_str_concat(bl, "\n"));
        }
        fn_code = simple_str_concat(fn_code, "}\n");
        simple_string_push(&func_defs, fn_code);
    // Assemble output
    }
    const char* out = c_runtime;
    // Forward declarations
    for (long long _idx_fd = 0; _idx_fd < fwd_decls.len; _idx_fd++) { const char* fd = fwd_decls.items[_idx_fd];
        out = simple_str_concat(out, simple_str_concat(fd, "\n"));
    }
    out = simple_str_concat(out, "\n");
    // Function definitions
    for (long long _idx_fdef = 0; _idx_fdef < func_defs.len; _idx_fdef++) { const char* fdef = func_defs.items[_idx_fdef];
        out = simple_str_concat(out, simple_str_concat(fdef, "\n"));
    // Main
    }
    out = simple_str_concat(out, "int main(void) \{\n");
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

