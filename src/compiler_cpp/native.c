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
const char* rt_file_read_text(const char* path);
int rt_file_exists(const char* path);
SimpleStringArray rt_cli_get_args(void);
const char* detect_platform(void);
const char* find_c_compiler(void);
const char* find_mold_for_native(void);
const char* get_dir_of_file(const char* path);
SimpleStringArray extract_use_modules(const char* source);
const char* resolve_module_file(const char* module_path, const char* base_dir);
const char* collect_all_sources(const char* source_file, const char* source, int verbose);
long long compile_native(const char* source_file, const char* output_file, int verbose, const char* compiler_override);
int compile_c_to_object(const char* c_file, const char* obj_file, int verbose, const char* cc);
int link_objects(SimpleStringArray obj_files, const char* output_file, int verbose, const char* cc);
long long compile_native_linked(const char* source_file, const char* output_file, int verbose, const char* compiler_override);
long long compile_gen_c_only(const char* source_file, const char* output_file, int verbose);

const char* detect_platform(void) {
    long long uname = shell_output("uname -s 2>/dev/null");
    if (simple_starts_with(uname, "Linux")) {
        return "linux";
    }
    if (simple_starts_with(uname, "Darwin")) {
        return "macos";
    }
    if (simple_starts_with(uname, "FreeBSD")) {
        return "freebsd";
    }
    if (simple_starts_with(uname, "MINGW") || simple_starts_with(uname, "MSYS") || simple_starts_with(uname, "CYGWIN")) {
        return "windows";
    }
    if (strcmp(uname, "") == 0) {
    // uname failed - likely Windows without MSYS
        long long win_check = shell_output("cmd /c ver 2>NUL");
        if (simple_contains(win_check, "Windows")) {
            return "windows";
        }
    }
    return "unknown";
}

const char* find_c_compiler(void) {
    SimpleStringArray compilers = simple_new_string_array(); simple_string_push(&compilers, "clang"); simple_string_push(&compilers, "gcc"); simple_string_push(&compilers, "cc");
    for (long long _idx_compiler = 0; _idx_compiler < compilers.len; _idx_compiler++) { const char* compiler = compilers.items[_idx_compiler];
        long long check = shell_output("which {compiler} 2>/dev/null");
        if (check.len > 0) {
            return compiler;
        }
    }
    return "";
}

const char* find_mold_for_native(void) {
    // mold is Linux-only
    const char* platform = detect_platform();
    if (strcmp(platform, "linux") != 0) {
        return "";
    }
    long long current_dir = shell_output("pwd");
    const char* local_mold = simple_str_concat(current_dir, "/bin/mold/mold");
    if (rt_file_exists(local_mold)) {
        return local_mold;
    }
    long long which_result = shell_output("which mold 2>/dev/null");
    if (which_result.len > 0) {
        return which_result;
    }
    return "";
}

const char* get_dir_of_file(const char* path) {
    long long last_slash = (simple_last_index_of(path, "/") >= 0 ? simple_last_index_of(path, "/") : -1);
    if (last_slash >= 0) {
        return simple_substring(path, 0, last_slash);
    }
    return ".";
}

SimpleStringArray extract_use_modules(const char* source) {
    SimpleStringArray modules = simple_new_string_array();
    SimpleStringArray lines = simple_split(source, "\n");
    for (long long _idx_line = 0; _idx_line < lines.len; _idx_line++) { const char* line = lines.items[_idx_line];
        const char* trimmed = simple_trim(line);
        if (simple_starts_with(trimmed, "use ")) {
            const char* rest = simple_substring(trimmed, 4, simple_strlen(trimmed));
    // Skip stdlib/framework imports
            if (simple_starts_with(rest, "app.") || simple_starts_with(rest, "std.") || simple_starts_with(rest, "compiler.")) {
                continue;
    // Extract module path (before { or .)
            }
            const char* module_path = rest;
            long long brace_idx = simple_index_of(rest, "\{");
            if (brace_idx >= 0) {
                module_path = simple_substring(rest, 0, brace_idx);
                if (simple_ends_with(module_path, ".")) {
                    module_path = simple_substring(module_path, 0, simple_strlen(module_path) - 1);
                }
            }
            if (simple_ends_with(module_path, "*")) {
                continue;
            }
            if (simple_strlen(module_path) > 0) {
                simple_string_push(&modules, module_path);
            }
        }
    }
    return modules;
}

const char* resolve_module_file(const char* module_path, const char* base_dir) {
    const char* rel_path = simple_replace(module_path, ".", "/");
    const char* spl_path = simple_str_concat(base_dir, simple_str_concat("/", simple_str_concat(rel_path, ".spl")));
    if (rt_file_exists(spl_path)) {
        return spl_path;
    }
    const char* init_path = simple_str_concat(base_dir, simple_str_concat("/", simple_str_concat(rel_path, "/__init__.spl")));
    if (rt_file_exists(init_path)) {
        return init_path;
    // Fallback: strip leading package prefix if it matches the base dir name
    // Handles intra-package imports like "use compiler.core.tokens" when base_dir is src/core
    }
    long long dot_pos = simple_index_of(module_path, ".");
    if (dot_pos >= 0) {
        const char* pkg_prefix = simple_substring(module_path, 0, dot_pos);
        long long last_slash = (simple_last_index_of(base_dir, "/") >= 0 ? simple_last_index_of(base_dir, "/") : -1);
        const char* dir_name = base_dir;
        if (last_slash >= 0) {
            dir_name = simple_substring(base_dir, last_slash + 1, simple_strlen(base_dir));
        }
        if (strcmp(pkg_prefix, dir_name) == 0) {
            const char* stripped_mod = simple_substring(module_path, dot_pos + 1, simple_strlen(module_path));
            const char* stripped = simple_replace(stripped_mod, ".", "/");
            const char* stripped_path = simple_str_concat(base_dir, simple_str_concat("/", simple_str_concat(stripped, ".spl")));
            if (rt_file_exists(stripped_path)) {
                return stripped_path;
            }
            const char* stripped_init = simple_str_concat(base_dir, simple_str_concat("/", simple_str_concat(stripped, "/__init__.spl")));
            if (rt_file_exists(stripped_init)) {
                return stripped_init;
            }
        }
    }
    return "";
}

const char* collect_all_sources(const char* source_file, const char* source, int verbose) {
    const char* base_dir = get_dir_of_file(source_file);
    SimpleStringArray visited = simple_new_string_array(); simple_string_push(&visited, source_file);
    SimpleStringArray dep_sources = simple_new_string_array();
    SimpleStringArray queue = simple_new_string_array();
    // Seed queue with main file's use imports
    SimpleStringArray main_modules = extract_use_modules(source);
    for (long long _idx_mod_path = 0; _idx_mod_path < main_modules.len; _idx_mod_path++) { const char* mod_path = main_modules.items[_idx_mod_path];
        const char* file_path = resolve_module_file(mod_path, base_dir);
        if (strcmp(file_path, "") != 0 && !(simple_str_array_contains(visited, file_path))) {
            simple_string_push(&visited, file_path);
            simple_string_push(&queue, file_path);
    // BFS over dependency files
        }
    }
    long long qi = 0;
    long long combined_size = simple_strlen(source);
    while (qi < queue.len) {
        const char* dep_file = queue.items[qi];
        qi = qi + 1;
        const char* dep_source = (rt_file_read_text(dep_file) != NULL ? rt_file_read_text(dep_file) : "");
        if (strcmp(dep_source, "") == 0) {
            if (verbose) {
                warn("compile", "cannot read dependency: {dep_file}");
            }
            continue;
    // Skip if combined source would exceed 80KB (runtime file_write limit)
        }
        if (simple_str_concat(combined_size, simple_strlen(dep_source)) > 80000) {
            if (verbose) {
                debug("compile", "Skipping dependency (size limit): {dep_file}");
            }
            continue;
        }
        if (verbose) {
            debug("compile", "Including dependency: {dep_file}");
        }
        simple_string_push(&dep_sources, dep_source);
        combined_size = simple_str_concat(combined_size, simple_strlen(dep_source));
    // Discover transitive dependencies
        const char* dep_dir = get_dir_of_file(dep_file);
        SimpleStringArray sub_modules = extract_use_modules(dep_source);
        for (long long _idx_sub_mod = 0; _idx_sub_mod < sub_modules.len; _idx_sub_mod++) { const char* sub_mod = sub_modules.items[_idx_sub_mod];
            const char* sub_file = resolve_module_file(sub_mod, dep_dir);
            if (strcmp(sub_file, "") != 0 && !(simple_str_array_contains(visited, sub_file))) {
                simple_string_push(&visited, sub_file);
                simple_string_push(&queue, sub_file);
            }
        }
    }
    if (dep_sources.len == 0) {
        return source;
    }
    const char* combined = "";
    for (long long _idx_dep_src = 0; _idx_dep_src < dep_sources.len; _idx_dep_src++) { const char* dep_src = dep_sources.items[_idx_dep_src];
        combined = simple_str_concat(combined, simple_str_concat(dep_src, "\n"));
    }
    return simple_str_concat(combined, source);
}

long long compile_native(const char* source_file, const char* output_file, int verbose, const char* compiler_override) {
    if (verbose) {
        info("compile", "Compiling {source_file} to native binary...");
    // Step 1: Read source file
    }
    const char* source_raw = rt_file_read_text(source_file);
    const char* source_single = (source_raw != NULL ? source_raw : "");
    if (strcmp(source_single, "") == 0) {
        error("compile", "Cannot read source file: {source_file}");
        return 1;
    // Step 1b: Collect dependencies (multi-file support)
    }
    const char* source = collect_all_sources(source_file, source_single, verbose);
    // Step 2: Generate C code
    long long c_code = generate_c_code(source);
    if (verbose) {
        debug("compile", "Generated C code ({c_code.len()} bytes)");
    // Step 3: Write to temp file
    }
    long long temp_c = shell_output("mktemp /tmp/simple_native_XXXXXX.c");
    if (strcmp(temp_c, "") == 0) {
        error("compile", "Failed to create temp file");
        return 1;
    }
    if (!(file_write(temp_c, c_code))) {
        error("compile", "Failed to write temp C file: {temp_c}");
        return 1;
    }
    if (verbose) {
        debug("compile", "Wrote temp C file: {temp_c}");
    // Step 4: Find compiler and mold, then compile
    }
    const char* cc = (strcmp(compiler_override, "") != 0 ? compiler_override : find_c_compiler());
    if (strcmp(cc, "") == 0) {
        error("compile", "No C compiler found (tried clang, gcc, cc)");
        file_delete(temp_c);
        return 1;
    }
    const char* mold_path = find_mold_for_native();
    const char* gcc_cmd = "";
    int used_mold = 0;
    if (strcmp(mold_path, "") != 0) {
        const char* mold_dir = ".";
        long long last_slash = (simple_last_index_of(mold_path, "/") >= 0 ? simple_last_index_of(mold_path, "/") : -1);
        if (last_slash >= 0) {
            mold_dir = simple_substring(mold_path, 0, last_slash);
        }
        gcc_cmd = "{cc} -fuse-ld=mold -B {mold_dir}/ -o '{output_file}' '{temp_c}'";
        used_mold = 1;
        if (verbose) {
            debug("compile", "Using mold linker at: {mold_path}");
        }
    } else {
        gcc_cmd = "{cc} -o '{output_file}' '{temp_c}'";
        if (verbose) {
            debug("compile", "No mold found, using system linker");
        }
    }
    if (verbose) {
        debug("compile", "Running: {gcc_cmd}");
    }
    SimpleTuple3 _tmp_tuple = shell(gcc_cmd); long long gcc_out = (long long)_tmp_tuple._0; long long gcc_err = (long long)_tmp_tuple._1; long long gcc_exit = (long long)_tmp_tuple._2;
    // Step 5: Cleanup temp file
    file_delete(temp_c);
    // Step 6: Report results
    if (gcc_exit != 0) {
        error("compile", "Compilation failed (exit code {gcc_exit})");
        if (strcmp(gcc_err, "") != 0) {
            error("compile", gcc_err);
        }
        return 1;
    }
    if (rt_file_exists(output_file)) {
        long long size = file_size(output_file);
        info("compile", "Compiled: {output_file} ({size} bytes)");
        if (verbose) {
            const char* linker_name = "system";
            if (used_mold) {
                linker_name = "mold";
            }
            debug("compile", "Linker: {linker_name}");
        }
    } else {
        error("compile", "Output file not created: {output_file}");
        return 1;
    }
    return 0;
}

int compile_c_to_object(const char* c_file, const char* obj_file, int verbose, const char* cc) {
    const char* cmd = "{cc} -c -fPIE -o '{obj_file}' '{c_file}'";
    if (verbose) {
        debug("compile", "{cc} -c: {c_file} -> {obj_file}");
    }
    SimpleTuple3 _tmp_tuple = shell(cmd); long long out = (long long)_tmp_tuple._0; long long err = (long long)_tmp_tuple._1; long long exit_code = (long long)_tmp_tuple._2;
    if (exit_code != 0) {
        error("compile", "compile failed for {c_file}");
        if (strcmp(err, "") != 0) {
            error("compile", err);
        }
        return 0;
    }
    return 1;
}

int link_objects(SimpleStringArray obj_files, const char* output_file, int verbose, const char* cc) {
    // Build link command: use mold if available, else system linker
    const char* mold_path = find_mold_for_native();
    const char* link_cmd = cc;
    if (strcmp(mold_path, "") != 0) {
        const char* mold_dir = ".";
        long long last_slash = (simple_last_index_of(mold_path, "/") >= 0 ? simple_last_index_of(mold_path, "/") : -1);
        if (last_slash >= 0) {
            mold_dir = simple_substring(mold_path, 0, last_slash);
        }
        link_cmd = "{cc} -fuse-ld=mold -B {mold_dir}/";
        if (verbose) {
            debug("compile", "Using mold linker at: {mold_path}");
        }
    } else {
        if (verbose) {
            debug("compile", "Using system linker ({cc})");
    // Add object files
        }
    }
    for (long long _idx_obj = 0; _idx_obj < obj_files.len; _idx_obj++) { const char* obj = obj_files.items[_idx_obj];
        link_cmd = simple_str_concat(link_cmd, " '{obj}'");
    }
    link_cmd = simple_str_concat(link_cmd, " -o '{output_file}'");
    if (verbose) {
        debug("compile", "Link: {link_cmd}");
    }
    SimpleTuple3 _tmp_tuple = shell(link_cmd); long long out = (long long)_tmp_tuple._0; long long err = (long long)_tmp_tuple._1; long long exit_code = (long long)_tmp_tuple._2;
    if (exit_code != 0) {
        error("compile", "Linking failed (exit code {exit_code})");
        if (strcmp(err, "") != 0) {
            error("compile", err);
        }
        return 0;
    }
    return 1;
}

long long compile_native_linked(const char* source_file, const char* output_file, int verbose, const char* compiler_override) {
    if (verbose) {
        info("compile", "Compiling {source_file} to native binary (separate compile+link)...");
    // Step 1: Read main source
    }
    const char* source_raw = rt_file_read_text(source_file);
    const char* source_single = (source_raw != NULL ? source_raw : "");
    if (strcmp(source_single, "") == 0) {
        error("compile", "Cannot read source file: {source_file}");
        return 1;
    // Step 2: Discover dependency files via BFS
    }
    const char* base_dir = get_dir_of_file(source_file);
    SimpleStringArray dep_sources = simple_new_string_array();
    SimpleStringArray visited = simple_new_string_array(); simple_string_push(&visited, source_file);
    SimpleStringArray queue = simple_new_string_array();
    SimpleStringArray main_modules = extract_use_modules(source_single);
    for (long long _idx_mod_path = 0; _idx_mod_path < main_modules.len; _idx_mod_path++) { const char* mod_path = main_modules.items[_idx_mod_path];
        const char* file_path = resolve_module_file(mod_path, base_dir);
        if (strcmp(file_path, "") != 0 && !(simple_str_array_contains(visited, file_path))) {
            simple_string_push(&visited, file_path);
            simple_string_push(&queue, file_path);
        }
    }
    long long qi = 0;
    while (qi < queue.len) {
        const char* dep_file = queue.items[qi];
        qi = qi + 1;
        const char* dep_source = (rt_file_read_text(dep_file) != NULL ? rt_file_read_text(dep_file) : "");
        if (strcmp(dep_source, "") == 0) {
            if (verbose) {
                warn("compile", "cannot read dependency: {dep_file}");
            }
            continue;
        }
        if (verbose) {
            debug("compile", "Found dependency: {dep_file}");
        }
        simple_string_push(&dep_sources, dep_source);
        const char* dep_dir = get_dir_of_file(dep_file);
        SimpleStringArray sub_modules = extract_use_modules(dep_source);
        for (long long _idx_sub_mod = 0; _idx_sub_mod < sub_modules.len; _idx_sub_mod++) { const char* sub_mod = sub_modules.items[_idx_sub_mod];
            const char* sub_file = resolve_module_file(sub_mod, dep_dir);
            if (strcmp(sub_file, "") != 0 && !(simple_str_array_contains(visited, sub_file))) {
                simple_string_push(&visited, sub_file);
                simple_string_push(&queue, sub_file);
    // Step 3: Combine sources and generate C code
            }
        }
    }
    const char* combined = "";
    for (long long _idx_dep_src = 0; _idx_dep_src < dep_sources.len; _idx_dep_src++) { const char* dep_src = dep_sources.items[_idx_dep_src];
        combined = simple_str_concat(combined, simple_str_concat(dep_src, "\n"));
    }
    combined = simple_str_concat(combined, source_single);
    long long c_code = generate_c_code(combined);
    if (verbose) {
        debug("compile", "Generated C code ({c_code.len()} bytes)");
    // Step 4: Write C, compile to .o, then link separately
    }
    long long temp_dir = shell_output("mktemp -d /tmp/simple_linked_XXXXXX");
    if (strcmp(temp_dir, "") == 0) {
        error("compile", "Failed to create temp directory");
        return 1;
    }
    const char* temp_c = simple_str_concat(temp_dir, "/combined.c");
    if (!(file_write(temp_c, c_code))) {
        error("compile", "Failed to write temp C file");
        shell("rm -rf '{temp_dir}'");
        return 1;
    }
    const char* cc = (strcmp(compiler_override, "") != 0 ? compiler_override : find_c_compiler());
    if (strcmp(cc, "") == 0) {
        error("compile", "No C compiler found (tried clang, gcc, cc)");
        shell("rm -rf '{temp_dir}'");
        return 1;
    }
    const char* temp_o = simple_str_concat(temp_dir, "/combined.o");
    if (!(compile_c_to_object(temp_c, temp_o, verbose, cc))) {
        shell("rm -rf '{temp_dir}'");
        return 1;
    // Step 5: Link object file(s) to binary
    }
    SimpleStringArray obj_files = simple_new_string_array(); simple_string_push(&obj_files, temp_o);
    if (verbose) {
        debug("compile", "Linking {obj_files.len()} object file(s)...");
    }
    long long link_ok = link_objects(obj_files, output_file, verbose, cc);
    // Step 6: Cleanup
    shell("rm -rf '{temp_dir}'");
    if (!(link_ok)) {
        return 1;
    }
    if (rt_file_exists(output_file)) {
        long long size = file_size(output_file);
        info("compile", "Compiled: {output_file} ({size} bytes) [linked]");
    } else {
        error("compile", "Output file not created: {output_file}");
        return 1;
    }
    return 0;
}

long long compile_gen_c_only(const char* source_file, const char* output_file, int verbose) {
    if (verbose) {
        info("compile", "Generating C code only for {source_file}...");
    }
    const char* source_raw = rt_file_read_text(source_file);
    const char* source_single = (source_raw != NULL ? source_raw : "");
    if (strcmp(source_single, "") == 0) {
        error("compile", "Cannot read source file: {source_file}");
        return 1;
    }
    const char* source = collect_all_sources(source_file, source_single, verbose);
    long long c_code = generate_c_code(source);
    if (!(file_write(output_file, c_code))) {
        error("compile", "Failed to write C file: {output_file}");
        return 1;
    }
    info("compile", "Generated C: {output_file} ({c_code.len()} bytes)");
    return 0;
}

int main(void) {
    SimpleStringArray args = rt_cli_get_args();
    // args[0] = binary, args[1] = script path, args[2..] = user args
    // Usage: native.spl <source_file> <output_file> [--verbose] [--linked] [--gen-c-only] [--compiler=X]
    if (args.len < 4) {
        puts("Usage: native.spl <source.spl> <output> [--verbose] [--linked] [--gen-c-only] [--compiler=X]");
        return 1;
    }
    const char* source_file = args.items[2];
    const char* output_file = args.items[3];
    int verbose = 0;
    int use_linked = 0;
    int gen_c_only = 0;
    const char* compiler_override = "";
    for (long long ai = 4; ai < args.len; ai++) {
        if (strcmp(args.items[ai], "--verbose") == 0) {
            verbose = 1;
        }
        if (strcmp(args.items[ai], "--linked") == 0) {
            use_linked = 1;
        }
        if (strcmp(args.items[ai], "--gen-c-only") == 0) {
            gen_c_only = 1;
        }
        if (simple_starts_with(args[ai], "--compiler=")) {
            compiler_override = simple_substring(args[ai], 11, simple_strlen(args[ai]));
        }
    }
    if (gen_c_only) {
        return compile_gen_c_only(source_file, output_file, verbose);
    }
    if (use_linked) {
        return compile_native_linked(source_file, output_file, verbose, compiler_override);
    }
    compile_native(source_file, output_file, verbose, compiler_override);
    return 0;
}

