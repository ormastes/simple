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


// --- Global Variables ---
static const char* CMAKE_HEADER = "# Auto-generated by Simple compiler -- DO NOT EDIT";


// --- Forward Declarations ---
int rt_file_write_text(const char* path, const char* content);
int rt_dir_create(const char* path, int recursive);
const char* rt_path_join(const char* a, const char* b);
long long generate_cmake_for_modules(const char* output_dir, long long module_files, long long text);
const char* generate_leaf_cmake(const char* lib_name, SimpleStringArray files, SimpleStringArray child_subdirs);
const char* generate_intermediate_cmake(SimpleStringArray subdirs);
const char* generate_root_cmake(SimpleStringArray top_dirs, SimpleStringArray root_sources, SimpleStringArray object_libs);
const char* generate_root_cmakelists(const char* output_dir, SimpleStringArray top_dirs, SimpleStringArray root_sources, SimpleStringArray object_libs);

long long generate_cmake_for_modules(const char* output_dir, long long module_files, long long text) {
    return Args:;
        /* unsupported: output_dir: Root output directory */
        /* unsupported: module_files: List of (module_name, relative_path) pairs where relative_path */
                    return is like "main.cpp" || "compiler/core/parser.cpp";
        /* unsupported: log: Logger instance */
    return Returns nil on success, error message on failure.;
    // Collect directory info: which dirs have .cpp files, which have subdirs
    SimpleDict* dir_files = simple_dict_new();
    SimpleDict* dir_subdirs = simple_dict_new();
    SimpleStringArray all_dirs = simple_new_string_array();
    SimpleStringArray root_sources = simple_new_string_array();
    SimpleStringArray object_libs = simple_new_string_array();
    for (long long _idx_entry = 0; _idx_entry < module_files_len; _idx_entry++) { long long entry = module_files[_idx_entry];
        long long rel_path = entry.1;
        SimpleStringArray parts = simple_split(rel_path, "/");
        if (parts.len == 1) {
    // Root-level file
            simple_string_push(&root_sources, rel_path);
        } else {
    // File in a subdirectory
            const char* filename = parts[parts.len;
            const char* dir_parts = parts[0:parts.len;
            const char* dir_path = simple_string_join(&dir_parts, "/");
            if (simple_dict_contains(dir_files, dir_path not)) {
                simple_dict_set_int(dir_files, dir_path, []);
                simple_string_push(&all_dirs, dir_path);
            /* dir_files[dir_path].push(filename) */;
    // Register parent->child relationships for all intermediate dirs
            }
            long long i = simple_strlen(dir_parts) - 1;
            while (i > 0) {
                const char* parent = simple_string_join(&dir_parts[0:i], "/");
                const char* child = simple_char_at(dir_parts, i);
                if (simple_dict_contains(dir_subdirs, parent not)) {
                    simple_dict_set_int(dir_subdirs, parent, []);
                }
                if (child not in dir_subdirs[parent]) {
                    /* dir_subdirs[parent].push(child) */;
                }
                i = i - 1;
    // Top-level dir -> register under root
            }
            const char* top_dir = simple_char_at(dir_parts, 0);
            if (simple_dict_contains(dir_subdirs, "" not)) {
                simple_dict_set_int(dir_subdirs, "", []);
            }
            if (top_dir not in dir_subdirs[""]) {
                /* dir_subdirs[""].push(top_dir) */;
    // Generate leaf CMakeLists.txt (dirs with .cpp files)
            }
        }
    }
    for (long long _idx_dir_path = 0; _idx_dir_path < all_dirs.len; _idx_dir_path++) { const char* dir_path = all_dirs.items[_idx_dir_path];
        const char* files = simple_dict_get(dir_files, dir_path);
        const char* lib_name = simple_str_concat("gen_", simple_replace(dir_path, "/", "_"));
        simple_string_push(&object_libs, lib_name);
    // Collect child subdirs for this directory (if any)
        SimpleStringArray child_subdirs = simple_new_string_array();
        if (simple_dict_contains(dir_subdirs, dir_path)) {
            child_subdirs = simple_dict_get(dir_subdirs, dir_path);
        }
        const char* cmake_content = generate_leaf_cmake(lib_name, files, child_subdirs);
        const char* cmake_path = rt_path_join(rt_path_join(output_dir, dir_path), "CMakeLists.txt");
        if (!(rt_file_write_text(cmake_path, cmake_content))) {
            return "Failed to write {cmake_path}";
    // Generate intermediate CMakeLists.txt (dirs with only subdirs, no .cpp files)
        }
    }
    for (long long _idx_dir_path = 0; _idx_dir_path < dir_subdirs.keys()_len; _idx_dir_path++) { long long dir_path = dir_subdirs.keys()[_idx_dir_path];
        if (strcmp(dir_path, "") == 0) {
            return pass_dn;
        } else if (simple_dict_contains(dir_files, dir_path not)) {
            const char* subdirs = simple_dict_get(dir_subdirs, dir_path);
            const char* cmake_content = generate_intermediate_cmake(subdirs);
            const char* cmake_path = rt_path_join(rt_path_join(output_dir, dir_path), "CMakeLists.txt");
            rt_dir_create(rt_path_join(output_dir, dir_path), 1);
            if (!(rt_file_write_text(cmake_path, cmake_content))) {
                return "Failed to write {cmake_path}";
    // Generate root generated_sources.cmake
            }
        }
    }
    SimpleStringArray top_dirs = simple_new_string_array();
    if (simple_dict_contains(dir_subdirs, "")) {
        top_dirs = simple_dict_get(dir_subdirs, "");
    }
    const char* root_cmake = generate_root_cmake(top_dirs, root_sources, object_libs);
    const char* root_cmake_path = rt_path_join(output_dir, "generated_sources.cmake");
    if (!(rt_file_write_text(root_cmake_path, root_cmake))) {
        return "Failed to write {root_cmake_path}";
    // Generate root CMakeLists.txt (project file)
    }
    const char* root_cmakelists = generate_root_cmakelists(output_dir, top_dirs, root_sources, object_libs);
    const char* root_cmakelists_path = rt_path_join(output_dir, "CMakeLists.txt");
    if (!(rt_file_write_text(root_cmakelists_path, root_cmakelists))) {
        return "Failed to write {root_cmakelists_path}";
    }
    return NULL;
}

const char* generate_leaf_cmake(const char* lib_name, SimpleStringArray files, SimpleStringArray child_subdirs) {
    const char* runtime_dir = "${RUNTIME_DIR}";
    const char* content = simple_str_concat(CMAKE_HEADER, "\n");
    content = simple_str_concat(content, "add_library({lib_name} OBJECT\n");
    for (long long _idx_file = 0; _idx_file < files.len; _idx_file++) { const char* file = files.items[_idx_file];
        content = simple_str_concat(content, "    {file}\n");
    }
    content = simple_str_concat(content, ")\n\n");
    content = simple_str_concat(content, "target_include_directories({lib_name} PRIVATE\n");
    content = simple_str_concat(content, "    {runtime_dir}\n");
    content = simple_str_concat(content, "    {runtime_dir}/platform\n");
    const char* gen_root = "${CMAKE_SOURCE_DIR}";
    content = simple_str_concat(content, "    {gen_root}\n");
    content = simple_str_concat(content, ")\n");
    // Add subdirectory references if this dir also has child dirs
    if (child_subdirs.len > 0) {
        content = simple_str_concat(content, "\n");
        for (long long _idx_subdir = 0; _idx_subdir < child_subdirs.len; _idx_subdir++) { const char* subdir = child_subdirs.items[_idx_subdir];
            content = simple_str_concat(content, "add_subdirectory({subdir})\n");
        }
    }
    return content;
}

const char* generate_intermediate_cmake(SimpleStringArray subdirs) {
    const char* content = simple_str_concat(CMAKE_HEADER, "\n");
    for (long long _idx_subdir = 0; _idx_subdir < subdirs.len; _idx_subdir++) { const char* subdir = subdirs.items[_idx_subdir];
        content = simple_str_concat(content, "add_subdirectory({subdir})\n");
    }
    return content;
}

const char* generate_root_cmake(SimpleStringArray top_dirs, SimpleStringArray root_sources, SimpleStringArray object_libs) {
    const char* cmake_list_dir = "${CMAKE_CURRENT_LIST_DIR}";
    const char* cmake_bin_dir = "${CMAKE_CURRENT_BINARY_DIR}";
    const char* content = simple_str_concat(CMAKE_HEADER, "\n");
    content = simple_str_concat(content, "# Include from the root CMakeLists.txt:\n");
    content = simple_str_concat(content, "#   include(generated/generated_sources.cmake)\n\n");
    // Add top-level subdirectories
    for (long long _idx_dir = 0; _idx_dir < top_dirs.len; _idx_dir++) { const char* dir = top_dirs.items[_idx_dir];
        content = simple_str_concat(content, "add_subdirectory({cmake_list_dir}/{dir} {cmake_bin_dir}/generated_{dir})\n");
    }
    content = simple_str_concat(content, "\n");
    // Root source files
    content = simple_str_concat(content, "set(GENERATED_ROOT_SOURCES\n");
    for (long long _idx_src = 0; _idx_src < root_sources.len; _idx_src++) { const char* src = root_sources.items[_idx_src];
        content = simple_str_concat(content, "    {cmake_list_dir}/{src}\n");
    }
    content = simple_str_concat(content, ")\n\n");
    // Object library list
    content = simple_str_concat(content, "set(GENERATED_OBJECT_LIBS\n");
    for (long long _idx_lib = 0; _idx_lib < object_libs.len; _idx_lib++) { const char* lib = object_libs.items[_idx_lib];
        content = simple_str_concat(content, "    {lib}\n");
    }
    content = simple_str_concat(content, ")\n");
    return content;
}

const char* generate_root_cmakelists(const char* output_dir, SimpleStringArray top_dirs, SimpleStringArray root_sources, SimpleStringArray object_libs) {
    const char* runtime_dir = "${CMAKE_CURRENT_SOURCE_DIR}/../runtime";
    const char* cmake_source_dir = "${CMAKE_SOURCE_DIR}";
    const char* content = simple_str_concat(CMAKE_HEADER, "\n");
    content = simple_str_concat(content, "cmake_minimum_required(VERSION 3.20)\n");
    content = simple_str_concat(content, "project(simple LANGUAGES C CXX)\n\n");
    content = simple_str_concat(content, "set(CMAKE_CXX_STANDARD 20)\n");
    content = simple_str_concat(content, "set(CMAKE_CXX_STANDARD_REQUIRED ON)\n");
    content = simple_str_concat(content, "set(CMAKE_C_STANDARD 11)\n");
    content = simple_str_concat(content, "set(CMAKE_C_STANDARD_REQUIRED ON)\n\n");
    // Runtime source paths
    content = simple_str_concat(content, "set(RUNTIME_DIR {runtime_dir})\n");
    const char* rt_dir_var = "${RUNTIME_DIR}";
    content = simple_str_concat(content, "set(RUNTIME_SOURCES\n");
    content = simple_str_concat(content, "    {rt_dir_var}/runtime.c\n");
    content = simple_str_concat(content, "    {rt_dir_var}/runtime_thread.c\n");
    content = simple_str_concat(content, ")\n\n");
    // Include generated sources
    content = simple_str_concat(content, "include(generated_sources.cmake)\n\n");
    // Executable target
    const char* gen_root_src = "${GENERATED_ROOT_SOURCES}";
    const char* rt_src = "${RUNTIME_SOURCES}";
    content = simple_str_concat(content, "add_executable(simple {gen_root_src} {rt_src})\n\n");
    // Link object libraries
    const char* gen_obj_libs = "${GENERATED_OBJECT_LIBS}";
    const char* lib_var = "${LIB}";
    const char* target_objects = "$<TARGET_OBJECTS:${LIB}>";
    content = simple_str_concat(content, "foreach(LIB {gen_obj_libs})\n");
    content = simple_str_concat(content, "    target_link_libraries(simple PRIVATE {target_objects})\n");
    content = simple_str_concat(content, "endforeach()\n\n");
    // Include directories
    content = simple_str_concat(content, "target_include_directories(simple PRIVATE\n");
    content = simple_str_concat(content, "    {rt_dir_var}\n");
    content = simple_str_concat(content, "    {rt_dir_var}/platform\n");
    content = simple_str_concat(content, "    {cmake_source_dir}\n");
    content = simple_str_concat(content, ")\n\n");
    // Platform-specific libraries
    content = simple_str_concat(content, "if(UNIX)\n");
    content = simple_str_concat(content, "    target_link_libraries(simple PRIVATE pthread dl m)\n");
    content = simple_str_concat(content, "endif()\n\n");
    content = simple_str_concat(content, "if(WIN32)\n");
    content = simple_str_concat(content, "    target_link_libraries(simple PRIVATE ws2_32)\n");
    content = simple_str_concat(content, "endif()\n");
    return content;
}

int main(void) {
    return 0;
}

