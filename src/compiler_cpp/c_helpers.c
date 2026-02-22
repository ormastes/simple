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
long long get_indent_level(const char* line);
long long get_c_indent(const char* line);
const char* simple_type_to_c(const char* stype);
const char* translate_params(const char* params_str);
SimpleStringArray parse_fn_signature(const char* trimmed);
long long find_close_paren(const char* expr, long long open_pos);
long long find_top_level_plus(const char* expr);
long long find_outside_strings(const char* expr, const char* needle);
int is_string_array_var(const char* name, const char* types);
int is_int_array_var(const char* name, const char* types);
int is_str_arr_arr_var(const char* name, const char* types);
int is_int_arr_arr_var(const char* name, const char* types);
int is_text_var(const char* name, const char* types);
int is_fn_returning_text(const char* name, const char* types);
const char* is_fn_returning_struct(const char* name, const char* types);
const char* is_struct_type_var(const char* name, const char* types);
int is_known_struct(const char* name, const char* types);
int is_known_method(const char* class_name, const char* method_name, const char* types);
int is_me_method(const char* class_name, const char* method_name, const char* types);
int is_static_fn(const char* class_name, const char* method_name, const char* types);
int is_struct_field_text(const char* dotted, const char* types);
int is_struct_field_str_array(const char* dotted, const char* types);
int is_struct_field_int_array(const char* dotted, const char* types);
int is_dict_var(const char* name, const char* types);
int is_option_var(const char* name, const char* types);
int is_enum_variant(const char* dotted, const char* types);
const char* resolve_enum_variant(const char* short_name, const char* types);
SimpleStringArray parse_method_signature(const char* trimmed, const char* class_name, int is_me);
SimpleStringArray parse_generic_type(const char* type_str);
const char* is_struct_array_var(const char* name, const char* types);
const char* is_struct_field_struct_array(const char* dotted, const char* types);
const char* is_fn_returning_struct_arr(const char* name, const char* types);
int is_fn_returning_int_arr(const char* name, const char* types);
int is_fn_returning_str_arr(const char* name, const char* types);

long long get_indent_level(const char* line) {
    long long spaces = 0;
    for (long long idx = 0; idx < simple_strlen(line); idx++) {
        const char* ch = simple_char_at(line, idx);
        if (strcmp(ch, " ") == 0) {
            spaces = spaces + 1;
        } else if (strcmp(ch, "\t") == 0) {
            spaces = spaces + 4;
        } else {
            break;
        }
    }
    return spaces / 4;
}

long long get_c_indent(const char* line) {
    long long spaces = 0;
    for (long long idx = 0; idx < simple_strlen(line); idx++) {
        const char* ch = simple_char_at(line, idx);
        if (strcmp(ch, " ") == 0) {
            spaces = spaces + 1;
        } else {
            break;
        }
    }
    return spaces / 4;
}

const char* simple_type_to_c(const char* stype) {
    if (strcmp(stype, "i64") == 0 || strcmp(stype, "int") == 0) {
        return "long long";
    }
    if (strcmp(stype, "i32") == 0) {
        return "int";
    }
    if (strcmp(stype, "f64") == 0 || strcmp(stype, "float") == 0) {
        return "double";
    }
    if (strcmp(stype, "f32") == 0) {
        return "float";
    }
    if (strcmp(stype, "bool") == 0) {
        return "int";
    }
    if (strcmp(stype, "text") == 0 || strcmp(stype, "str") == 0) {
        return "const char*";
    }
    if (strcmp(stype, "[text]") == 0 || strcmp(stype, "[str]") == 0) {
        return "SimpleStringArray";
    }
    if (strcmp(stype, "[i64]") == 0 || strcmp(stype, "[int]") == 0 || strcmp(stype, "[bool]") == 0) {
        return "SimpleIntArray";
    }
    if (strcmp(stype, "[[text]]") == 0 || strcmp(stype, "[[str]]") == 0) {
        return "SimpleStringArrayArray";
    }
    if (strcmp(stype, "[[i64]]") == 0 || strcmp(stype, "[[int]]") == 0) {
        return "SimpleIntArrayArray";
    // Struct array: [StructName] -> SimpleStructArray
    }
    if (simple_starts_with(stype, "[") && simple_ends_with(stype, "]")) {
        const char* sa_inner = simple_substring(stype, 1, simple_strlen(stype) - 1);
        if (simple_strlen(sa_inner) > 0) {
            const char* sa_first = simple_char_at(sa_inner, 0);
            if (sa_first >= "A" && sa_first <= "Z") {
                return "SimpleStructArray";
    // If the type starts with uppercase, treat it as a struct type name
            }
        }
    }
    if (simple_strlen(stype) > 0) {
        const char* first_char = simple_char_at(stype, 0);
        int is_upper = first_char >= "A" && first_char <= "Z";
        if (is_upper) {
            return stype;
    /* unsupported: "long long" */
        }
    }
}

const char* translate_params(const char* params_str) {
    SimpleStringArray params = simple_split(params_str, ",");
    SimpleStringArray c_parts = simple_new_string_array();
    for (long long _idx_param = 0; _idx_param < params.len; _idx_param++) { const char* param = params.items[_idx_param];
        const char* p = simple_trim(param);
        long long colon_idx = simple_index_of(p, ":");
        if (colon_idx >= 0) {
            const char* pname = simple_substring(p, 0, colon_idx);
            const char* ptype = simple_substring(p, colon_idx + 1, simple_strlen(p));
            const char* ctype = simple_type_to_c(ptype);
            simple_string_push(&c_parts, simple_str_concat(ctype, simple_str_concat(" ", pname)));
        } else {
            simple_string_push(&c_parts, simple_str_concat("long long ", p));
        }
    }
    return simple_string_join(&c_parts, ", ");
}

SimpleStringArray parse_fn_signature(const char* trimmed) {
    const char* without_fn = simple_substring(trimmed, 3, simple_strlen(trimmed));
    long long colon_pos = simple_strlen(without_fn) - 1;
    const char* sig = simple_substring(without_fn, 0, colon_pos);
    // Find function name (up to first paren)
    long long paren_idx = simple_index_of(sig, "(");
    if (paren_idx < 0) {
        SimpleStringArray fallback = simple_new_string_array();
        simple_string_push(&fallback, sig);
        simple_string_push(&fallback, simple_str_concat("long long ", simple_str_concat(sig, "(void)")));
        simple_string_push(&fallback, simple_str_concat("long long ", simple_str_concat(sig, "(void);")));
        return fallback;
    }
    const char* name = simple_substring(sig, 0, paren_idx);
    // Find return type - default to void if no -> annotation
    long long arrow_idx = simple_index_of(sig, "->");
    const char* ret_type = "void";
    if (arrow_idx >= 0) {
        const char* ret_str = simple_substring(sig, arrow_idx + 2, simple_strlen(sig));
        ret_type = simple_type_to_c(ret_str);
    // Parse parameters
    }
    long long close_paren_idx = simple_index_of(sig, ")");
    const char* params_str = "";
    if (close_paren_idx > paren_idx + 1) {
        params_str = simple_substring(sig, paren_idx + 1, close_paren_idx);
    }
    const char* c_params = "void";
    if (simple_strlen(params_str) > 0) {
        c_params = translate_params(params_str);
    }
    const char* c_sig = simple_str_concat(ret_type, simple_str_concat(" ", simple_str_concat(name, simple_str_concat("(", simple_str_concat(c_params, ")")))));
    SimpleStringArray result = simple_new_string_array();
    simple_string_push(&result, name);
    simple_string_push(&result, c_sig);
    simple_string_push(&result, simple_str_concat(c_sig, ";"));
    return result;
}

long long find_close_paren(const char* expr, long long open_pos) {
    // Find matching close paren, skipping string literals and escaped quotes
    long long depth = 1;
    int in_str = 0;
    long long i = open_pos + 1;
    long long elen = simple_strlen(expr);
    while (i < elen) {
        const char* ch = simple_substring(expr, i, i + 1);
        if (in_str) {
            if (strcmp(ch, "\\") == 0 && i + 1 < elen) {
    // Skip escaped character (handles \" inside strings)
                i = i + 2;
                continue;
            }
            if (strcmp(ch, "\"") == 0) {
                in_str = 0;
            }
            i = i + 1;
            continue;
        }
        if (strcmp(ch, "\"") == 0) {
            in_str = 1;
            i = i + 1;
            continue;
        }
        if (strcmp(ch, "(") == 0) {
            depth = depth + 1;
        } else if (strcmp(ch, ")") == 0) {
            depth = depth - 1;
            if (depth == 0) {
                return i;
            }
        }
        i = i + 1;
    }
    return -1;
}

long long find_top_level_plus(const char* expr) {
    int in_str = 0;
    long long depth = 0;
    long long i = 0;
    long long elen = simple_strlen(expr);
    while (i < elen) {
        const char* ch = simple_substring(expr, i, i + 1);
        if (in_str) {
            if (strcmp(ch, "\\") == 0 && i + 1 < elen) {
                i = i + 2;
                continue;
            }
            if (strcmp(ch, "\"") == 0) {
                in_str = 0;
            }
            i = i + 1;
            continue;
        }
        if (strcmp(ch, "\"") == 0) {
            in_str = 1;
            i = i + 1;
            continue;
        }
        if (strcmp(ch, "(") == 0) {
            depth = depth + 1;
        } else if (strcmp(ch, ")") == 0) {
            depth = depth - 1;
        } else if (strcmp(ch, "+") == 0 && depth == 0) {
    // Check for " + " pattern (space before and after)
            if (i >= 1 && i + 1 < elen) {
                const char* before = simple_substring(expr, i - 1, i);
                const char* after = simple_substring(expr, i + 1, i + 2);
                if (strcmp(before, " ") == 0 && strcmp(after, " ") == 0) {
                    return i - 1;
                }
            }
        }
        i = i + 1;
    }
    return -1;
}

long long find_outside_strings(const char* expr, const char* needle) {
    int in_str = 0;
    long long i = 0;
    long long elen = simple_strlen(expr);
    long long nlen = simple_strlen(needle);
    while (i < elen) {
        const char* ch = simple_substring(expr, i, i + 1);
        if (in_str) {
            if (strcmp(ch, "\\") == 0 && i + 1 < elen) {
                i = i + 2;
                continue;
            }
            if (strcmp(ch, "\"") == 0) {
                in_str = 0;
            }
            i = i + 1;
            continue;
        }
        if (strcmp(ch, "\"") == 0) {
            in_str = 1;
            i = i + 1;
            continue;
        }
        if (i + nlen <= elen) {
            const char* candidate = simple_substring(expr, i, i + nlen);
            if (strcmp(candidate, needle) == 0) {
                return i;
            }
        }
        i = i + 1;
    }
    return -1;
}

int is_string_array_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";arr:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_int_array_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";int_arr:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_str_arr_arr_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";str_arr_arr:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_int_arr_arr_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";int_arr_arr:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_text_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";text:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_fn_returning_text(const char* name, const char* types) {
    const char* marker = simple_str_concat(";fn_text:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

const char* is_fn_returning_struct(const char* name, const char* types) {
    const char* marker = simple_str_concat(";fn_struct:", simple_str_concat(name, "="));
    long long pos = simple_index_of(types, marker);
    if (pos < 0) {
        return "";
    }
    const char* after = simple_substring(types, pos + simple_strlen(marker), simple_strlen(types));
    long long end_pos = simple_index_of(after, ";");
    if (end_pos < 0) {
        return "";
    }
    return simple_substring(after, 0, end_pos);
}

const char* is_struct_type_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";struct_var:", simple_str_concat(name, "="));
    long long pos = simple_index_of(types, marker);
    if (pos < 0) {
        return "";
    }
    const char* after = simple_substring(types, pos + simple_strlen(marker), simple_strlen(types));
    long long end_pos = simple_index_of(after, ";");
    if (end_pos < 0) {
        return "";
    }
    return simple_substring(after, 0, end_pos);
}

int is_known_struct(const char* name, const char* types) {
    const char* marker = simple_str_concat(";struct:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_known_method(const char* class_name, const char* method_name, const char* types) {
    const char* marker1 = simple_str_concat(";method:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(method_name, ";"))));
    const char* marker2 = simple_str_concat(";me_method:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(method_name, ";"))));
    long long found1 = simple_contains(types, marker1);
    long long found2 = simple_contains(types, marker2);
    return found1 || found2;
}

int is_me_method(const char* class_name, const char* method_name, const char* types) {
    const char* marker = simple_str_concat(";me_method:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(method_name, ";"))));
    return simple_contains(types, marker);
}

int is_static_fn(const char* class_name, const char* method_name, const char* types) {
    const char* marker = simple_str_concat(";static_fn:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(method_name, ";"))));
    return simple_contains(types, marker);
}

int is_struct_field_text(const char* dotted, const char* types) {
    long long dot_pos = simple_index_of(dotted, ".");
    if (dot_pos < 0) {
        return 0;
    }
    const char* obj = simple_substring(dotted, 0, dot_pos);
    const char* field = simple_substring(dotted, dot_pos + 1, simple_strlen(dotted));
    const char* class_name = is_struct_type_var(obj, types);
    if (strcmp(class_name, "") == 0) {
        return 0;
    }
    const char* marker = simple_str_concat(";field_text:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(field, ";"))));
    return simple_contains(types, marker);
}

int is_struct_field_str_array(const char* dotted, const char* types) {
    long long dot_pos = simple_index_of(dotted, ".");
    if (dot_pos < 0) {
        return 0;
    }
    const char* obj = simple_substring(dotted, 0, dot_pos);
    const char* field = simple_substring(dotted, dot_pos + 1, simple_strlen(dotted));
    const char* class_name = is_struct_type_var(obj, types);
    if (strcmp(class_name, "") == 0) {
        return 0;
    }
    const char* marker = simple_str_concat(";field_arr:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(field, ";"))));
    return simple_contains(types, marker);
}

int is_struct_field_int_array(const char* dotted, const char* types) {
    long long dot_pos = simple_index_of(dotted, ".");
    if (dot_pos < 0) {
        return 0;
    }
    const char* obj = simple_substring(dotted, 0, dot_pos);
    const char* field = simple_substring(dotted, dot_pos + 1, simple_strlen(dotted));
    const char* class_name = is_struct_type_var(obj, types);
    if (strcmp(class_name, "") == 0) {
        return 0;
    }
    const char* marker = simple_str_concat(";field_int_arr:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(field, ";"))));
    return simple_contains(types, marker);
}

int is_dict_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";dict:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_option_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";option:", simple_str_concat(name, ";"));
    return simple_contains(types, marker);
}

int is_enum_variant(const char* dotted, const char* types) {
    const char* marker = simple_str_concat(";enum_variant:", simple_str_concat(dotted, ";"));
    return simple_contains(types, marker);
}

const char* resolve_enum_variant(const char* short_name, const char* types) {
    const char* search = simple_str_concat(".", simple_str_concat(short_name, ";"));
    long long pos = simple_index_of(types, search);
    if (pos < 0) {
        return "";
    // Walk backwards to find "enum_variant:"
    }
    const char* before = simple_substring(types, 0, pos);
    long long marker_pos = (simple_last_index_of(before, ";enum_variant:") >= 0 ? simple_last_index_of(before, ";enum_variant:") : -1);
    if (marker_pos < 0) {
        return "";
    }
    const char* entry = simple_substring(before, marker_pos + 14, simple_strlen(before));
    // entry is like "PointcutKind"
    return simple_str_concat(entry, simple_str_concat("_", short_name));
}

SimpleStringArray parse_method_signature(const char* trimmed, const char* class_name, int is_me) {
    // trimmed is like "fn method_name(params) -> ret:" or "me method_name(params) -> ret:"
    const char* without_prefix = "";
    if (is_me) {
        without_prefix = simple_substring(trimmed, 3, simple_strlen(trimmed));
    } else {
        without_prefix = simple_substring(trimmed, 3, simple_strlen(trimmed));
    // Remove trailing colon
    }
    long long colon_pos = simple_strlen(without_prefix) - 1;
    const char* sig = simple_substring(without_prefix, 0, colon_pos);
    long long paren_idx = simple_index_of(sig, "(");
    if (paren_idx < 0) {
        const char* mangled = simple_str_concat(class_name, simple_str_concat("__", sig));
        SimpleStringArray mfallback = simple_new_string_array();
        simple_string_push(&mfallback, sig);
        simple_string_push(&mfallback, simple_str_concat("long long ", simple_str_concat(mangled, "(void)")));
        simple_string_push(&mfallback, simple_str_concat("long long ", simple_str_concat(mangled, "(void);")));
        return mfallback;
    }
    const char* method_name = simple_substring(sig, 0, paren_idx);
    const char* mangled = simple_str_concat(class_name, simple_str_concat("__", method_name));
    // Return type - default to void if no -> annotation
    long long arrow_idx = simple_index_of(sig, "->");
    const char* ret_type = "void";
    if (arrow_idx >= 0) {
        const char* ret_str = simple_substring(sig, arrow_idx + 2, simple_strlen(sig));
        ret_type = simple_type_to_c(ret_str);
    // Parameters
    }
    long long close_paren_idx = simple_index_of(sig, ")");
    const char* params_str = "";
    if (close_paren_idx > paren_idx + 1) {
        params_str = simple_substring(sig, paren_idx + 1, close_paren_idx);
    // Build self parameter + user params
    }
    const char* self_param = simple_str_concat("const ", simple_str_concat(class_name, "* self"));
    if (is_me) {
        self_param = simple_str_concat(class_name, "* self");
    }
    const char* c_params = self_param;
    if (simple_strlen(params_str) > 0) {
        const char* user_params = translate_params(params_str);
        c_params = simple_str_concat(self_param, simple_str_concat(", ", user_params));
    }
    const char* c_sig = simple_str_concat(ret_type, simple_str_concat(" ", simple_str_concat(mangled, simple_str_concat("(", simple_str_concat(c_params, ")")))));
    SimpleStringArray mresult = simple_new_string_array();
    simple_string_push(&mresult, method_name);
    simple_string_push(&mresult, c_sig);
    simple_string_push(&mresult, simple_str_concat(c_sig, ";"));
    return mresult;
}

SimpleStringArray parse_generic_type(const char* type_str) {
    long long lt_pos = simple_index_of(type_str, "<");
    if (lt_pos < 0) {
        SimpleStringArray gt_single = simple_new_string_array();
        simple_string_push(&gt_single, type_str);
        return gt_single;
    }
    const char* base = simple_substring(type_str, 0, lt_pos);
    long long gt_pos = simple_index_of(type_str, ">");
    if (gt_pos < 0) {
        SimpleStringArray gt_base = simple_new_string_array();
        simple_string_push(&gt_base, base);
        return gt_base;
    }
    const char* inner = simple_substring(type_str, lt_pos + 1, gt_pos);
    SimpleStringArray parts = simple_split(inner, ",");
    SimpleStringArray result = simple_new_string_array();
    simple_string_push(&result, base);
    for (long long _idx_part = 0; _idx_part < parts.len; _idx_part++) { const char* part = parts.items[_idx_part];
        simple_string_push(&result, simple_trim(part));
    }
    return result;
}

const char* is_struct_array_var(const char* name, const char* types) {
    const char* marker = simple_str_concat(";struct_arr_var:", simple_str_concat(name, "="));
    long long pos = simple_index_of(types, marker);
    if (pos < 0) {
        return "";
    }
    const char* after = simple_substring(types, pos + simple_strlen(marker), simple_strlen(types));
    long long end_pos = simple_index_of(after, ";");
    if (end_pos < 0) {
        return "";
    }
    return simple_substring(after, 0, end_pos);
}

const char* is_struct_field_struct_array(const char* dotted, const char* types) {
    long long dot_pos = simple_index_of(dotted, ".");
    if (dot_pos < 0) {
        return "";
    }
    const char* obj = simple_substring(dotted, 0, dot_pos);
    const char* field = simple_substring(dotted, dot_pos + 1, simple_strlen(dotted));
    const char* class_name = is_struct_type_var(obj, types);
    if (strcmp(class_name, "") == 0) {
        return "";
    }
    const char* marker = simple_str_concat(";field_struct_arr:", simple_str_concat(class_name, simple_str_concat(".", simple_str_concat(field, "="))));
    long long pos = simple_index_of(types, marker);
    if (pos < 0) {
        return "";
    }
    const char* after = simple_substring(types, pos + simple_strlen(marker), simple_strlen(types));
    long long end_pos = simple_index_of(after, ";");
    if (end_pos < 0) {
        return "";
    }
    return simple_substring(after, 0, end_pos);
}

const char* is_fn_returning_struct_arr(const char* name, const char* types) {
    const char* marker = simple_str_concat(";fn_struct_arr:", simple_str_concat(name, "="));
    long long pos = simple_index_of(types, marker);
    if (pos < 0) {
        return "";
    }
    const char* after = simple_substring(types, pos + simple_strlen(marker), simple_strlen(types));
    long long end_pos = simple_index_of(after, ";");
    if (end_pos < 0) {
        return "";
    }
    return simple_substring(after, 0, end_pos);
}

int is_fn_returning_int_arr(const char* name, const char* types) {
    return simple_contains(types, simple_str_concat(";fn_int_arr:", simple_str_concat(name, ";")));
}

int is_fn_returning_str_arr(const char* name, const char* types) {
    return simple_contains(types, simple_str_concat(";fn_str_arr:", simple_str_concat(name, ";")));
}

int main(void) {
    return 0;
}

