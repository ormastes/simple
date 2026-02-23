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
const char* translate_interpolated_print(const char* inner, const char* types);
const char* translate_print(const char* arg, const char* types);
const char* translate_for_loop(const char* trimmed, const char* types);
const char* translate_case(const char* trimmed, const char* types);
const char* translate_statement(const char* trimmed, const char* types);

const char* translate_interpolated_print(const char* inner, const char* types) {
    const char* fmt = "";
    SimpleStringArray interp_args = simple_new_string_array();
    long long i = 0;
    long long inner_len = simple_strlen(inner);
    for (long long idx = 0; idx < inner_len; idx++) {
        const char* ch = simple_char_at(inner, idx);
        if (strcmp(ch, "\{") == 0) {
            long long end_idx = idx + 1;
            for (long long j = idx + 1; j < inner_len; j++) {
                if (strcmp(simple_char_at(inner, j), "}") == 0) {
                    end_idx = j;
                    break;
                }
            }
            const char* raw_expr = simple_substring(inner, idx + 1, end_idx);
            long long c_expr = translate_expr(raw_expr, types);
    // Determine format specifier based on expression type
            long long is_text = is_text_var(raw_expr, types);
            long long is_dict_keys = simple_contains(c_expr, "simple_dict_keys");
    // Check if raw expr is a struct field that returns text
            long long raw_dot = simple_index_of(raw_expr, ".");
            int is_struct_text_field = 0;
            if (raw_dot >= 0) {
                const char* sf_obj = simple_substring(raw_expr, 0, raw_dot);
                const char* sf_field = simple_substring(raw_expr, raw_dot + 1, simple_strlen(raw_expr));
                long long sf_class = is_struct_type_var(sf_obj, types);
                if (strcmp(sf_class, "") != 0) {
                    const char* field_text_marker = simple_str_concat(";field_text:", simple_str_concat(sf_class, simple_str_concat(".", simple_str_concat(sf_field, ";"))));
                    is_struct_text_field = simple_contains(types, field_text_marker);
                }
            }
            int any_string = is_c_expr_string_result(c_expr) || is_text || is_struct_text_field;
            if (any_string) {
                fmt = simple_str_concat(fmt, "%s");
                simple_string_push(&interp_args, c_expr);
            } else {
                fmt = simple_str_concat(fmt, "%lld");
                simple_string_push(&interp_args, simple_str_concat("(long long)(", simple_str_concat(c_expr, ")")));
            }
            i = end_idx + 1;
        } else if (idx >= i) {
            fmt = simple_str_concat(fmt, ch);
        }
    }
    const char* args_str = "";
    for (long long _idx_current_arg = 0; _idx_current_arg < interp_args.len; _idx_current_arg++) { const char* current_arg = interp_args.items[_idx_current_arg];
        args_str = simple_str_concat(args_str, simple_str_concat(", ", current_arg));
    }
    return simple_str_concat("printf(", simple_str_concat("\"", simple_str_concat(fmt, simple_str_concat("\n", simple_str_concat("\"", simple_str_concat(args_str, ");"))))));
}

const char* translate_print(const char* arg, const char* types) {
    if (simple_strlen(arg) < 2) {
        return "puts(\"\");";
    }
    if (simple_starts_with(arg, "\"") && simple_ends_with(arg, "\"")) {
    // Check for string concatenation: "str" + expr + "str"
        int has_concat = simple_contains(arg, "\" + ") || simple_contains(arg, " + \"");
        if (has_concat) {
            long long c_arg = translate_expr(arg, types);
            return simple_str_concat("printf(", simple_str_concat("\"", simple_str_concat("%s\n", simple_str_concat("\",", simple_str_concat(c_arg, ");")))));
    // Check for interpolation: {expr} inside the string
        }
        if (simple_contains(arg, "\{")) {
    // Extract inner text between quotes for interpolation
            const char* inner = simple_substring(arg, 1, simple_strlen(arg) - 1);
            if (simple_ends_with(inner, "\"")) {
                inner = simple_substring(inner, 0, simple_strlen(inner) - 1);
            }
            return translate_interpolated_print(inner, types);
    // Simple string literal - use arg directly (already has quotes)
    // Emit as puts(arg) with \n via puts
    // Use printf to append newline properly
        }
        return simple_str_concat("puts(", simple_str_concat(arg, ");"));
    // Print a variable
    }
    if (is_text_var(arg, types)) {
        return simple_str_concat("printf(", simple_str_concat("\"", simple_str_concat("%s\n", simple_str_concat("\",", simple_str_concat(arg, ");")))));
    // Translate expression and check if it's a string result
    }
    long long c_arg = translate_expr(arg, types);
    if (is_c_expr_string_result(c_arg)) {
        return simple_str_concat("printf(", simple_str_concat("\"", simple_str_concat("%s\n", simple_str_concat("\",", simple_str_concat(c_arg, ");")))));
    }
    return simple_str_concat("printf(", simple_str_concat("\"", simple_str_concat("%lld\n", simple_str_concat("\",(long long)", simple_str_concat(c_arg, ");")))));
}

const char* translate_for_loop(const char* trimmed, const char* types) {
    const char* body = simple_substring(trimmed, 4, simple_strlen(trimmed) - 1);
    long long in_idx = simple_index_of(body, " in ");
    if (in_idx < 0) {
        return simple_str_concat("/* unsupported for: ", simple_str_concat(trimmed, " */"));
    }
    const char* loop_var = simple_substring(body, 0, in_idx);
    const char* iterable = simple_substring(body, in_idx + 4, simple_strlen(body));
    // range(start, end)
    if (simple_starts_with(iterable, "range(") && simple_ends_with(iterable, ")")) {
        const char* range_args = simple_substring(iterable, 6, simple_strlen(iterable) - 1);
        long long comma_idx = simple_index_of(range_args, ",");
        if (comma_idx >= 0) {
            const char* start_expr = simple_substring(range_args, 0, comma_idx);
            const char* end_expr = simple_substring(range_args, comma_idx + 1, simple_strlen(range_args));
            return simple_str_concat("for (long long ", simple_str_concat(loop_var, simple_str_concat(" = ", simple_str_concat(translate_expr(start_expr, types), simple_str_concat("; ", simple_str_concat(loop_var, simple_str_concat(" < ", simple_str_concat(translate_expr(end_expr, types), simple_str_concat("; ", simple_str_concat(loop_var, simple_str_concat("++) ", "\{")))))))))));
        } else {
            return simple_str_concat("for (long long ", simple_str_concat(loop_var, simple_str_concat(" = 0; ", simple_str_concat(loop_var, simple_str_concat(" < ", simple_str_concat(translate_expr(range_args, types), simple_str_concat("; ", simple_str_concat(loop_var, simple_str_concat("++) ", "\{")))))))));
    // Inline array literal: [1, 2, 3, 4, 5]
        }
    }
    if (simple_starts_with(iterable, "[") && simple_ends_with(iterable, "]")) {
        const char* inner = simple_substring(iterable, 1, simple_strlen(iterable) - 1);
        SimpleStringArray elements = simple_split(inner, ",");
        const char* init = simple_str_concat("SimpleIntArray _arr_", simple_str_concat(loop_var, " = simple_new_int_array();"));
        for (long long _idx_elem = 0; _idx_elem < elements.len; _idx_elem++) { const char* elem = elements.items[_idx_elem];
            const char* e = translate_expr(simple_trim(elem), types);
            init = simple_str_concat(init, simple_str_concat(" simple_int_push(&_arr_", simple_str_concat(loop_var, simple_str_concat(", ", simple_str_concat(e, ");")))));
        }
        init = simple_str_concat(init, simple_str_concat(" for (long long _idx_", simple_str_concat(loop_var, simple_str_concat(" = 0; _idx_", simple_str_concat(loop_var, simple_str_concat(" < _arr_", simple_str_concat(loop_var, simple_str_concat(".len; _idx_", simple_str_concat(loop_var, simple_str_concat("++) \{ long long ", simple_str_concat(loop_var, simple_str_concat(" = _arr_", simple_str_concat(loop_var, simple_str_concat(".items[_idx_", simple_str_concat(loop_var, "];")))))))))))))));
        return init;
    // start..end range
    }
    long long dotdot_idx = simple_index_of(iterable, "..");
    if (dotdot_idx >= 0) {
        const char* start_expr = simple_substring(iterable, 0, dotdot_idx);
        const char* end_expr = simple_substring(iterable, dotdot_idx + 2, simple_strlen(iterable));
        return simple_str_concat("for (long long ", simple_str_concat(loop_var, simple_str_concat(" = ", simple_str_concat(translate_expr(start_expr, types), simple_str_concat("; ", simple_str_concat(loop_var, simple_str_concat(" < ", simple_str_concat(translate_expr(end_expr, types), simple_str_concat("; ", simple_str_concat(loop_var, simple_str_concat("++) ", "\{")))))))))));
    // Inline array literal: for i in [1, 2, 3]:
    }
    if (simple_starts_with(iterable, "[") && simple_ends_with(iterable, "]")) {
        const char* ia_inner = simple_substring(iterable, 1, simple_strlen(iterable) - 1);
        SimpleStringArray ia_elements = simple_split(ia_inner, ",");
        const char* ia_init = simple_str_concat("\{ SimpleIntArray _arr_", simple_str_concat(loop_var, " = simple_new_int_array();"));
        for (long long _idx_ia_elem = 0; _idx_ia_elem < ia_elements.len; _idx_ia_elem++) { const char* ia_elem = ia_elements.items[_idx_ia_elem];
            const char* ia_e = translate_expr(simple_trim(ia_elem), types);
            ia_init = simple_str_concat(ia_init, simple_str_concat(" simple_int_push(&_arr_", simple_str_concat(loop_var, simple_str_concat(", ", simple_str_concat(ia_e, ");")))));
        }
        ia_init = simple_str_concat(ia_init, simple_str_concat(" for (long long _idx_", simple_str_concat(loop_var, simple_str_concat(" = 0; _idx_", simple_str_concat(loop_var, simple_str_concat(" < _arr_", simple_str_concat(loop_var, simple_str_concat(".len; _idx_", simple_str_concat(loop_var, simple_str_concat("++) \{ long long ", simple_str_concat(loop_var, simple_str_concat(" = _arr_", simple_str_concat(loop_var, simple_str_concat(".items[_idx_", simple_str_concat(loop_var, "];")))))))))))))));
        return ia_init;
    // for item in string_array or struct.field string array
    }
    if (is_string_array_var(iterable, types) || is_struct_field_str_array(iterable, types)) {
        return gen_array_for_loop(loop_var, iterable, "const char*", 1);
    // for item in int_array or struct.field int array
    }
    if (is_int_array_var(iterable, types) || is_struct_field_int_array(iterable, types)) {
        return gen_array_for_loop(loop_var, iterable, "long long", 0);
    // for item in struct_array (SimpleStructArray)
    }
    long long sa_iter_elem = is_struct_array_var(iterable, types);
    if (strcmp(sa_iter_elem, "") != 0) {
        return simple_str_concat("for (long long _idx_", simple_str_concat(loop_var, simple_str_concat(" = 0; _idx_", simple_str_concat(loop_var, simple_str_concat(" < ", simple_str_concat(iterable, simple_str_concat(".len; _idx_", simple_str_concat(loop_var, simple_str_concat("++) \{ ", simple_str_concat(sa_iter_elem, simple_str_concat(" ", simple_str_concat(loop_var, simple_str_concat(" = *(", simple_str_concat(sa_iter_elem, simple_str_concat("*)", simple_str_concat(iterable, simple_str_concat(".items[_idx_", simple_str_concat(loop_var, simple_str_concat("];
    // for item in struct.field (struct array field)
    }
    long long sf_iter_elem = is_struct_field_struct_array(iterable, types);
    if (strcmp(sf_iter_elem, "") != 0) {
        return simple_str_concat("for (long long _idx_", simple_str_concat(loop_var, simple_str_concat(" = 0; _idx_", simple_str_concat(loop_var, simple_str_concat(" < ", simple_str_concat(iterable, simple_str_concat(".len; _idx_", simple_str_concat(loop_var, simple_str_concat("++) \{ ", simple_str_concat(sf_iter_elem, simple_str_concat(" ", simple_str_concat(loop_var, simple_str_concat(" = *(", simple_str_concat(sf_iter_elem, simple_str_concat("*)", simple_str_concat(iterable, simple_str_concat(".items[_idx_", simple_str_concat(loop_var, simple_str_concat("];
    // for item in split result - detect .split( in iterable
    }
    if (simple_contains(iterable, ".split(")) {
        long long c_split = translate_expr(iterable, types);
        return simple_str_concat("\{ SimpleStringArray _split_", simple_str_concat(loop_var, simple_str_concat(" = ", simple_str_concat(c_split, simple_str_concat("; for (long long _idx_", simple_str_concat(loop_var, simple_str_concat(" = 0; _idx_", simple_str_concat(loop_var, simple_str_concat(" < _split_", simple_str_concat(loop_var, simple_str_concat(".len; _idx_", simple_str_concat(loop_var, simple_str_concat("++) \{ const char* ", simple_str_concat(loop_var, simple_str_concat(" = _split_", simple_str_concat(loop_var, simple_str_concat(".items[_idx_", simple_str_concat(loop_var, simple_str_concat("];
    // Default: integer array iteration
    }
    return simple_str_concat("for (long long _idx_", simple_str_concat(loop_var, simple_str_concat(" = 0; _idx_", simple_str_concat(loop_var, simple_str_concat(" < ", simple_str_concat(iterable, simple_str_concat("_len; _idx_", simple_str_concat(loop_var, simple_str_concat("++) \{ long long ", simple_str_concat(loop_var, simple_str_concat(" = ", simple_str_concat(iterable, simple_str_concat("[_idx_", simple_str_concat(loop_var, "];"))))))))))))));
}

const char* translate_case(const char* trimmed, const char* types) {
    const char* case_body = simple_substring(trimmed, 5, simple_strlen(trimmed) - 1);
    if (strcmp(case_body, "_") == 0) {
        return "/* default: */";
    }
    if (strcmp(case_body, "nil") == 0) {
        return "if (_match_val == NULL) \{";
    }
    if (simple_starts_with(case_body, "\"")) {
        return simple_str_concat("if (strcmp(_match_val, ", simple_str_concat(case_body, simple_str_concat(") == 0) ", "\{")));
    // Check for destructuring pattern: Variant(field1, field2)
    }
    long long dp_pos = simple_index_of(case_body, "(");
    if (dp_pos >= 0) {
        const char* variant_name = simple_substring(case_body, 0, dp_pos);
        long long dp_close = simple_index_of(case_body, ")");
        if (dp_close > dp_pos + 1) {
            const char* fields_str = simple_substring(case_body, dp_pos + 1, dp_close);
            SimpleStringArray fields = simple_split(fields_str, ",");
    // Generate tag check + field extraction
            const char* result = simple_str_concat("if (_match_val.tag == _match_type_TAG_", simple_str_concat(variant_name, ") \{"));
            long long fi = 0;
            for (long long _idx_field = 0; _idx_field < fields.len; _idx_field++) { const char* field = fields.items[_idx_field];
                const char* fname = simple_trim(field);
    // Check if named or positional
                long long fc = simple_index_of(fname, ":");
                if (fc >= 0) {
                    const char* fvar = simple_substring(fname, 0, fc);
                    result = simple_str_concat(result, simple_str_concat(" const char* ", simple_str_concat(fvar, simple_str_concat(" = _match_val.data.", simple_str_concat(variant_name, simple_str_concat(".", simple_str_concat(fvar, ";")))))));
                } else {
                    result = simple_str_concat(result, simple_str_concat(" const char* ", simple_str_concat(fname, simple_str_concat(" = _match_val.data.", simple_str_concat(variant_name, simple_str_concat("._", simple_str_concat(fi, ";")))))));
                }
                fi = fi + 1;
            }
            return result;
    // No fields - just tag check
        }
        return simple_str_concat("if (_match_val.tag == _match_type_TAG_", simple_str_concat(variant_name, ") \{"));
    // Check for Some(var) pattern
    }
    if (simple_starts_with(case_body, "Some(")) {
        const char* inner = simple_substring(case_body, 5, simple_strlen(case_body) - 1);
        return simple_str_concat("if (simple_option_has(_match_val)) \{ const char* ", simple_str_concat(inner, " = _match_val.str_val;"));
    // Check if case_body is an enum variant name
    }
    long long resolved = resolve_enum_variant(case_body, types);
    if (strcmp(resolved, "") != 0) {
        return simple_str_concat("if (_match_val == (long long)", simple_str_concat(resolved, simple_str_concat(") ", "\{")));
    }
    return simple_str_concat("if (_match_val == (long long)", simple_str_concat(case_body, simple_str_concat(") ", "\{")));
}

const char* translate_statement(const char* trimmed, const char* types) {
    // Skip module-system directives
    if (simple_starts_with(trimmed, "use ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "import ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "export ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "extern fn ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "from ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "pub mod ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "common use ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "export use ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (simple_starts_with(trimmed, "type ") && simple_contains(trimmed, " = ")) {
        return simple_str_concat("/* ", simple_str_concat(trimmed, " */"));
    }
    if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0) {
        return "/* pass */;";
    // Print
    }
    if (simple_starts_with(trimmed, "print ")) {
        const char* rest = simple_substring(trimmed, 6, simple_strlen(trimmed));
        return translate_print(rest, types);
    }
    if (strcmp(trimmed, "print") == 0) {
        return "puts(\"\");";
    // eprint -> fprintf(stderr, ...)
    }
    if (simple_starts_with(trimmed, "eprint ")) {
        const char* rest = simple_substring(trimmed, 7, simple_strlen(trimmed));
        if (simple_starts_with(rest, "\"") && simple_ends_with(rest, "\"")) {
            const char* inner = simple_substring(rest, 1, simple_strlen(rest) - 1);
            if (simple_contains(inner, "\{")) {
    // Reuse print interpolation logic but redirect to stderr
                const char* print_code = translate_interpolated_print(inner, types);
                return simple_replace(print_code, "printf(", "fprintf(stderr, ");
            }
            return simple_str_concat("fprintf(stderr, ", simple_str_concat("\"", simple_str_concat(inner, simple_str_concat("\n", "\");"))));
        }
        return simple_str_concat("fprintf(stderr, ", simple_str_concat("\"", simple_str_concat("%s\n", simple_str_concat("\",", simple_str_concat(translate_expr(rest, types), ");")))));
    // Tuple destructuring: val (a, b) = expr
    }
    if (simple_starts_with(trimmed, "val (") || simple_starts_with(trimmed, "var (")) {
        long long eq_idx = simple_index_of(trimmed, " = ");
        if (eq_idx >= 0) {
            const char* lhs = simple_substring(trimmed, 4, eq_idx);
            const char* rhs = simple_substring(trimmed, eq_idx + 3, simple_strlen(trimmed));
            if (simple_starts_with(lhs, "(") && simple_ends_with(lhs, ")")) {
                const char* inner = simple_substring(lhs, 1, simple_strlen(lhs) - 1);
                SimpleStringArray tparts = simple_split(inner, ",");
                long long c_rhs = translate_expr(rhs, types);
                if (tparts.len == 2) {
                    const char* v0 = simple_trim(tparts[0]);
                    const char* v1 = simple_trim(tparts[1]);
                    return simple_str_concat("SimpleTuple2 _tmp_tuple = ", simple_str_concat(c_rhs, simple_str_concat("; long long ", simple_str_concat(v0, simple_str_concat(" = (long long)_tmp_tuple._0; long long ", simple_str_concat(v1, " = (long long)_tmp_tuple._1;"))))));
                }
                if (tparts.len == 3) {
                    const char* v0 = simple_trim(tparts[0]);
                    const char* v1 = simple_trim(tparts[1]);
                    const char* v2 = simple_trim(tparts[2]);
                    return simple_str_concat("SimpleTuple3 _tmp_tuple = ", simple_str_concat(c_rhs, simple_str_concat("; long long ", simple_str_concat(v0, simple_str_concat(" = (long long)_tmp_tuple._0; long long ", simple_str_concat(v1, simple_str_concat(" = (long long)_tmp_tuple._1; long long ", simple_str_concat(v2, " = (long long)_tmp_tuple._2;"))))))));
    // Variable declarations
                }
            }
        }
    }
    if (simple_starts_with(trimmed, "val ") || simple_starts_with(trimmed, "var ")) {
        return translate_var_decl(trimmed, types);
    // Return
    }
    if (simple_starts_with(trimmed, "return ")) {
        const char* expr = simple_substring(trimmed, 7, simple_strlen(trimmed));
        if (strcmp(expr, "()") == 0) {
            return "return;";
        }
        if (strcmp(expr, "[]") == 0) {
            return "return simple_new_struct_array();";
    // Use translate_condition for expressions with and/or/comparisons
        }
        int has_and = simple_contains(expr, " and ");
        int has_or = simple_contains(expr, " or ");
        if (has_and || has_or) {
            return simple_str_concat("return ", simple_str_concat(translate_condition(expr, types), ";"));
        }
        return simple_str_concat("return ", simple_str_concat(translate_expr(expr, types), ";"));
    }
    if (strcmp(trimmed, "return") == 0) {
        return "return;";
    }
    if (strcmp(trimmed, "return ()") == 0) {
        return "return;";
    // Control flow
    }
    if (simple_starts_with(trimmed, "if ") && simple_ends_with(trimmed, ":")) {
        const char* cond = simple_substring(trimmed, 3, simple_strlen(trimmed) - 1);
        return simple_str_concat("if (", simple_str_concat(translate_condition(cond, types), simple_str_concat(") ", "\{")));
    // Inline if: "if cond: statement" (single-line if)
    }
    if (simple_starts_with(trimmed, "if ") && !(simple_ends_with(trimmed, ":"))) {
        long long if_colon = simple_index_of(trimmed, ":");
        if (if_colon >= 0) {
            const char* if_cond = simple_substring(trimmed, 3, if_colon);
            const char* if_body = simple_substring(trimmed, if_colon + 1, simple_strlen(trimmed));
            long long c_cond = translate_condition(if_cond, types);
            const char* body_result = translate_statement(if_body, types);
    // Don't include implicit return from body
            const char* c_body = body_result;
            long long pipe_pos = simple_index_of(c_body, "
            if (pipe_pos >= 0) {
                c_body = simple_substring(c_body, 0, pipe_pos);
            }
            return simple_str_concat("if (", simple_str_concat(c_cond, simple_str_concat(") \{ ", simple_str_concat(c_body, " }"))));
        }
    }
    if (simple_starts_with(trimmed, "elif ") && simple_ends_with(trimmed, ":")) {
        const char* cond = simple_substring(trimmed, 5, simple_strlen(trimmed) - 1);
        return simple_str_concat("} else if (", simple_str_concat(translate_condition(cond, types), simple_str_concat(") ", "\{")));
    }
    if (strcmp(trimmed, "else:") == 0) {
        return "} else \{";
    // Loops
    }
    if (simple_starts_with(trimmed, "for ") && simple_ends_with(trimmed, ":")) {
        return translate_for_loop(trimmed, types);
    // Match/case
    }
    if (simple_starts_with(trimmed, "match ") && simple_ends_with(trimmed, ":")) {
        const char* match_expr = simple_substring(trimmed, 6, simple_strlen(trimmed) - 1);
        long long c_match_expr = translate_expr(match_expr, types);
    // Detect string vs integer match
        if (is_text_var(match_expr, types)) {
            return simple_str_concat("\{ const char* _match_val = ", simple_str_concat(c_match_expr, ";"));
        }
        return simple_str_concat("\{ long long _match_val = ", simple_str_concat(c_match_expr, ";"));
    }
    if (simple_starts_with(trimmed, "case ") && simple_ends_with(trimmed, ":")) {
        return translate_case(trimmed, types);
    // Inline case: case PATTERN: body_expr
    }
    if (simple_starts_with(trimmed, "case ")) {
        long long case_colon = simple_index_of(trimmed, ":");
        if (case_colon >= 0) {
            const char* case_pattern = simple_substring(trimmed, 5, case_colon);
            const char* case_inline_body = simple_substring(trimmed, case_colon + 1, simple_strlen(trimmed));
    // Build the if-check for the pattern
            const char* case_check_trimmed = simple_str_concat("case ", simple_str_concat(case_pattern, ":"));
            const char* case_check = translate_case(case_check_trimmed, types);
            const char* case_if = case_check;
            if (simple_ends_with(case_if, "\{")) {
                case_if = simple_substring(case_if, 0, simple_strlen(case_if) - 1);
    // Check if body is an assignment (statement) vs expression
            }
            long long body_eq_pos = simple_index_of(case_inline_body, " = ");
            int body_is_assignment = body_eq_pos >= 0 && !(simple_starts_with(case_inline_body, "\""));
            if (body_is_assignment) {
    // Translate as statement (not expression)
                const char* case_stmt_raw = translate_statement(case_inline_body, types);
    // Extract code part only (strip type annotations after <|TYPE|>)
                long long case_sep = simple_index_of(case_stmt_raw, "
                const char* case_stmt_code = case_stmt_raw;
                if (case_sep >= 0) {
                    case_stmt_code = simple_substring(case_stmt_raw, 0, case_sep);
                }
                return simple_str_concat(case_if, simple_str_concat(" \{ ", simple_str_concat(case_stmt_code, " }")));
    // Translate the body expression
            }
            long long case_body_c = translate_expr(case_inline_body, types);
            return simple_str_concat(case_if, simple_str_concat(" \{ return ", simple_str_concat(case_body_c, "; }")));
        }
    }
    if (strcmp(trimmed, "break") == 0) {
        return "break;";
    }
    if (strcmp(trimmed, "continue") == 0) {
        return "continue;";
    }
    if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0) {
        return "/* pass */;";
    // Method calls as statements (e.g., arr.push("x"))
    }
    long long push_pos = simple_index_of(trimmed, ".push(");
    if (push_pos >= 0) {
        const char* obj = simple_substring(trimmed, 0, push_pos);
        long long arg_start = push_pos + 6;
        long long arg_end = find_close_paren(trimmed, arg_start - 1);
        if (arg_end >= 0) {
            const char* arg = simple_substring(trimmed, arg_start, arg_end);
            if (is_string_array_var(obj, types)) {
                return simple_str_concat("simple_string_push(&", simple_str_concat(obj, simple_str_concat(", ", simple_str_concat(translate_expr(arg, types), ");"))));
            }
            if (is_int_array_var(obj, types)) {
                return simple_str_concat("simple_int_push(&", simple_str_concat(obj, simple_str_concat(", ", simple_str_concat(translate_expr(arg, types), ");"))));
            }
            if (is_str_arr_arr_var(obj, types)) {
                long long push_arg = translate_expr(arg, types);
                if (strcmp(arg, "[]") == 0) {
                    push_arg = "simple_new_string_array()";
                }
                return simple_str_concat("simple_string_array_push(&", simple_str_concat(obj, simple_str_concat(", ", simple_str_concat(push_arg, ");"))));
            }
            if (is_int_arr_arr_var(obj, types)) {
                long long push_arg = translate_expr(arg, types);
                if (strcmp(arg, "[]") == 0) {
                    push_arg = "simple_new_int_array()";
                }
                return simple_str_concat("simple_int_array_push(&", simple_str_concat(obj, simple_str_concat(", ", simple_str_concat(push_arg, ");"))));
    // Check struct array: arr.push(item)
            }
            long long sa_push_elem = is_struct_array_var(obj, types);
            if (strcmp(sa_push_elem, "") != 0) {
                long long c_arg = translate_expr(arg, types);
                return simple_str_concat("\{ ", simple_str_concat(sa_push_elem, simple_str_concat("* _e = malloc(sizeof(", simple_str_concat(sa_push_elem, simple_str_concat(")); *_e = ", simple_str_concat(c_arg, simple_str_concat("; simple_struct_push(&", simple_str_concat(obj, ", (void*)_e); }"))))))));
    // Check struct field arrays: table.names.push(x)
            }
            if (is_struct_field_str_array(obj, types)) {
                return simple_str_concat("simple_string_push(&", simple_str_concat(obj, simple_str_concat(", ", simple_str_concat(translate_expr(arg, types), ");"))));
            }
            if (is_struct_field_int_array(obj, types)) {
                return simple_str_concat("simple_int_push(&", simple_str_concat(obj, simple_str_concat(", ", simple_str_concat(translate_expr(arg, types), ");"))));
            }
            return simple_str_concat("/* ", simple_str_concat(trimmed, " */;"));
    // .pop() as statement
        }
    }
    if (simple_ends_with(trimmed, ".pop()")) {
        const char* obj = simple_substring(trimmed, 0, simple_strlen(trimmed) - 6);
        if (is_string_array_var(obj, types)) {
            return simple_str_concat("simple_string_pop(&", simple_str_concat(obj, ");"));
        }
        if (is_int_array_var(obj, types)) {
            return simple_str_concat("simple_int_pop(&", simple_str_concat(obj, ");"));
    // Compound assignment
        }
    }
    long long plus_eq = simple_index_of(trimmed, " += ");
    if (plus_eq >= 0) {
        const char* lhs = simple_substring(trimmed, 0, plus_eq);
        const char* rhs = simple_substring(trimmed, plus_eq + 4, simple_strlen(trimmed));
    // String concatenation assignment
        if (is_text_var(lhs, types)) {
            return simple_str_concat(lhs, simple_str_concat(" = simple_str_concat(", simple_str_concat(lhs, simple_str_concat(", ", simple_str_concat(translate_expr(rhs, types), ");")))));
        }
        return simple_str_concat(lhs, simple_str_concat(" += ", simple_str_concat(translate_expr(rhs, types), ";")));
    }
    SimpleStringArray compound_ops = simple_new_string_array(); simple_string_push(&compound_ops, " -= "); simple_string_push(&compound_ops, " *= "); simple_string_push(&compound_ops, " /= ");
    for (long long _idx_cop = 0; _idx_cop < compound_ops.len; _idx_cop++) { const char* cop = compound_ops.items[_idx_cop];
        long long cop_result = try_translate_compound_assign(trimmed, cop, types);
        if (strcmp(cop_result, "") != 0) {
            return cop_result;
    // Variable assignment
        }
    }
    long long eq_idx = simple_index_of(trimmed, " = ");
    if (eq_idx >= 0) {
        const char* lhs = simple_substring(trimmed, 0, eq_idx);
        const char* rhs = simple_substring(trimmed, eq_idx + 3, simple_strlen(trimmed));
    // Dict indexing assignment: d[key] = value
        long long lhs_bracket = simple_index_of(lhs, "[");
        if (lhs_bracket >= 0) {
            const char* dict_name = simple_substring(lhs, 0, lhs_bracket);
            if (is_dict_var(dict_name, types)) {
                long long lhs_close = simple_index_of(lhs, "]");
                if (lhs_close > lhs_bracket + 1) {
                    const char* key_expr = simple_substring(lhs, lhs_bracket + 1, lhs_close);
                    long long c_rhs = translate_expr(rhs, types);
                    long long c_key = translate_expr(key_expr, types);
    // Detect value type
                    long long rhs_is_str = simple_starts_with(rhs, "\"");
                    long long rhs_text = is_text_var(rhs, types);
                    if (rhs_is_str || rhs_text) {
                        return simple_str_concat("simple_dict_set_str(", simple_str_concat(dict_name, simple_str_concat(", ", simple_str_concat(c_key, simple_str_concat(", ", simple_str_concat(c_rhs, ");"))))));
                    }
                    return simple_str_concat("simple_dict_set_int(", simple_str_concat(dict_name, simple_str_concat(", ", simple_str_concat(c_key, simple_str_concat(", ", simple_str_concat(c_rhs, ");"))))));
    // Array element assignment: arr[idx] = value -> arr.items[idx] = value
                }
            }
        }
        if (lhs_bracket >= 0) {
            const char* arr_name = simple_substring(lhs, 0, lhs_bracket);
            long long arr_is_int = is_int_array_var(arr_name, types);
            long long arr_is_str = is_string_array_var(arr_name, types);
            long long arr_is_iaa = is_int_arr_arr_var(arr_name, types);
            long long arr_is_saa = is_str_arr_arr_var(arr_name, types);
            int arr_is_any = arr_is_int || arr_is_str || arr_is_iaa || arr_is_saa;
            if (arr_is_any) {
                long long lhs_close = simple_index_of(lhs, "]");
                if (lhs_close > lhs_bracket + 1) {
                    const char* idx_expr = simple_substring(lhs, lhs_bracket + 1, lhs_close);
                    long long c_idx = translate_expr(idx_expr, types);
                    long long c_rhs = translate_expr(rhs, types);
                    return simple_str_concat(arr_name, simple_str_concat(".items[", simple_str_concat(c_idx, simple_str_concat("] = ", simple_str_concat(c_rhs, ";")))));
    // Struct field assignment: obj.field = value
                }
            }
        }
        long long lhs_dot = simple_index_of(lhs, ".");
        if (lhs_dot >= 0) {
            const char* lhs_obj = simple_substring(lhs, 0, lhs_dot);
            const char* lhs_field = simple_substring(lhs, lhs_dot + 1, simple_strlen(lhs));
            long long lhs_class = is_struct_type_var(lhs_obj, types);
            if (strcmp(lhs_class, "") != 0) {
                long long c_rhs = translate_expr(rhs, types);
                return simple_str_concat(lhs_obj, simple_str_concat(".", simple_str_concat(lhs_field, simple_str_concat(" = ", simple_str_concat(c_rhs, ";")))));
            }
        }
        int no_space = !(simple_contains(lhs, " "));
        int no_paren = !(simple_starts_with(lhs, "("));
        if (no_space && no_paren) {
    // Handle array reset: arr = []
            if (strcmp(rhs, "[]") == 0) {
                if (is_str_arr_arr_var(lhs, types)) {
                    return simple_str_concat(lhs, " = simple_new_string_array_array();");
                }
                if (is_int_arr_arr_var(lhs, types)) {
                    return simple_str_concat(lhs, " = simple_new_int_array_array();");
                }
                if (is_string_array_var(lhs, types)) {
                    return simple_str_concat(lhs, " = simple_new_string_array();");
                }
                if (is_int_array_var(lhs, types)) {
                    return simple_str_concat(lhs, " = simple_new_int_array();");
                }
                if (strcmp(is_struct_array_var(lhs, types), "") != 0) {
                    return simple_str_concat(lhs, " = simple_new_struct_array();");
                }
                return simple_str_concat(lhs, " = simple_new_int_array();");
    // Handle array concat: arr = arr + [elem] -> direct push (optimization)
            }
            long long rhs_concat_pos = simple_index_of(rhs, " + [");
            if (rhs_concat_pos >= 0 && simple_ends_with(rhs, "]")) {
                const char* arr_part = simple_substring(rhs, 0, rhs_concat_pos);
                const char* concat_elem = simple_substring(rhs, rhs_concat_pos + 4, simple_strlen(rhs) - 1);
                if (strcmp(arr_part, lhs) == 0) {
                    long long sa_concat_type = is_struct_array_var(lhs, types);
                    if (strcmp(sa_concat_type, "") != 0) {
                        long long c_concat_elem = translate_expr(concat_elem, types);
                        return simple_str_concat("\{ ", simple_str_concat(sa_concat_type, simple_str_concat("* _e = malloc(sizeof(", simple_str_concat(sa_concat_type, simple_str_concat(")); *_e = ", simple_str_concat(c_concat_elem, simple_str_concat("; simple_struct_push(&", simple_str_concat(lhs, ", (void*)_e); }"))))))));
                    }
                    if (is_int_array_var(lhs, types)) {
                        return simple_str_concat("simple_int_push(&", simple_str_concat(lhs, simple_str_concat(", ", simple_str_concat(translate_expr(concat_elem, types), ");"))));
                    }
                    if (is_string_array_var(lhs, types)) {
                        return simple_str_concat("simple_string_push(&", simple_str_concat(lhs, simple_str_concat(", ", simple_str_concat(translate_expr(concat_elem, types), ");"))));
                    }
                }
            }
            long long c_rhs = translate_expr(rhs, types);
    // Track if assigning a string to a var (e.g., name = "Alice")
            long long rhs_is_str = simple_starts_with(rhs, "\"");
            long long rhs_is_text = simple_contains(c_rhs, "simple_");
            if (rhs_is_str || rhs_is_text) {
                return simple_str_concat(lhs, simple_str_concat(" = ", simple_str_concat(c_rhs, simple_str_concat(";
            }
            return simple_str_concat(lhs, simple_str_concat(" = ", simple_str_concat(c_rhs, ";")));
    // While loop
        }
    }
    if (simple_starts_with(trimmed, "while ") && simple_ends_with(trimmed, ":")) {
        const char* cond = simple_substring(trimmed, 6, simple_strlen(trimmed) - 1);
        return simple_str_concat("while (", simple_str_concat(translate_condition(cond, types), simple_str_concat(") ", "\{")));
    // Function call as statement - detect BEFORE comparison/logic check
    // to avoid treating comparison operators inside function arguments as bare comparisons
    // e.g., check_eq_bool("5 > 3", 5 > 3, true) should NOT be treated as a comparison
    }
    long long paren_pos = simple_index_of(trimmed, "(");
    if (paren_pos >= 0 && simple_ends_with(trimmed, ")")) {
        const char* fn_part = simple_substring(trimmed, 0, paren_pos);
    // If the part before ( is a simple name (no spaces = no operators), it's a function call
        long long fn_has_space = simple_contains(fn_part, " ");
        if (!(fn_has_space && simple_strlen(fn_part) > 0)) {
            return simple_str_concat(translate_expr(trimmed, types), ";");
    // Bare expression as implicit return (e.g., last line of function body)
    // Handle comparison/logical expressions: a == b, a and b, a or b, etc.
        }
    }
    int has_cmp = simple_contains(trimmed, " == ") || simple_contains(trimmed, " != ") || simple_contains(trimmed, " < ") || simple_contains(trimmed, " > ") || simple_contains(trimmed, " <= ") || simple_contains(trimmed, " >= ");
    int has_logic = simple_contains(trimmed, " and ") || simple_contains(trimmed, " or ") || simple_starts_with(trimmed, "not ");
    if (has_cmp || has_logic) {
        return simple_str_concat("return ", simple_str_concat(translate_condition(trimmed, types), ";"));
    }
    long long c_expr = translate_expr(trimmed, types);
    if (strcmp(c_expr, trimmed) != 0) {
    // Expression was translated to something different - use as return
        return simple_str_concat("return ", simple_str_concat(c_expr, ";"));
    // Simple variable reference or literal - implicit return
    }
    int is_simple_var = !(simple_contains(trimmed, " "));
    long long is_bracket = simple_contains(trimmed, "[");
    long long is_dot = simple_contains(trimmed, ".");
    if (is_simple_var || is_bracket || is_dot) {
        return simple_str_concat("return ", simple_str_concat(c_expr, ";"));
    // Arithmetic expressions with spaces (e.g., "a + b", "-1")
    }
    int is_arith = simple_contains(trimmed, " + ") || simple_contains(trimmed, " - ") || simple_contains(trimmed, " * ") || simple_contains(trimmed, " / ") || simple_starts_with(trimmed, "-");
    if (is_arith) {
        return simple_str_concat("return ", simple_str_concat(c_expr, ";"));
    }
    return simple_str_concat("/* unsupported: ", simple_str_concat(trimmed, " */"));
}

int main(void) {
    return 0;
}

