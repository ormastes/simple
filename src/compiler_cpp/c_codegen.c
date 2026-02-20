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
const char* generate_c_code(const char* source_text);

const char* generate_c_code(const char* source_text) {
    //  Type registry - tracks variable types and function return types
    //  Format: ";text:name;arr:name;fn_text:funcname;struct:StructName;"
    const char* types = ";";
    //  Pre-seed well-known cross-module variables (used by parser, lexer, etc.)
    types = simple_str_concat(types, "text:par_text;text:par_current;text:lex_cur_text;text:lex_cur_suffix;");
    types = simple_str_concat(types, "text:g_log_filter_pattern;");
    SimpleStringArray raw_lines = simple_split(source_text, "\n");
    //  Pre-process: join multi-line expressions (unclosed parentheses)
    SimpleIntArray lines_arr = simple_new_int_array();
    const char* pending_line = "";
    long long paren_depth = 0;
    for (long long li = 0; li <  raw_lines.len; li++) {
        long long rline = raw_lines[li];
        if (strcmp(pending_line, "") != 0) {
            pending_line = simple_str_concat(pending_line, simple_str_concat(" ", simple_trim(rline)));
        } else {
            pending_line = rline;
    //  Count parens outside string literals and comments
        }
        int has_paren = simple_contains(rline, "(") || simple_contains(rline, ")");
        if (has_paren) {
            int pp_in_str = 0;
            long long pp_opens = 0;
            long long pp_closes = 0;
            long long pp_i = 0;
            long long pp_len = rline.len;
            while (pp_i < pp_len) {
                const char* pp_ch = simple_substring(rline, pp_i, pp_i + 1);
                if (pp_in_str) {
                    if (strcmp(pp_ch, "\\") == 0 && pp_i + 1 < pp_len) {
                        pp_i = pp_i + 2;
                        continue;
                    }
                    if (strcmp(pp_ch, "\"") == 0) {
                        pp_in_str = 0;
                    }
                    pp_i = pp_i + 1;
                    continue;
    //  Stop at comment (# outside of string = rest is comment)
                }
                if (strcmp(pp_ch, "#") == 0) {
                    pp_i = pp_len;
                    continue;
                }
                if (strcmp(pp_ch, "\"") == 0) {
                    pp_in_str = 1;
                    pp_i = pp_i + 1;
                    continue;
                }
                if (strcmp(pp_ch, "(") == 0) {
                    pp_opens = pp_opens + 1;
                } else if (strcmp(pp_ch, ")") == 0) {
                    pp_closes = pp_closes + 1;
                }
                pp_i = pp_i + 1;
            }
            paren_depth = paren_depth + pp_opens - pp_closes;
        }
        if (paren_depth <= 0) {
            /* lines_arr.push(pending_line) */;
            pending_line = "";
            paren_depth = 0;
        }
    }
    if (strcmp(pending_line, "") != 0) {
        /* lines_arr.push(pending_line) */;
    }
    SimpleIntArray forward_decls = simple_new_int_array();
    SimpleIntArray func_defs = simple_new_int_array();
    SimpleIntArray struct_defs = simple_new_int_array();
    SimpleIntArray enum_defs = simple_new_int_array();
    SimpleIntArray global_defs = simple_new_int_array();
    SimpleIntArray main_body = simple_new_int_array();
    const char* current_fn_name = "";
    SimpleIntArray current_fn_lines = simple_new_int_array();
    const char* current_fn_sig = "";
    const char* types_before_fn = "";
    int in_main = 0;
    int in_func = 0;
    int in_struct = 0;
    int in_enum = 0;
    int skip_until_unindent = 0;
    const char* current_impl_class = "";
    int in_impl = 0;
    int in_impl_method = 0;
    const char* impl_method_name = "";
    const char* impl_method_sig = "";
    SimpleIntArray impl_method_lines = simple_new_int_array();
    int impl_method_is_me = 0;
    long long lambda_counter = 0;
    int skip_until_close_brace = 0;
    //  Pre-pass: collect all struct/class/enum names and field types
    //  This resolves forward references (e.g., impl using struct defined later)
    int pre_skip = 0;
    for (long long pi = 0; pi <  lines_arr.len; pi++) {
        long long pline = lines_arr[pi];
        const char* ptrim = simple_trim(pline);
        if (strcmp(ptrim, "") == 0) {
            continue;
        }
        int p_is_struct = simple_starts_with(ptrim, "struct ") && simple_ends_with(ptrim, ":");
        int p_is_class = simple_starts_with(ptrim, "class ") && simple_ends_with(ptrim, ":");
        int p_is_enum = simple_starts_with(ptrim, "enum ") && simple_ends_with(ptrim, ":");
        if (p_is_struct || p_is_class) {
            const char* p_name = "";
            if (p_is_struct) {
                p_name = simple_substring(ptrim, 7, simple_strlen(ptrim) - 1);
            } else {
                p_name = simple_substring(ptrim, 6, simple_strlen(ptrim) - 1);
            }
            types = simple_str_concat(types, simple_str_concat("struct:", simple_str_concat(p_name, ";")));
    //  Scan fields
            for (long long pfi = pi + 1; pfi <  lines_arr.len; pfi++) {
                long long pfline = lines_arr[pfi];
                const char* pftrim = simple_trim(pfline);
                if (strcmp(pftrim, "") == 0) {
                    continue;
                }
                int pf_ind = simple_starts_with(pfline, "    ") || simple_starts_with(pfline, "\t");
                if (!(pf_ind)) {
                    break;
                }
                if (simple_starts_with(pftrim, "fn ") || simple_starts_with(pftrim, "me ") || simple_starts_with(pftrim, "static fn ")) {
                    break;
                }
                if (simple_starts_with(pftrim, "#")) {
                    continue;
    //  Strip inline comments
                }
                const char* pf_clean = pftrim;
                long long pf_hash = simple_index_of(pftrim, " #");
                if (pf_hash >= 0) {
                    pf_clean = simple_substring(pftrim, 0, pf_hash);
                }
                long long pf_colon = simple_index_of(pf_clean, ":");
                if (pf_colon >= 0) {
                    const char* pf_fname = simple_substring(pf_clean, 0, pf_colon);
                    const char* pf_ftype = simple_substring(pf_clean, pf_colon + 1, simple_strlen(pf_clean));
                    if (strcmp(pf_ftype, "text") == 0 || strcmp(pf_ftype, "str") == 0) {
                        types = simple_str_concat(types, simple_str_concat("field_text:", simple_str_concat(p_name, simple_str_concat(".", simple_str_concat(pf_fname, ";")))));
                    }
                    if (strcmp(pf_ftype, "[text]") == 0 || strcmp(pf_ftype, "[str]") == 0) {
                        types = simple_str_concat(types, simple_str_concat("field_arr:", simple_str_concat(p_name, simple_str_concat(".", simple_str_concat(pf_fname, ";")))));
                    }
                    if (strcmp(pf_ftype, "[i64]") == 0 || strcmp(pf_ftype, "[int]") == 0 || strcmp(pf_ftype, "[bool]") == 0) {
                        types = simple_str_concat(types, simple_str_concat("field_int_arr:", simple_str_concat(p_name, simple_str_concat(".", simple_str_concat(pf_fname, ";")))));
    //  Struct array field: [StructName]
                    }
                    if (simple_starts_with(pf_ftype, "[") && simple_ends_with(pf_ftype, "]")) {
                        const char* pf_elem = simple_substring(pf_ftype, 1, simple_strlen(pf_ftype) - 1);
                        if (simple_strlen(pf_elem) > 0) {
                            const char* pf_ef = simple_char_at(pf_elem, 0);
                            if (pf_ef >= "A" && pf_ef <= "Z") {
                                types = simple_str_concat(types, simple_str_concat("field_struct_arr:", simple_str_concat(p_name, simple_str_concat(".", simple_str_concat(pf_fname, simple_str_concat("=", simple_str_concat(pf_elem, ";")))))));
                            }
                        }
                    }
                }
            }
        }
        if (p_is_enum) {
            const char* pe_name = simple_substring(ptrim, 5, simple_strlen(ptrim) - 1);
    //  Scan variants
            for (long long pei = pi + 1; pei <  lines_arr.len; pei++) {
                long long peline = lines_arr[pei];
                const char* petrim = simple_trim(peline);
                if (strcmp(petrim, "") == 0) {
                    continue;
                }
                int pe_ind = simple_starts_with(peline, "    ") || simple_starts_with(peline, "\t");
                if (!(pe_ind)) {
                    break;
                }
                if (simple_starts_with(petrim, "#") || simple_starts_with(petrim, "fn ") || simple_starts_with(petrim, "me ")) {
                    continue;
                }
                long long pe_paren = simple_index_of(petrim, "(");
                const char* pe_vname = petrim;
                if (pe_paren >= 0) {
                    pe_vname = simple_substring(petrim, 0, pe_paren);
                }
                types = simple_str_concat(types, simple_str_concat("enum_variant:", simple_str_concat(pe_name, simple_str_concat(".", simple_str_concat(pe_vname, ";")))));
    //  Pre-pass 2: collect all function return types (resolves forward references)
            }
        }
    }
    for (long long fp_i = 0; fp_i <  lines_arr.len; fp_i++) {
        const char* fp_line = simple_trim(lines_arr[fp_i]);
        if (simple_starts_with(fp_line, "fn ") && simple_ends_with(fp_line, ":")) {
            long long fp_paren = simple_index_of(fp_line, "(");
            if (fp_paren >= 0) {
                const char* fp_name = simple_substring(fp_line, 3, fp_paren);
                types = simple_str_concat(types, cg_track_fn_types(fp_line, fp_name));
            }
        }
    }
    for (long long line_idx = 0; line_idx <  lines_arr.len; line_idx++) {
        long long line = lines_arr[line_idx];
        const char* trimmed = simple_trim(line);
        if (strcmp(trimmed, "") == 0) {
            continue;
    //  Skip lines inside multi-line import blocks (pub use ... { ... })
        }
        if (skip_until_close_brace) {
            if (strcmp(trimmed, "}") == 0 || simple_ends_with(trimmed, "}")) {
                skip_until_close_brace = 0;
            }
            continue;
    //  Strip inline comments: code # comment (but not inside strings)
    //  Handle both "code  # comment" and "code # comment"
        }
        if (simple_contains(trimmed, " #") && !(simple_starts_with(trimmed, "#"))) {
            long long inline_hash = simple_index_of(trimmed, " #");
            if (inline_hash >= 0) {
    //  Make sure it's not inside a string literal
                const char* before_hash = simple_substring(trimmed, 0, inline_hash);
                SimpleStringArray quote_count = simple_split(before_hash, simple_strlen("\""));
                long long is_inside_str = quote_count % 2 == 1;
    //  Also check it's not a #[ decorator or #! shebang
                const char* after_hash = simple_substring(trimmed, inline_hash + 2, simple_strlen(trimmed));
                long long is_decorator = simple_starts_with(after_hash, "[");
                if (!(is_inside_str && !(is_decorator))) {
                    trimmed = simple_trim(before_hash);
                }
            }
        }
        if (simple_starts_with(trimmed, "#!")) {
            continue;
        }
        if (simple_starts_with(trimmed, "#")) {
            const char* comment_text = simple_substring(trimmed, 1, simple_strlen(trimmed));
            int comment_indented = simple_starts_with(line, "    ") || simple_starts_with(line, "\t");
            if (in_main && comment_indented) {
                /* main_body.push(r"    // " + comment_text) */;
            } else if (in_func && comment_indented) {
                /* current_fn_lines.push(r"    // " + comment_text) */;
            } else if (in_func && !(comment_indented)) {
    //  Top-level comment while in_func - end the function
                long long fn_code = build_function(current_fn_name, current_fn_sig, current_fn_lines);
                /* func_defs.push(fn_code) */;
                current_fn_lines = simple_new_int_array();
                in_func = 0;
                types = types_before_fn;
            }
            continue;
    //  Handle impl block methods - indented lines inside impl
        }
        if (in_impl) {
            long long still_indented = simple_starts_with(line, "    ");
            long long is_tab = simple_starts_with(line, "\t");
            if (!(still_indented && !(is_tab))) {
    //  End of impl block - flush any pending method
                if (in_impl_method) {
                    const char* method_code = build_function(simple_str_concat(current_impl_class, simple_str_concat("__", impl_method_name)), impl_method_sig, impl_method_lines);
                    /* func_defs.push(method_code) */;
                    impl_method_lines = simple_new_int_array();
                    in_impl_method = 0;
                }
                in_impl = 0;
                current_impl_class = "";
    //  Fall through to process current line normally
            } else {
    //  Inside impl block
                long long impl_indent = get_indent_level(line);
                if (impl_indent == 1) {
    //  Top-level impl member (fn, me, static fn)
                    if (in_impl_method) {
                        const char* method_code = build_function(simple_str_concat(current_impl_class, simple_str_concat("__", impl_method_name)), impl_method_sig, impl_method_lines);
                        /* func_defs.push(method_code) */;
                        impl_method_lines = simple_new_int_array();
                        in_impl_method = 0;
                    }
                    if (simple_starts_with(trimmed, "fn ") && simple_ends_with(trimmed, ":")) {
                        long long parsed = parse_method_signature(trimmed, current_impl_class, 0);
                        impl_method_name = parsed[0];
                        impl_method_sig = parsed[1];
                        long long fwd = parsed[2];
                        /* forward_decls.push(fwd) */;
                        in_impl_method = 1;
                        impl_method_is_me = 0;
                        types = simple_str_concat(types, simple_str_concat("method:", simple_str_concat(current_impl_class, simple_str_concat(".", simple_str_concat(impl_method_name, ";")))));
                        types = simple_str_concat(types, simple_str_concat("struct_var:self=", simple_str_concat(current_impl_class, ";")));
                        types = simple_str_concat(types, cg_track_fn_types(trimmed, simple_str_concat(current_impl_class, simple_str_concat("__", impl_method_name))));
                        continue;
                    } else if (simple_starts_with(trimmed, "me ") && simple_ends_with(trimmed, ":")) {
                        long long parsed = parse_method_signature(trimmed, current_impl_class, 1);
                        impl_method_name = parsed[0];
                        impl_method_sig = parsed[1];
                        long long fwd = parsed[2];
                        /* forward_decls.push(fwd) */;
                        in_impl_method = 1;
                        impl_method_is_me = 1;
                        types = simple_str_concat(types, simple_str_concat("me_method:", simple_str_concat(current_impl_class, simple_str_concat(".", simple_str_concat(impl_method_name, ";")))));
                        types = simple_str_concat(types, simple_str_concat("struct_var:self=", simple_str_concat(current_impl_class, ";")));
                        types = simple_str_concat(types, cg_track_fn_types(trimmed, simple_str_concat(current_impl_class, simple_str_concat("__", impl_method_name))));
                        continue;
                    } else if (simple_starts_with(trimmed, "static fn ") && simple_ends_with(trimmed, ":")) {
    //  Static method - no self parameter
                        const char* static_trimmed = simple_str_concat("fn ", simple_substring(trimmed, 10, simple_strlen(trimmed)));
                        long long parsed = parse_fn_signature(static_trimmed);
                        long long static_method_name = parsed[0];
                        const char* mangled_name = simple_str_concat(current_impl_class, simple_str_concat("__", static_method_name));
    //  Re-parse with mangled name
                        const char* static_sig_trimmed = simple_replace(static_trimmed, static_method_name + "(", mangled_name + "(");
                        long long parsed2 = parse_fn_signature(static_sig_trimmed);
                        impl_method_name = static_method_name;
                        impl_method_sig = parsed2[1];
                        /* forward_decls.push(parsed2[2]) */;
                        in_impl_method = 1;
                        impl_method_is_me = 0;
                        types = simple_str_concat(types, simple_str_concat("static_fn:", simple_str_concat(current_impl_class, simple_str_concat(".", simple_str_concat(static_method_name, ";")))));
                        types = simple_str_concat(types, cg_track_fn_types(trimmed, mangled_name));
                        continue;
                    } else {
    //  Skip other impl-level lines (comments etc)
                        continue;
                    }
                } else if (impl_indent >= 2 && in_impl_method) {
    //  Method body line - translate with self context
                    long long raw_result = translate_statement(trimmed, types);
                    long long parts = split_result(raw_result);
                    long long code = parts[0];
                    long long new_types = parts[1];
                    if (strcmp(new_types, "") != 0) {
                        types = simple_str_concat(types, new_types);
    //  Replace self.method(args) calls before generic self. replacement
                    }
                    if (simple_contains(code, "self.")) {
                        long long sm_pos = simple_index_of(code, "self.");
                        if (sm_pos >= 0) {
                            const char* sm_after = simple_substring(code, sm_pos + 5, simple_strlen(code));
                            long long sm_paren = simple_index_of(sm_after, "(");
                            long long sm_dot2 = simple_index_of(sm_after, ".");
                            long long sm_space = simple_index_of(sm_after, " ");
                            long long sm_eq = simple_index_of(sm_after, "=");
    //  Is this a method call? (paren comes before dot/space/eq)
                            long long sm_is_call = sm_paren >= 0;
                            if (sm_is_call && sm_dot2 >= 0 && sm_dot2 < sm_paren) {
                                sm_is_call = 0;
                            }
                            if (sm_is_call && sm_space >= 0 && sm_space < sm_paren) {
                                sm_is_call = 0;
                            }
                            if (sm_is_call && sm_eq >= 0 && sm_eq < sm_paren) {
                                sm_is_call = 0;
                            }
                            if (sm_is_call) {
                                const char* sm_name = simple_substring(sm_after, 0, sm_paren);
                                long long sm_close = find_close_paren(sm_after, sm_paren);
                                if (sm_close >= 0) {
                                    const char* sm_args = "";
                                    if (sm_close > sm_paren + 1) {
                                        sm_args = simple_substring(sm_after, sm_paren + 1, sm_close);
                                    }
                                    const char* sm_rest = "";
                                    if (sm_close + 1 < simple_strlen(sm_after)) {
                                        sm_rest = simple_substring(sm_after, sm_close + 1, simple_strlen(sm_after));
                                    }
                                    const char* sm_before = simple_substring(code, 0, sm_pos);
                                    if (strcmp(sm_args, "") != 0) {
                                        code = simple_str_concat(sm_before, simple_str_concat(current_impl_class, r"__" + sm_name + r"(&self, " + sm_args + r")" + sm_rest));
                                    } else {
                                        code = simple_str_concat(sm_before, simple_str_concat(current_impl_class, r"__" + sm_name + r"(&self)" + sm_rest));
    //  Replace self.field access/assignment inside method bodies
                                    }
                                }
                            }
                        }
                    }
                    if (simple_contains(code, "self.")) {
                        code = simple_replace(code, "self.", "self->");
                    }
                    if (strcmp(code, "") != 0) {
                        const char* padding = "";
                        for (long long pi = 0; pi <  impl_indent - 1; pi++) {
                            padding = simple_str_concat(padding, "    ");
                        /* impl_method_lines.push(padding + code) */;
                        }
                    }
                    continue;
                } else {
                    continue;
    //  Skip indented lines after struct/enum/class (not impl - handled above)
                }
            }
        }
        if (skip_until_unindent) {
            long long still_indented = simple_starts_with(line, "    ");
            long long is_tab = simple_starts_with(line, "\t");
            if (still_indented || is_tab) {
                continue;
            }
            skip_until_unindent = 0;
    //  Module directives - skip at top level
        }
        if (simple_starts_with(trimmed, "use ")) {
    //  Extract cross-module variable names from use imports
    //  Generate global declarations for known patterns (lex_cur_*, etc.)
            long long use_brace = simple_index_of(trimmed, "\{");
            long long use_brace_end = (simple_last_index_of(trimmed, "}") >= 0 ? simple_last_index_of(trimmed, "}") : -1);
            if (use_brace >= 0 && use_brace_end > use_brace) {
                const char* use_names_str = simple_substring(trimmed, use_brace + 1, use_brace_end);
                SimpleStringArray use_names = simple_split(use_names_str, ",");
                for (long long _idx_use_name_raw = 0; _idx_use_name_raw < use_names_len; _idx_use_name_raw++) { long long use_name_raw = use_names[_idx_use_name_raw];
                    const char* use_name = simple_trim(use_name_raw);
    //  Detect external globals: lowercase names that start with known prefixes
                    if (simple_starts_with(use_name, "lex_cur_") || simple_starts_with(use_name, "par_")) {
    //  Check if already declared (avoid duplicates)
                        const char* use_decl_marker = simple_str_concat(";use_decl:", simple_str_concat(use_name, ";"));
                        if (!(simple_contains(types, use_decl_marker))) {
                            types = simple_str_concat(types, use_decl_marker);
    //  Determine type from types registry
                            long long is_text_glob = simple_contains(types, simple_str_concat(";text:", simple_str_concat(use_name, ";")));
                            if (is_text_glob) {
                                /* global_defs.push(r"static const char* " + use_name + r" = " + "\"\"" + r";") */;
                            } else {
                                /* global_defs.push(r"static long long " + use_name + r" = 0;") */;
                            }
                        }
                    }
                }
            }
            continue;
        }
        if (simple_starts_with(trimmed, "import ")) {
            continue;
        }
        if (simple_starts_with(trimmed, "export ")) {
            continue;
        }
        if (simple_starts_with(trimmed, "from ")) {
            continue;
        }
        if (simple_starts_with(trimmed, "pub mod ")) {
            continue;
        }
        if (simple_starts_with(trimmed, "mod ")) {
            continue;
        }
        if (simple_starts_with(trimmed, "export use ")) {
            continue;
        }
        if (simple_starts_with(trimmed, "pub use ")) {
            if (simple_ends_with(trimmed, "{")) {
                skip_until_close_brace = 1;
            }
            continue;
        }
        if (simple_starts_with(trimmed, "common use ")) {
            continue;
    //  Extern function - generate forward declaration instead of skipping
        }
        if (simple_starts_with(trimmed, "extern fn ")) {
            const char* extern_rest = simple_substring(trimmed, 10, simple_strlen(trimmed));
    //  Parse: name(params) -> ret
            long long ep_idx = simple_index_of(extern_rest, "(");
            if (ep_idx >= 0) {
                const char* extern_name = simple_substring(extern_rest, 0, ep_idx);
                long long eclose = simple_index_of(extern_rest, ")");
                if (eclose >= 0) {
                    const char* eparams_str = "";
                    if (eclose > ep_idx + 1) {
                        eparams_str = simple_substring(extern_rest, ep_idx + 1, eclose);
                    }
                    long long earrow = simple_index_of(extern_rest, "->");
                    const char* eret_type = "void";
                    if (earrow >= 0) {
                        eret_type = simple_type_to_c(simple_substring(extern_rest, earrow + 2, simple_strlen(extern_rest)));
                    }
                    const char* ec_params = "void";
                    if (simple_strlen(eparams_str) > 0) {
                        ec_params = translate_params(eparams_str);
                    /* forward_decls.push(eret_type + r" " + extern_name + r"(" + ec_params + r");") */;
    //  Track extern fn return types for type inference
                    }
                    if (strcmp(eret_type, "const char*") == 0) {
                        types = simple_str_concat(types, simple_str_concat("fn_text:", simple_str_concat(extern_name, ";")));
    //  Track struct and array return types
                    }
                    if (earrow >= 0) {
                        const char* eret_raw = simple_substring(extern_rest, earrow + 2, simple_strlen(extern_rest));
                        if (simple_strlen(eret_raw) > 0) {
                            const char* eret_first = simple_char_at(eret_raw, 0);
                            if (eret_first >= "A" && eret_first <= "Z") {
                                types = simple_str_concat(types, simple_str_concat("fn_struct:", simple_str_concat(extern_name, simple_str_concat("=", simple_str_concat(eret_raw, ";")))));
                            }
                            if (simple_starts_with(eret_raw, "[") && simple_ends_with(eret_raw, "]")) {
                                const char* ext_arr_elem = simple_substring(eret_raw, 1, simple_strlen(eret_raw) - 1);
                                if (strcmp(ext_arr_elem, "i64") == 0 || strcmp(ext_arr_elem, "int") == 0) {
                                    types = simple_str_concat(types, simple_str_concat("fn_int_arr:", simple_str_concat(extern_name, ";")));
                                } else if (strcmp(ext_arr_elem, "text") == 0 || strcmp(ext_arr_elem, "str") == 0) {
                                    types = simple_str_concat(types, simple_str_concat("fn_str_arr:", simple_str_concat(extern_name, ";")));
                                }
                            }
                        }
                    }
                }
            }
            continue;
    //  Type alias - skip
        }
        if (simple_starts_with(trimmed, "type ") && simple_contains(trimmed, " = ")) {
            continue;
    //  Docstrings - skip
        }
        if (simple_starts_with(trimmed, "\"\"\"")) {
            continue;
    //  Decorator attributes - skip
        }
        if (simple_starts_with(trimmed, "#[")) {
            continue;
    //  Struct definition
        }
        if (simple_starts_with(trimmed, "struct ") && simple_ends_with(trimmed, ":")) {
            const char* struct_name = simple_substring(trimmed, 7, simple_strlen(trimmed) - 1);
            types = simple_str_concat(types, simple_str_concat("struct:", simple_str_concat(struct_name, ";")));
            long long field_result = parse_struct_fields(lines_arr, line_idx);
            long long field_body = field_result[1];
            const char* sdef = simple_str_concat("typedef struct {", "\n");
            sdef = simple_str_concat(sdef, simple_str_concat(field_body, "\n"));
            sdef = simple_str_concat(sdef, simple_str_concat("} ", simple_str_concat(struct_name, ";")));
            /* struct_defs.push(sdef) */;
            types = simple_str_concat(types, cg_track_field_types(lines_arr, line_idx, struct_name));
            skip_until_unindent = 1;
            continue;
    //  Enum definition - detect data variants vs simple enums
        }
        if (simple_starts_with(trimmed, "enum ") && simple_ends_with(trimmed, ":")) {
            long long enum_result = cg_process_enum(lines_arr, line_idx, trimmed);
            SimpleStringArray enum_parts = simple_split(enum_result, "
            /* enum_defs.push(enum_parts[0]) */;
            types = simple_str_concat(types, enum_parts[1]);
            skip_until_unindent = 1;
            continue;
    //  Class definition - treat like struct
        }
        if (simple_starts_with(trimmed, "class ") && simple_ends_with(trimmed, ":")) {
            const char* class_name = simple_substring(trimmed, 6, simple_strlen(trimmed) - 1);
            types = simple_str_concat(types, simple_str_concat("struct:", simple_str_concat(class_name, ";")));
            long long field_result = parse_struct_fields(lines_arr, line_idx);
            long long field_body = field_result[1];
            const char* cdef = simple_str_concat("typedef struct {", "\n");
            cdef = simple_str_concat(cdef, simple_str_concat(field_body, "\n"));
            cdef = simple_str_concat(cdef, simple_str_concat("} ", simple_str_concat(class_name, ";")));
            /* struct_defs.push(cdef) */;
            types = simple_str_concat(types, cg_track_field_types(lines_arr, line_idx, class_name));
            skip_until_unindent = 1;
            continue;
    //  Impl block - parse methods
        }
        if (simple_starts_with(trimmed, "impl ") && simple_ends_with(trimmed, ":")) {
            current_impl_class = simple_substring(trimmed, 5, simple_strlen(trimmed) - 1);
            in_impl = 1;
            in_impl_method = 0;
            continue;
    //  Function definition
        }
        if (simple_starts_with(trimmed, "fn ") && simple_ends_with(trimmed, ":")) {
            if (in_func) {
                long long fn_code = build_function(current_fn_name, current_fn_sig, current_fn_lines);
                /* func_defs.push(fn_code) */;
                current_fn_lines = simple_new_int_array();
    //  Restore types to before function (clear local var types)
                types = types_before_fn;
            }
            if (strcmp(trimmed, "fn main():") == 0 || simple_starts_with(trimmed, "fn main()")) {
                in_main = 1;
                in_func = 0;
                types_before_fn = types;
                continue;
            }
            long long parsed = parse_fn_signature(trimmed);
            current_fn_name = parsed[0];
            current_fn_sig = parsed[1];
            long long fwd = parsed[2];
            /* forward_decls.push(fwd) */;
            in_func = 1;
            in_main = 0;
    //  Track function return type and parameter types
            types = simple_str_concat(types, cg_track_fn_types(trimmed, current_fn_name));
            types_before_fn = types;
            continue;
    //  Static fn at top level - skip (only valid inside impl)
        }
        if (simple_starts_with(trimmed, "static fn ") && simple_ends_with(trimmed, ":")) {
            skip_until_unindent = 1;
            continue;
    //  Mutable method at top level - skip (only valid inside impl)
        }
        if (simple_starts_with(trimmed, "me ") && simple_ends_with(trimmed, ":")) {
            skip_until_unindent = 1;
            continue;
        }
        long long is_indented = simple_starts_with(line, "    ");
        if (!(is_indented)) {
            is_indented = simple_starts_with(line, "\t");
        }
        if (in_main && is_indented) {
            long long indent = get_indent_level(line);
            long long raw_result = translate_statement(trimmed, types);
            long long parts = split_result(raw_result);
            long long code = parts[0];
            long long new_types = parts[1];
            if (strcmp(new_types, "") != 0) {
                types = simple_str_concat(types, new_types);
            }
            if (strcmp(code, "") != 0) {
                const char* padding = "";
                for (long long pi = 0; pi <  indent; pi++) {
                    padding = simple_str_concat(padding, "    ");
                /* main_body.push(padding + code) */;
                }
            }
            continue;
        }
        if (in_func && is_indented) {
            long long indent = get_indent_level(line);
            long long raw_result = translate_statement(trimmed, types);
            long long parts = split_result(raw_result);
            long long code = parts[0];
            long long new_types = parts[1];
            if (strcmp(new_types, "") != 0) {
                types = simple_str_concat(types, new_types);
            }
            if (strcmp(code, "") != 0) {
                const char* padding = "";
                for (long long pi = 0; pi <  indent; pi++) {
                    padding = simple_str_concat(padding, "    ");
                /* current_fn_lines.push(padding + code) */;
                }
            }
            continue;
        }
        if (in_main) {
            in_main = 0;
            types = types_before_fn;
        }
        if (in_func) {
            long long fn_code = build_function(current_fn_name, current_fn_sig, current_fn_lines);
            /* func_defs.push(fn_code) */;
            current_fn_lines = simple_new_int_array();
            in_func = 0;
            types = types_before_fn;
    //  Module-level statement - check if it's a val/var declaration (-> global)
        }
        long long is_module_val = simple_starts_with(trimmed, "val ");
        long long is_module_var = simple_starts_with(trimmed, "var ");
        if (is_module_val || is_module_var) {
            long long raw_result = translate_statement(trimmed, types);
            long long parts = split_result(raw_result);
            long long code = parts[0];
            long long new_types = parts[1];
            if (strcmp(new_types, "") != 0) {
                types = simple_str_concat(types, new_types);
            }
            if (strcmp(code, "") != 0) {
    //  Convert to global: remove const for val (use static), add static for var
                long long global_code = code;
                if (simple_starts_with(global_code, "long long ")) {
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "const char* ")) {
    //  Check if init uses a function call (can't do at global scope)
                    long long str_eq = simple_index_of(global_code, " = ");
                    if (str_eq >= 0) {
                        const char* str_init = simple_substring(global_code, str_eq + 3, simple_strlen(global_code));
                        long long str_has_call = simple_contains(str_init, "(");
                        if (str_has_call) {
                            const char* str_decl = simple_substring(global_code, 0, str_eq);
                            /* global_defs.push(r"static " + str_decl + r" = NULL;") */;
                            const char* str_name = simple_substring(str_decl, 12, simple_strlen(str_decl));
                            long long str_semi = simple_index_of(str_init, ";");
                            const char* str_val = str_init;
                            if (str_semi >= 0) {
                                str_val = simple_substring(str_init, 0, str_semi);
                            /* main_body.push(r"    " + str_name + r" = " + str_val + r";") */;
                            }
                            continue;
                        }
                    }
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "int ")) {
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "SimpleStringArray ")) {
    //  Arrays need special init - can't call functions in global init
    //  Extract name and emit as uninitialized, init in main
                    long long arr_eq = simple_index_of(global_code, " = ");
                    if (arr_eq >= 0) {
                        const char* arr_decl = simple_substring(global_code, 0, arr_eq);
                        /* global_defs.push(r"static " + arr_decl + r";") */;
    //  Add init to main_body
                        const char* arr_name = simple_substring(arr_decl, 18, simple_strlen(arr_decl));
                        long long arr_semi = simple_index_of(arr_name, ";");
                        const char* clean_name = arr_name;
                        if (arr_semi >= 0) {
                            clean_name = simple_substring(arr_name, 0, arr_semi);
                        /* main_body.push(r"    " + clean_name + r" = simple_new_string_array();") */;
                        }
                        continue;
                    }
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "SimpleIntArray ")) {
    //  Int arrays need deferred init too
                    long long arr_eq = simple_index_of(global_code, " = ");
                    if (arr_eq >= 0) {
                        const char* arr_decl = simple_substring(global_code, 0, arr_eq);
                        /* global_defs.push(r"static " + arr_decl + r";") */;
                        const char* arr_name = simple_substring(arr_decl, 15, simple_strlen(arr_decl));
                        long long arr_semi = simple_index_of(arr_name, ";");
                        const char* clean_name = arr_name;
                        if (arr_semi >= 0) {
                            clean_name = simple_substring(arr_name, 0, arr_semi);
                        /* main_body.push(r"    " + clean_name + r" = simple_new_int_array();") */;
                        }
                        continue;
                    }
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "SimpleStringArrayArray ")) {
                    long long arr_eq = simple_index_of(global_code, " = ");
                    if (arr_eq >= 0) {
                        const char* arr_decl = simple_substring(global_code, 0, arr_eq);
                        /* global_defs.push(r"static " + arr_decl + r";") */;
                        const char* arr_name = simple_substring(arr_decl, 23, simple_strlen(arr_decl));
                        long long arr_semi = simple_index_of(arr_name, ";");
                        const char* clean_name = arr_name;
                        if (arr_semi >= 0) {
                            clean_name = simple_substring(arr_name, 0, arr_semi);
                        /* main_body.push(r"    " + clean_name + r" = simple_new_string_array_array();") */;
                        }
                        continue;
                    }
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "SimpleIntArrayArray ")) {
                    long long arr_eq = simple_index_of(global_code, " = ");
                    if (arr_eq >= 0) {
                        const char* arr_decl = simple_substring(global_code, 0, arr_eq);
                        /* global_defs.push(r"static " + arr_decl + r";") */;
                        const char* arr_name = simple_substring(arr_decl, 20, simple_strlen(arr_decl));
                        long long arr_semi = simple_index_of(arr_name, ";");
                        const char* clean_name = arr_name;
                        if (arr_semi >= 0) {
                            clean_name = simple_substring(arr_name, 0, arr_semi);
                        /* main_body.push(r"    " + clean_name + r" = simple_new_int_array_array();") */;
                        }
                        continue;
                    }
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "SimpleStructArray ")) {
    //  Struct arrays need deferred init
                    long long sarr_eq = simple_index_of(global_code, " = ");
                    if (sarr_eq >= 0) {
                        const char* sarr_decl = simple_substring(global_code, 0, sarr_eq);
                        /* global_defs.push(r"static " + sarr_decl + r";") */;
                        const char* sarr_name = simple_substring(sarr_decl, 18, simple_strlen(sarr_decl));
                        long long sarr_semi = simple_index_of(sarr_name, ";");
                        const char* clean_sarr = sarr_name;
                        if (sarr_semi >= 0) {
                            clean_sarr = simple_substring(sarr_name, 0, sarr_semi);
                        /* main_body.push(r"    " + clean_sarr + r" = simple_new_struct_array();") */;
                        }
                        continue;
                    }
                    global_code = simple_str_concat("static ", global_code);
                } else if (simple_starts_with(global_code, "SimpleDict* ")) {
                    long long dict_eq = simple_index_of(global_code, " = ");
                    if (dict_eq >= 0) {
                        const char* dict_decl = simple_substring(global_code, 0, dict_eq);
                        /* global_defs.push(r"static " + dict_decl + r" = NULL;") */;
                        long long dict_name_start = simple_index_of(dict_decl, "* ");
                        if (dict_name_start >= 0) {
                            const char* dict_name = simple_substring(dict_decl, dict_name_start + 2, simple_strlen(dict_decl));
                            /* main_body.push(r"    " + dict_name + r" = simple_dict_new();") */;
                        }
                        continue;
                    }
                    global_code = simple_str_concat("static ", global_code);
                } else {
                    global_code = simple_str_concat("static ", global_code);
                /* global_defs.push(global_code) */;
                }
            }
        } else {
            long long raw_result = translate_statement(trimmed, types);
            long long parts = split_result(raw_result);
            long long code = parts[0];
            long long new_types = parts[1];
            if (strcmp(new_types, "") != 0) {
                types = simple_str_concat(types, new_types);
            }
            if (strcmp(code, "") != 0) {
                long long mod_indent = get_indent_level(line);
                const char* mod_padding = "    ";
                for (long long mpi = 0; mpi <  mod_indent; mpi++) {
                    mod_padding = simple_str_concat(mod_padding, "    ");
                /* main_body.push(mod_padding + code) */;
    //  Flush pending impl method
                }
            }
        }
    }
    if (in_impl && in_impl_method) {
        const char* method_code = build_function(simple_str_concat(current_impl_class, simple_str_concat("__", impl_method_name)), impl_method_sig, impl_method_lines);
        /* func_defs.push(method_code) */;
    }
    if (in_func) {
        long long fn_code = build_function(current_fn_name, current_fn_sig, current_fn_lines);
        /* func_defs.push(fn_code) */;
    }
    main_body = close_blocks(main_body);
    //  Build final C code
    const char* c_code = "#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n";
    c_code = simple_str_concat(c_code, "#include <stdint.h>\n");
    c_code = simple_str_concat(c_code, "#ifdef _MSC_VER\n#define strdup _strdup\n#endif\n");
    //  Add C runtime helpers
    c_code = simple_str_concat(c_code, );
    //  Add enum definitions first (structs may reference enum types)
    if (enum_defs.len > 0) {
        c_code = simple_str_concat(c_code, "\n// --- Enum Definitions ---\n");
        for (long long _idx_edef = 0; _idx_edef < enum_defs_len; _idx_edef++) { long long edef = enum_defs[_idx_edef];
            c_code = simple_str_concat(c_code, simple_str_concat(edef, "\n\n"));
    //  Add struct definitions
        }
    }
    if (struct_defs.len > 0) {
        c_code = simple_str_concat(c_code, "\n// --- Struct Definitions ---\n");
        for (long long _idx_sdef = 0; _idx_sdef < struct_defs_len; _idx_sdef++) { long long sdef = struct_defs[_idx_sdef];
            c_code = simple_str_concat(c_code, simple_str_concat(sdef, "\n\n"));
    //  Add global variable definitions
        }
    }
    if (global_defs.len > 0) {
        c_code = simple_str_concat(c_code, "\n// --- Global Variables ---\n");
        for (long long _idx_gdef = 0; _idx_gdef < global_defs_len; _idx_gdef++) { long long gdef = global_defs[_idx_gdef];
            c_code = simple_str_concat(c_code, simple_str_concat(gdef, "\n"));
        }
        c_code = simple_str_concat(c_code, "\n");
    //  Add forward declarations
    }
    if (forward_decls.len > 0) {
        c_code = simple_str_concat(c_code, "\n// --- Forward Declarations ---\n");
        for (long long _idx_fwd = 0; _idx_fwd < forward_decls_len; _idx_fwd++) { long long fwd = forward_decls[_idx_fwd];
            c_code = simple_str_concat(c_code, simple_str_concat(fwd, "\n"));
        }
        c_code = simple_str_concat(c_code, "\n");
    //  Add function definitions
    }
    for (long long _idx_func = 0; _idx_func < func_defs_len; _idx_func++) { long long func = func_defs[_idx_func];
        c_code = simple_str_concat(c_code, simple_str_concat(func, "\n\n"));
    //  Add main
    }
    c_code = simple_str_concat(c_code, simple_str_concat("int main(void) {", "\n"));
    }
    for (long long _idx_body_line = 0; _idx_body_line < main_body_len; _idx_body_line++) { long long body_line = main_body[_idx_body_line];
        c_code = simple_str_concat(c_code, simple_str_concat(body_line, "\n"));
    }
    c_code = simple_str_concat(c_code, "    return 0;\n}\n");
    return c_code;
}

int main(void) {
    return 0;
}
