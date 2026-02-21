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
const char* cg_process_enum(SimpleStringArray lines_arr, long long line_idx, const char* trimmed);
const char* cg_track_field_types(SimpleStringArray lines_arr, long long start_idx, const char* type_name);
const char* cg_track_fn_types(const char* trimmed, const char* fn_name);

const char* cg_process_enum(SimpleStringArray lines_arr, long long line_idx, const char* trimmed) {
    const char* enum_name = simple_substring(trimmed, 5, simple_strlen(trimmed) - 1);
    const char* type_entries = simple_str_concat("struct:", simple_str_concat(enum_name, ";"));
    SimpleStringArray variants = simple_new_string_array();
    int has_data_variant = 0;
    SimpleStringArray data_variants = simple_new_string_array();
    SimpleStringArray simple_variants = simple_new_string_array();
    for (long long vi = line_idx + 1; vi < lines_arr.len; vi++) {
        const char* vline = lines_arr.items[vi];
        const char* vtrimmed = simple_trim(vline);
        if (strcmp(vtrimmed, "") == 0) {
            continue;
        }
        long long v_indented = simple_starts_with(vline, "    ");
        if (!(v_indented)) {
            break;
        }
        if (simple_starts_with(vtrimmed, "#")) {
            continue;
        }
        if (simple_starts_with(vtrimmed, "fn ") || simple_starts_with(vtrimmed, "me ") || simple_starts_with(vtrimmed, "static fn ")) {
            continue;
        }
        long long vparen = simple_index_of(vtrimmed, "(");
        if (vparen >= 0) {
            has_data_variant = 1;
            simple_string_push(&data_variants, vtrimmed);
        } else {
            simple_string_push(&simple_variants, vtrimmed);
        }
    }
    const char* enum_def = "";
    if (has_data_variant) {
        long long tag_idx = 0;
        const char* union_fields = "";
        const char* constructors = "";
        const char* tag_defines = "";
        for (long long _idx_dv = 0; _idx_dv < data_variants.len; _idx_dv++) { const char* dv = data_variants.items[_idx_dv];
            long long dv_paren = simple_index_of(dv, "(");
            const char* dv_name = simple_substring(dv, 0, dv_paren);
            long long dv_close = simple_index_of(dv, ")");
            const char* dv_fields_str = "";
            if (dv_close > dv_paren + 1) {
                dv_fields_str = simple_substring(dv, dv_paren + 1, dv_close);
            }
            tag_defines = simple_str_concat(tag_defines, simple_str_concat("#define ", simple_str_concat(enum_name, simple_str_concat("_TAG_", simple_str_concat(dv_name, simple_str_concat(" ", simple_str_concat(tag_idx, "\n")))))));
            type_entries = simple_str_concat(type_entries, simple_str_concat("enum_variant:", simple_str_concat(enum_name, simple_str_concat(".", simple_str_concat(dv_name, ";")))));
            const char* struct_fields = "";
            const char* ctor_params = "";
            const char* ctor_assigns = "";
            if (simple_strlen(dv_fields_str) > 0) {
                SimpleStringArray dv_parts = simple_split(dv_fields_str, ",");
                long long fi = 0;
                for (long long _idx_dvp = 0; _idx_dvp < dv_parts.len; _idx_dvp++) { const char* dvp = dv_parts.items[_idx_dvp];
                    const char* dvf = simple_trim(dvp);
                    long long dvf_colon = simple_index_of(dvf, ":");
                    if (dvf_colon >= 0) {
                        const char* fname = simple_substring(dvf, 0, dvf_colon);
                        const char* ftype = simple_substring(dvf, dvf_colon + 1, simple_strlen(dvf));
                        long long ctype = simple_type_to_c(ftype);
                        struct_fields = simple_str_concat(struct_fields, simple_str_concat("            ", simple_str_concat(ctype, simple_str_concat(" ", simple_str_concat(fname, simple_str_concat(";", "\n"))))));
                        if (fi > 0) {
                            ctor_params = simple_str_concat(ctor_params, ", ");
                        }
                        ctor_params = simple_str_concat(ctor_params, simple_str_concat(ctype, simple_str_concat(" ", fname)));
                        ctor_assigns = simple_str_concat(ctor_assigns, simple_str_concat("    r.data.", simple_str_concat(dv_name, simple_str_concat(".", simple_str_concat(fname, simple_str_concat(" = ", simple_str_concat(fname, simple_str_concat(";", "\n"))))))));
                    } else {
                        long long ctype = simple_type_to_c(dvf);
                        const char* pname = simple_str_concat("_", fi);
                        struct_fields = simple_str_concat(struct_fields, simple_str_concat("            ", simple_str_concat(ctype, simple_str_concat(" ", simple_str_concat(pname, simple_str_concat(";", "\n"))))));
                        if (fi > 0) {
                            ctor_params = simple_str_concat(ctor_params, ", ");
                        }
                        ctor_params = simple_str_concat(ctor_params, simple_str_concat(ctype, simple_str_concat(" ", pname)));
                        ctor_assigns = simple_str_concat(ctor_assigns, simple_str_concat("    r.data.", simple_str_concat(dv_name, simple_str_concat(".", simple_str_concat(pname, simple_str_concat(" = ", simple_str_concat(pname, simple_str_concat(";", "\n"))))))));
                    }
                    fi = fi + 1;
                }
            }
            union_fields = simple_str_concat(union_fields, simple_str_concat("        struct \{", simple_str_concat("\n", simple_str_concat(struct_fields, simple_str_concat("        } ", simple_str_concat(dv_name, ";\n"))))));
            constructors = simple_str_concat(constructors, simple_str_concat("static ", simple_str_concat(enum_name, simple_str_concat(" ", simple_str_concat(enum_name, simple_str_concat("__", simple_str_concat(dv_name, simple_str_concat("(", simple_str_concat(ctor_params, simple_str_concat(") \{", "\n"))))))))));
            constructors = simple_str_concat(constructors, simple_str_concat("    ", simple_str_concat(enum_name, simple_str_concat(" r;", simple_str_concat("\n", simple_str_concat("    r.tag = ", simple_str_concat(enum_name, simple_str_concat("_TAG_", simple_str_concat(dv_name, simple_str_concat(";", "\n"))))))))));
            constructors = simple_str_concat(constructors, ctor_assigns);
            constructors = simple_str_concat(constructors, simple_str_concat("    return r;", simple_str_concat("\n", simple_str_concat("}", "\n"))));
            tag_idx = tag_idx + 1;
        }
        for (long long _idx_sv = 0; _idx_sv < simple_variants.len; _idx_sv++) { const char* sv = simple_variants.items[_idx_sv];
            tag_defines = simple_str_concat(tag_defines, simple_str_concat("#define ", simple_str_concat(enum_name, simple_str_concat("_TAG_", simple_str_concat(sv, simple_str_concat(" ", simple_str_concat(tag_idx, "\n")))))));
            constructors = simple_str_concat(constructors, simple_str_concat("static ", simple_str_concat(enum_name, simple_str_concat(" ", simple_str_concat(enum_name, simple_str_concat("__", simple_str_concat(sv, simple_str_concat("(void) \{", "\n"))))))));
            constructors = simple_str_concat(constructors, simple_str_concat("    ", simple_str_concat(enum_name, simple_str_concat(" r;", simple_str_concat("\n", simple_str_concat("    r.tag = ", simple_str_concat(enum_name, simple_str_concat("_TAG_", simple_str_concat(sv, simple_str_concat(";", "\n"))))))))));
            constructors = simple_str_concat(constructors, simple_str_concat("    return r;", simple_str_concat("\n", simple_str_concat("}", "\n"))));
            tag_idx = tag_idx + 1;
        }
        enum_def = simple_str_concat(tag_defines, "\n");
        enum_def = simple_str_concat(enum_def, simple_str_concat("typedef struct \{", simple_str_concat("\n", simple_str_concat("    int tag;", simple_str_concat("\n", simple_str_concat("    union \{", "\n"))))));
        enum_def = simple_str_concat(enum_def, union_fields);
        enum_def = simple_str_concat(enum_def, simple_str_concat("    } data;", simple_str_concat("\n", simple_str_concat("} ", simple_str_concat(enum_name, ";\n\n")))));
        enum_def = simple_str_concat(enum_def, constructors);
    } else {
        SimpleStringArray variant_names = simple_new_string_array();
        for (long long _idx_sv = 0; _idx_sv < simple_variants.len; _idx_sv++) { const char* sv = simple_variants.items[_idx_sv];
            simple_string_push(&variant_names, simple_str_concat(enum_name, simple_str_concat("_", sv)));
            type_entries = simple_str_concat(type_entries, simple_str_concat("enum_variant:", simple_str_concat(enum_name, simple_str_concat(".", simple_str_concat(sv, ";")))));
        }
        const char* variant_list = simple_string_join(&variant_names, ", ");
        enum_def = simple_str_concat("typedef enum \{ ", simple_str_concat(variant_list, simple_str_concat(" } ", simple_str_concat(enum_name, ";"))));
    }
    return simple_str_concat(enum_def, simple_str_concat("
}

const char* cg_track_field_types(SimpleStringArray lines_arr, long long start_idx, const char* type_name) {
    const char* type_entries = "";
    for (long long fi = start_idx + 1; fi < lines_arr.len; fi++) {
        const char* fline = lines_arr.items[fi];
        const char* ftrimmed = simple_trim(fline);
        if (strcmp(ftrimmed, "") == 0) {
            continue;
        }
        long long f_indented = simple_starts_with(fline, "    ");
        if (!(f_indented)) {
            break;
        }
        if (simple_starts_with(ftrimmed, "fn ") || simple_starts_with(ftrimmed, "me ") || simple_starts_with(ftrimmed, "static fn ")) {
            break;
        }
        const char* fclean = ftrimmed;
        long long fhash = simple_index_of(ftrimmed, " #");
        if (fhash >= 0) {
            fclean = simple_substring(ftrimmed, 0, fhash);
        }
        long long fcolon = simple_index_of(fclean, ":");
        if (fcolon >= 0) {
            const char* fname = simple_substring(fclean, 0, fcolon);
            const char* ftype = simple_substring(fclean, fcolon + 1, simple_strlen(fclean));
            if (strcmp(ftype, "text") == 0 || strcmp(ftype, "str") == 0) {
                type_entries = simple_str_concat(type_entries, simple_str_concat("field_text:", simple_str_concat(type_name, simple_str_concat(".", simple_str_concat(fname, ";")))));
            }
            if (strcmp(ftype, "[text]") == 0 || strcmp(ftype, "[str]") == 0) {
                type_entries = simple_str_concat(type_entries, simple_str_concat("field_arr:", simple_str_concat(type_name, simple_str_concat(".", simple_str_concat(fname, ";")))));
            }
            if (strcmp(ftype, "[i64]") == 0 || strcmp(ftype, "[int]") == 0 || strcmp(ftype, "[bool]") == 0) {
                type_entries = simple_str_concat(type_entries, simple_str_concat("field_int_arr:", simple_str_concat(type_name, simple_str_concat(".", simple_str_concat(fname, ";")))));
            }
            if (simple_starts_with(ftype, "[") && simple_ends_with(ftype, "]")) {
                const char* sf_elem = simple_substring(ftype, 1, simple_strlen(ftype) - 1);
                if (simple_strlen(sf_elem) > 0) {
                    const char* sf_ef = simple_char_at(sf_elem, 0);
                    if (sf_ef >= "A" && sf_ef <= "Z") {
                        type_entries = simple_str_concat(type_entries, simple_str_concat("field_struct_arr:", simple_str_concat(type_name, simple_str_concat(".", simple_str_concat(fname, simple_str_concat("=", simple_str_concat(sf_elem, ";")))))));
                    }
                }
            }
        }
    }
    return type_entries;
}

const char* cg_track_fn_types(const char* trimmed, const char* fn_name) {
    const char* type_entries = "";
    // Track return type
    long long arrow_idx = simple_index_of(trimmed, "->");
    if (arrow_idx >= 0) {
        const char* ret_str = simple_substring(trimmed, arrow_idx + 2, simple_strlen(trimmed));
        long long colon_pos = simple_index_of(ret_str, ":");
        const char* ret_type = simple_trim(ret_str);
        if (colon_pos >= 0) {
            ret_type = simple_substring(ret_str, 0, colon_pos);
        }
        int is_text_ret = strcmp(ret_type, "text") == 0 || strcmp(ret_type, "str") == 0;
        if (is_text_ret) {
            type_entries = simple_str_concat(type_entries, simple_str_concat("fn_text:", simple_str_concat(fn_name, ";")));
        }
        if (simple_strlen(ret_type) > 0) {
            const char* ret_first = simple_char_at(ret_type, 0);
            int ret_is_upper = ret_first >= "A" && ret_first <= "Z";
            if (ret_is_upper) {
                type_entries = simple_str_concat(type_entries, simple_str_concat("fn_struct:", simple_str_concat(fn_name, simple_str_concat("=", simple_str_concat(ret_type, ";")))));
            }
        }
        if (simple_starts_with(ret_type, "[") && simple_ends_with(ret_type, "]")) {
            const char* ret_sa_elem = simple_substring(ret_type, 1, simple_strlen(ret_type) - 1);
            if (strcmp(ret_sa_elem, "i64") == 0 || strcmp(ret_sa_elem, "int") == 0) {
                type_entries = simple_str_concat(type_entries, simple_str_concat("fn_int_arr:", simple_str_concat(fn_name, ";")));
            } else if (strcmp(ret_sa_elem, "text") == 0 || strcmp(ret_sa_elem, "str") == 0) {
                type_entries = simple_str_concat(type_entries, simple_str_concat("fn_str_arr:", simple_str_concat(fn_name, ";")));
            } else if (simple_strlen(ret_sa_elem) > 0) {
                const char* ret_sa_f = simple_char_at(ret_sa_elem, 0);
                if (ret_sa_f >= "A" && ret_sa_f <= "Z") {
                    type_entries = simple_str_concat(type_entries, simple_str_concat("fn_struct_arr:", simple_str_concat(fn_name, simple_str_concat("=", simple_str_concat(ret_sa_elem, ";")))));
    // Track parameter types
                }
            }
        }
    }
    long long fn_paren_idx = simple_index_of(trimmed, "(");
    long long fn_close_idx = simple_index_of(trimmed, ")");
    if (fn_paren_idx >= 0 && fn_close_idx > fn_paren_idx + 1) {
        const char* fn_params_str = simple_substring(trimmed, fn_paren_idx + 1, fn_close_idx);
        SimpleStringArray fn_params = simple_split(fn_params_str, ",");
        for (long long _idx_fn_param = 0; _idx_fn_param < fn_params.len; _idx_fn_param++) { const char* fn_param = fn_params.items[_idx_fn_param];
            const char* fp = simple_trim(fn_param);
            long long fp_colon = simple_index_of(fp, ":");
            if (fp_colon >= 0) {
                const char* fp_name = simple_substring(fp, 0, fp_colon);
                const char* fp_type = simple_substring(fp, fp_colon + 1, simple_strlen(fp));
                if (strcmp(fp_type, "text") == 0 || strcmp(fp_type, "str") == 0) {
                    type_entries = simple_str_concat(type_entries, simple_str_concat("text:", simple_str_concat(fp_name, ";")));
                }
                if (strcmp(fp_type, "[text]") == 0 || strcmp(fp_type, "[str]") == 0) {
                    type_entries = simple_str_concat(type_entries, simple_str_concat("arr:", simple_str_concat(fp_name, ";")));
                }
                if (strcmp(fp_type, "[i64]") == 0 || strcmp(fp_type, "[int]") == 0 || strcmp(fp_type, "[bool]") == 0) {
                    type_entries = simple_str_concat(type_entries, simple_str_concat("int_arr:", simple_str_concat(fp_name, ";")));
                }
                if (strcmp(fp_type, "[[text]]") == 0 || strcmp(fp_type, "[[str]]") == 0) {
                    type_entries = simple_str_concat(type_entries, simple_str_concat("str_arr_arr:", simple_str_concat(fp_name, ";")));
                }
                if (strcmp(fp_type, "[[i64]]") == 0 || strcmp(fp_type, "[[int]]") == 0) {
                    type_entries = simple_str_concat(type_entries, simple_str_concat("int_arr_arr:", simple_str_concat(fp_name, ";")));
                }
                if (simple_starts_with(fp_type, "[") && simple_ends_with(fp_type, "]")) {
                    const char* fp_elem = simple_substring(fp_type, 1, simple_strlen(fp_type) - 1);
                    if (simple_strlen(fp_elem) > 0) {
                        const char* fp_ef = simple_char_at(fp_elem, 0);
                        if (fp_ef >= "A" && fp_ef <= "Z") {
                            type_entries = simple_str_concat(type_entries, simple_str_concat("struct_arr_var:", simple_str_concat(fp_name, simple_str_concat("=", simple_str_concat(fp_elem, ";")))));
                        }
                    }
                }
                if (simple_strlen(fp_type) > 0) {
                    const char* fp_first = simple_char_at(fp_type, 0);
                    int fp_upper = fp_first >= "A" && fp_first <= "Z";
                    if (fp_upper) {
                        type_entries = simple_str_concat(type_entries, simple_str_concat("struct_var:", simple_str_concat(fp_name, simple_str_concat("=", simple_str_concat(fp_type, ";")))));
                    }
                }
            }
        }
    }
    return type_entries;
}

int main(void) {
    return 0;
}

