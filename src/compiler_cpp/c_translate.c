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
SimpleStringArray close_blocks(SimpleStringArray body_lines);
const char* build_function(const char* name, const char* sig, SimpleStringArray body_lines);

SimpleStringArray close_blocks(SimpleStringArray body_lines) {
    SimpleStringArray result = simple_new_string_array();
    SimpleIntArray brace_indents = simple_new_int_array();
    for (long long idx = 0; idx < body_lines.len; idx++) {
        const char* line = body_lines.items[idx];
        const char* trimmed = simple_trim(line);
        long long current_indent = get_c_indent(line);
    // Don't let comments trigger block closing
        if (simple_starts_with(trimmed, "//") || simple_starts_with(trimmed, "/*")) {
            simple_string_push(&result, line);
            continue;
        }
        if (simple_starts_with(trimmed, "} else")) {
    // Close any nested blocks at higher indent before the else
            long long else_close = 0;
            for (long long ebi = 0; ebi < brace_indents.len; ebi++) {
                long long esi = brace_indents.len - 1 - ebi;
                if (esi < 0) {
                    break;
                }
                if (brace_indents.items[esi] > current_indent) {
                    else_close = else_close + 1;
                } else {
                    break;
                }
            }
            for (long long eci = 0; eci < else_close; eci++) {
                long long epi = brace_indents.len - 1;
                long long eclose_indent = brace_indents.items[epi];
                simple_int_pop(&brace_indents);
                const char* epad = "";
                for (long long epi2 = 0; epi2 < eclose_indent; epi2++) {
                    epad = simple_str_concat(epad, "    ");
                }
                simple_string_push(&result, simple_str_concat(epad, "}"));
            }
            simple_string_push(&result, line);
            continue;
        }
        long long close_count = 0;
        for (long long bi = 0; bi < brace_indents.len; bi++) {
            long long stack_idx = brace_indents.len - 1 - bi;
            if (stack_idx < 0) {
                break;
            }
            if (current_indent <= brace_indents.items[stack_idx]) {
                close_count = close_count + 1;
            } else {
                break;
            }
        }
        for (long long ci = 0; ci < close_count; ci++) {
            long long pop_idx = brace_indents.len - 1;
            long long close_indent = brace_indents.items[pop_idx];
            simple_int_pop(&brace_indents);
            const char* close_padding = "";
            for (long long pi = 0; pi < close_indent; pi++) {
                close_padding = simple_str_concat(close_padding, "    ");
            }
            simple_string_push(&result, simple_str_concat(close_padding, "}"));
        }
        simple_string_push(&result, line);
        if (simple_ends_with(trimmed, "\{")) {
            simple_int_push(&brace_indents, current_indent);
        } else if (simple_contains(trimmed, ") \{") && !(simple_ends_with(trimmed, "}"))) {
    // Inline opening brace (e.g., for-loop with inline body start)
            simple_int_push(&brace_indents, current_indent);
        } else if (simple_starts_with(trimmed, "\{") && !(simple_ends_with(trimmed, "}"))) {
    // Match block opening: { long long _match_val = ...;
            simple_int_push(&brace_indents, current_indent);
        }
    }
    for (long long ci = 0; ci < brace_indents.len; ci++) {
        long long pop_idx = brace_indents.len - 1 - ci;
        long long close_indent = brace_indents.items[pop_idx];
        const char* close_padding = "";
        for (long long pi = 0; pi < close_indent; pi++) {
            close_padding = simple_str_concat(close_padding, "    ");
        }
        simple_string_push(&result, simple_str_concat(close_padding, "}"));
    }
    return result;
}

const char* build_function(const char* name, const char* sig, SimpleStringArray body_lines) {
    SimpleStringArray closed_lines = close_blocks(body_lines);
    // Check if the function has a non-void return type
    long long is_void_fn = simple_starts_with(sig, "void ");
    // Find the last meaningful statement line (not a closing brace)
    long long last_stmt_idx = -1;
    if (!(is_void_fn)) {
        for (long long li = 0; li < closed_lines.len; li++) {
            long long check_idx = closed_lines.len - 1 - li;
            if (check_idx < 0) {
                break;
            }
            const char* check_line = simple_trim(closed_lines[check_idx]);
            if (strcmp(check_line, "}") == 0) {
                continue;
            }
            if (strcmp(check_line, "") == 0) {
                continue;
            }
            if (simple_starts_with(check_line, "//")) {
                continue;
            }
            if (simple_starts_with(check_line, "/*")) {
                continue;
            }
            last_stmt_idx = check_idx;
            break;
    // Deduplicate variable declarations: if a name is declared multiple times
    // (e.g., in different branches), convert subsequent declarations to assignments
    // Scope-aware: track indent level of each declaration so that variables in
    // sibling scopes (e.g., two if-blocks at the same indent) are not deduped
        }
    }
    SimpleStringArray declared_vars = simple_new_string_array();
    SimpleIntArray declared_indents = simple_new_int_array();
    SimpleStringArray deduped_lines = simple_new_string_array();
    SimpleStringArray c_types_arr = simple_new_string_array(); simple_string_push(&c_types_arr, "const char* "); simple_string_push(&c_types_arr, "long long "); simple_string_push(&c_types_arr, "int "); simple_string_push(&c_types_arr, "double "); simple_string_push(&c_types_arr, "SimpleStringArray "); simple_string_push(&c_types_arr, "SimpleIntArray "); simple_string_push(&c_types_arr, "SimpleStringArrayArray "); simple_string_push(&c_types_arr, "SimpleIntArrayArray "); simple_string_push(&c_types_arr, "SimpleStructArray "); simple_string_push(&c_types_arr, "SimpleDict* "); simple_string_push(&c_types_arr, "SimpleOption ");
    for (long long dl_idx = 0; dl_idx < closed_lines.len; dl_idx++) {
        const char* dl = closed_lines.items[dl_idx];
        const char* dl_trim = simple_trim(dl);
        long long dl_c_indent = get_c_indent(dl);
    // Scope cleanup: remove vars declared at indent > current indent
    // (they went out of scope when their block's } was processed)
        SimpleStringArray scope_new_vars = simple_new_string_array();
        SimpleIntArray scope_new_indents = simple_new_int_array();
        for (long long scope_vi = 0; scope_vi < declared_vars.len; scope_vi++) {
            if (declared_indents.items[scope_vi] <= dl_c_indent) {
                simple_string_push(&scope_new_vars, declared_vars.items[scope_vi]);
                simple_int_push(&scope_new_indents, declared_indents.items[scope_vi]);
            }
        }
        declared_vars = scope_new_vars;
        declared_indents = scope_new_indents;
    // Check if this line is a C variable declaration
        const char* found_type = "";
        const char* found_name = "";
        for (long long _idx_ct = 0; _idx_ct < c_types_arr.len; _idx_ct++) { const char* ct = c_types_arr.items[_idx_ct];
            if (simple_starts_with(dl_trim, ct) && simple_contains(dl_trim, " = ")) {
                const char* after_type = simple_substring(dl_trim, simple_strlen(ct), simple_strlen(dl_trim));
                long long eq_pos = simple_index_of(after_type, " = ");
                if (eq_pos >= 0) {
                    found_type = ct;
                    found_name = simple_substring(after_type, 0, eq_pos);
                    break;
    // Also check struct declarations: StructName varname = ...
                }
            }
        }
        if (strcmp(found_type, "") == 0 && simple_contains(dl_trim, " = ") && !(simple_starts_with(dl_trim, "if ") && !(simple_starts_with(dl_trim, "for ") && !(simple_starts_with(dl_trim, "return ") && !(simple_starts_with(dl_trim, "//") && !(simple_starts_with(dl_trim, "/*"))))))) {
            long long space_pos = simple_index_of(dl_trim, " ");
            if (space_pos >= 0) {
                const char* first_word = simple_substring(dl_trim, 0, space_pos);
                const char* fw_first = simple_char_at(first_word, 0);
                int fw_upper = fw_first >= "A" && fw_first <= "Z";
                if (fw_upper && !(simple_starts_with(first_word, "Simple"))) {
                    const char* after_struct = simple_substring(dl_trim, space_pos + 1, simple_strlen(dl_trim));
                    long long eq_pos = simple_index_of(after_struct, " = ");
                    if (eq_pos >= 0) {
                        found_type = simple_str_concat(first_word, " ");
                        found_name = simple_substring(after_struct, 0, eq_pos);
                    }
                }
            }
        }
        if (strcmp(found_name, "") != 0) {
    // Check if already declared (only vars still in scope)
            int already = 0;
            for (long long _idx_dv = 0; _idx_dv < declared_vars.len; _idx_dv++) { const char* dv = declared_vars.items[_idx_dv];
                if (strcmp(dv, found_name) == 0) {
                    already = 1;
                    break;
                }
            }
            if (already) {
    // Replace declaration with assignment: strip the type prefix
                const char* dl_indent = simple_substring(dl, 0, simple_strlen(dl) - simple_strlen(dl_trim));
                const char* assignment = simple_substring(dl_trim, simple_strlen(found_type), simple_strlen(dl_trim));
                simple_string_push(&deduped_lines, "{dl_indent}{assignment}");
            } else {
                simple_string_push(&declared_vars, found_name);
                simple_int_push(&declared_indents, dl_c_indent);
                simple_string_push(&deduped_lines, dl);
            }
        } else {
            simple_string_push(&deduped_lines, dl);
        }
    }
    const char* result = simple_str_concat("{sig} ", simple_str_concat("\{", "\n"));
    for (long long line_idx = 0; line_idx < deduped_lines.len; line_idx++) {
        const char* body_line = deduped_lines.items[line_idx];
        if (line_idx == last_stmt_idx) {
            const char* bl_trimmed = simple_trim(body_line);
    // Add return if the last statement doesn't have one
            long long has_ret = simple_starts_with(bl_trimmed, "return ");
            int is_control = simple_starts_with(bl_trimmed, "if ") || simple_starts_with(bl_trimmed, "} else") || simple_starts_with(bl_trimmed, "for ") || simple_starts_with(bl_trimmed, "while ");
            int is_comment = simple_starts_with(bl_trimmed, "//") || simple_starts_with(bl_trimmed, "/*");
            if (!(has_ret && !(is_control && !(is_comment)))) {
    // Remove the trailing semicolon, wrap with return
                const char* stmt = bl_trimmed;
                if (simple_ends_with(stmt, ";")) {
                    stmt = simple_substring(stmt, 0, simple_strlen(stmt) - 1);
                }
                const char* indent = simple_substring(body_line, 0, simple_strlen(body_line) - simple_strlen(bl_trimmed));
                result = simple_str_concat(result, "{indent}return {stmt};\n");
                continue;
            }
        }
        result = simple_str_concat(result, simple_str_concat(body_line, "\n"));
    }
    result = simple_str_concat(result, "}");
    return result;
}

int main(void) {
    return 0;
}

