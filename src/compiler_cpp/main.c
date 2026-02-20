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


// --- Struct Definitions ---
typedef struct {
    int gc_log;
    int gc_off;
    int use_notui;
    long long max_recursion_depth;
    long long timeout_secs;
    long long execution_limit;
    int stack_overflow_detection;
    const char* backend;
    int force_interpret;
    const char* interpreter_mode;
    const char* run_config;
    int no_jit;
    long long jit_threshold;
} GlobalFlags;


// --- Forward Declarations ---
const char* get_version(void);
void print_version(void);
void print_targets(void);
void print_linkers(void);
void print_error(const char* msg);
void print_error_with_help(const char* msg);
long long run_lex_command(const char* path);
long long parse_global_flags(SimpleStringArray args);
void apply_fault_detection(long long flags);
void apply_jit_env_vars(long long flags);
SimpleStringArray filter_internal_flags(SimpleStringArray args);

const char* get_version(void) {
    long long version = env_get("SIMPLE_VERSION");
    if (strcmp(version, "") != 0 && version >= 0) {
        return version;
    }
    return "0.5.0";
}

void print_version(void) {
    const char* v = ;
    printf("Simple v%s\n", v);
}

void print_targets(void) {
    puts("Available target architectures:");
    puts("");
    puts("  x86_64          64-bit x86 Linux (ELF)");
    puts("  aarch64         64-bit ARM Linux (ELF)");
    puts("  riscv64         64-bit RISC-V Linux (ELF)");
    puts("  aarch64-macos   64-bit ARM macOS (Mach-O, Apple Silicon)");
    puts("  x86_64-macos    64-bit x86 macOS (Mach-O, Intel Mac)");
    puts("  i686            32-bit x86");
    puts("  armv7           32-bit ARM");
    puts("  riscv32         32-bit RISC-V");
    puts("");
    puts("WebAssembly:");
    puts("  wasm32-wasi     32-bit WebAssembly (WASI Preview 1)");
    puts("  wasm32          32-bit WebAssembly (standalone, no WASI)");
    puts("  wasm64          64-bit WebAssembly (Memory64 proposal)");
    puts("");
    puts("Usage:");
    puts("  simple compile app.spl --target aarch64");
    puts("  simple compile app.spl --target aarch64-macos");
    puts("  simple compile app.spl --target wasm32-wasi -o app.wasm");
}

void print_linkers(void) {
    puts("Available native linkers:");
    puts("");
    puts("  mold      Modern linker (fastest, recommended)");
    puts("  lld       LLVM linker (fast, widely available)");
    puts("  ld        GNU linker (default, always available)");
    puts("");
    puts("The linker is auto-detected if not specified.");
    puts("Preference order: mold > lld > ld");
    puts("");
    puts("Usage:");
    puts("  simple compile app.spl --linker mold");
}

void print_error(const char* msg) {
    error("cli", msg);
}

void print_error_with_help(const char* msg) {
    error("cli", msg);
    puts("");
    ;
}

long long run_lex_command(const char* path) {
    long long args = ;
    return cli_run_lex(args);
}

long long parse_global_flags(SimpleStringArray args) {
    int gc_log = 0;
    int gc_off = 0;
    int use_notui = 0;
    long long max_recursion_depth = 0;
    long long timeout_secs = 0;
    long long execution_limit = 0;
    int stack_overflow_detection = 0;
    int has_stack_overflow_flag = 0;
    const char* backend = "auto";
    int force_interpret = 0;
    const char* interpreter_mode = "optimized";
    const char* run_config = "";
    int no_jit = 0;
    long long jit_threshold = 10;
    long long i = 0;
    while (i < args.len) {
        const char* arg = args.items[i];
        if (strcmp(arg, "--gc-log") == 0) {
            gc_log = 1;
        } else if (strcmp(arg, "--gc-off") == 0) {
            gc_off = 1;
        } else if (strcmp(arg, "--notui") == 0) {
            use_notui = 1;
        } else if (strcmp(arg, "--interpret") == 0) {
            force_interpret = 1;
        } else if (strcmp(arg, "--interpret-optimized") == 0) {
            force_interpret = 1;
            interpreter_mode = "optimized";
        } else if (strcmp(arg, "--no-jit") == 0) {
            no_jit = 1;
        } else if (simple_starts_with(arg, "--jit-threshold=")) {
            const char* val_str = simple_substring(arg, 16, simple_strlen(arg));
            jit_threshold = atoll(val_str);
        } else if (strcmp(arg, "--jit-threshold") == 0 && i + 1 < args.len) {
            i = i + 1;
            jit_threshold = atoll(args[i]);
        } else if (simple_starts_with(arg, "--interpreter-mode=")) {
            interpreter_mode = simple_substring(arg, 19, simple_strlen(arg));
        } else if (strcmp(arg, "--interpreter-mode") == 0 && i + 1 < args.len) {
            i = i + 1;
            interpreter_mode = args.items[i];
        } else if (simple_starts_with(arg, "--run-config=")) {
            run_config = simple_substring(arg, 13, simple_strlen(arg));
        } else if (strcmp(arg, "--run-config") == 0 && i + 1 < args.len) {
            i = i + 1;
            run_config = args.items[i];
        } else if (simple_starts_with(arg, "--backend=")) {
            backend = simple_substring(arg, 10, simple_strlen(arg));
        } else if (strcmp(arg, "--backend") == 0 && i + 1 < args.len) {
            i = i + 1;
            backend = args.items[i];
        } else if (strcmp(arg, "--stack-overflow-detection") == 0) {
            stack_overflow_detection = 1;
            has_stack_overflow_flag = 1;
        } else if (strcmp(arg, "--no-stack-overflow-detection") == 0) {
            stack_overflow_detection = 0;
            has_stack_overflow_flag = 1;
        } else if (simple_starts_with(arg, "--max-recursion-depth=")) {
            const char* val_str = simple_substring(arg, 21, simple_strlen(arg));
            max_recursion_depth = atoll(val_str);
        } else if (strcmp(arg, "--max-recursion-depth") == 0 && i + 1 < args.len) {
            i = i + 1;
            max_recursion_depth = atoll(args[i]);
        } else if (simple_starts_with(arg, "--timeout=")) {
            const char* val_str = simple_substring(arg, 10, simple_strlen(arg));
            timeout_secs = atoll(val_str);
        } else if (strcmp(arg, "--timeout") == 0 && i + 1 < args.len) {
            i = i + 1;
            timeout_secs = atoll(args[i]);
        } else if (simple_starts_with(arg, "--execution-limit=")) {
            const char* val_str = simple_substring(arg, 18, simple_strlen(arg));
            execution_limit = atoll(val_str);
        } else if (strcmp(arg, "--execution-limit") == 0 && i + 1 < args.len) {
            i = i + 1;
            execution_limit = atoll(args[i]);
        }
        i = i + 1;
    //  Check SIMPLE_EXECUTION_MODE env var as fallback
    }
    if (!(force_interpret && strcmp(backend, "auto") == 0)) {
        long long env_mode = env_get("SIMPLE_EXECUTION_MODE");
        if (strcmp(env_mode, "interpret") == 0) {
            force_interpret = 1;
        } else if (strcmp(env_mode, "interpret-optimized") == 0) {
            force_interpret = 1;
            interpreter_mode = "optimized";
        } else if (strcmp(env_mode, "cranelift") == 0) {
            backend = "cranelift";
        } else if (strcmp(env_mode, "llvm") == 0) {
            backend = "llvm";
        } else if (strcmp(env_mode, "vhdl") == 0) {
            backend = "vhdl";
        } else if (strcmp(env_mode, "jit") == 0) {
            backend = "auto";
    //  Read run-config from simple.sdn if not set via CLI/env
        }
    }
    if (strcmp(run_config, "") == 0) {
        run_config = ;
    //  Map run_config to interpreter_mode
    }
    if (strcmp(run_config, "compiler") == 0 || strcmp(run_config, "shared") == 0) {
        interpreter_mode = "optimized";
        force_interpret = 1;
    } else if (strcmp(run_config, "interpreter") == 0) {
    //  Backward-compatible alias: "interpreter" now means shared/default mode.
        interpreter_mode = "optimized";
        force_interpret = 1;
    } else if (strcmp(run_config, "legacy") == 0) {
        interpreter_mode = "classic";
        force_interpret = 1;
    }
    return (GlobalFlags){.gc_log =  gc_log, .gc_off =  gc_off, .use_notui =  use_notui, .max_recursion_depth =  max_recursion_depth, .timeout_secs =  timeout_secs, .execution_limit =  execution_limit, .stack_overflow_detection =  stack_overflow_detection, .backend =  backend, .force_interpret =  force_interpret, .interpreter_mode =  interpreter_mode, .run_config =  run_config, .no_jit =  no_jit, .jit_threshold =  jit_threshold};
}

void apply_fault_detection(long long flags) {
    if (flags.max_recursion_depth > 0) {
        fault_set_max_recursion_depth(flags.max_recursion_depth);
        fault_set_stack_overflow_detection(1);
    }
    if (flags.stack_overflow_detection) {
        fault_set_stack_overflow_detection(1);
    }
    if (flags.timeout_secs > 0) {
        fault_set_timeout(flags.timeout_secs);
    }
    if (flags.execution_limit > 0) {
        fault_set_execution_limit(flags.execution_limit);
    }
}

void apply_jit_env_vars(long long flags) {
    if (flags.no_jit) {
        env_set("SIMPLE_NO_JIT", "1");
    }
    if (flags.jit_threshold != 10) {
        const char* t = "{flags.jit_threshold}";
        env_set("SIMPLE_JIT_THRESHOLD", t);
    }
    if (strcmp(flags.backend, "auto") != 0) {
        env_set("SIMPLE_JIT_BACKEND", flags.backend);
    }
}

SimpleStringArray filter_internal_flags(SimpleStringArray args) {
    SimpleIntArray result = simple_new_int_array();
    int skip_next = 0;
    for (long long _idx_arg = 0; _idx_arg < args.len; _idx_arg++) { const char* arg = args.items[_idx_arg];
        if (skip_next) {
            skip_next = 0;
        } else if (strcmp(arg, "--max-recursion-depth") == 0 || strcmp(arg, "--timeout") == 0 || strcmp(arg, "--execution-limit") == 0 || strcmp(arg, "--interpreter-mode") == 0 || strcmp(arg, "--run-config") == 0 || strcmp(arg, "--jit-threshold") == 0) {
            skip_next = 1;
        } else if (!(simple_starts_with(arg, "--gc") && strcmp(arg, "--notui") != 0 && strcmp(arg, "--lang") != 0 && strcmp(arg, "--stack-overflow-detection") != 0 && strcmp(arg, "--no-stack-overflow-detection") != 0 && strcmp(arg, "--interpret") != 0 && strcmp(arg, "--interpret-optimized") != 0 && strcmp(arg, "--no-jit") != 0)) {
            if (!(simple_starts_with(arg, "--lang=") && !(simple_starts_with(arg, "--max-recursion-depth=") && !(simple_starts_with(arg, "--timeout=") && !(simple_starts_with(arg, "--execution-limit=") && !(simple_starts_with(arg, "--interpreter-mode") && !(simple_starts_with(arg, "--run-config") && !(simple_starts_with(arg, "--jit-threshold="))))))))) {
    //  Keep --backend flags (used by both JIT and compile commands)
                /* result.push(arg) */;
            }
        }
    }
    return result;
}

int main(void) {
    long long args = ;
    //  Early check: is this a self-contained binary?
    //  Only check when no args are passed (self-contained binaries run directly)
    //  or when args don't start with a known subcommand
    if (args.len == 0) {
        if () {
            return 0;
        }
    }
    long long flags = parse_global_flags(args);
    apply_fault_detection(flags);
    apply_jit_env_vars(flags);
    //  Load user-level DL config (~/.simple/dl.config.sdn) once at startup
    ;
    SimpleStringArray filtered_args = filter_internal_flags(args);
    //  If user explicitly requested a JIT backend but native JIT is absent, fail fast
    if (strcmp(flags.backend, "auto") != 0 && !(flags.force_interpret)) {
        if (!()) {
            print_error(simple_str_concat(simple_str_concat("requested JIT backend '", simple_int_to_str(flags.backend)), "' but runtime has no native exec_manager support"));
            return 1;
    //  If backend is auto and only soft JIT is present, inform user once.
        }
    }
    if (strcmp(flags.backend, "auto") == 0 && !(flags.force_interpret)) {
        if (!( && )) {
            puts("[jit] Using soft exec_manager fallback (interpreted); native JIT not present.");
        }
    }
    if (filtered_args.len == 0) {
        return cli_run_repl(flags.gc_log, flags.gc_off);
    }
    long long first = filtered_args[0];
    { long long _match_val = first;
        if (strcmp(_match_val, "-h" | "--help") == 0) {
            ;
            return 0;
        }
        if (strcmp(_match_val, "-v" | "--version") == 0) {
            ;
            return 0;
        }
        if (strcmp(_match_val, "-c") == 0) {
            if (filtered_args.len < 2) {
                print_error("-c requires a code argument");
                return 1;
            }
            return cli_run_code(filtered_args[1], flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "compile") == 0) {
            return cli_compile(filtered_args);
        }
        if (strcmp(_match_val, "targets") == 0) {
            ;
            return 0;
        }
        if (strcmp(_match_val, "linkers") == 0) {
            ;
            return 0;
        }
        if (strcmp(_match_val, "web") == 0) {
            return cli_handle_web(filtered_args);
        }
        if (strcmp(_match_val, "watch") == 0) {
            if (filtered_args.len < 2) {
                print_error("watch requires a source file");
                return 1;
            }
            return cli_watch_file(filtered_args[1]);
        }
        if (strcmp(_match_val, "test") == 0) {
            long long test_args = filtered_args[1:];
            return cli_run_tests(test_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "lex") == 0) {
            if (filtered_args.len < 2) {
                print_error("lex requires a source file");
                return 1;
            }
            return run_lex_command(filtered_args[1]);
        }
        if (strcmp(_match_val, "lint") == 0) {
            return cli_run_lint(filtered_args);
        }
        if (strcmp(_match_val, "duplicate-check") == 0) {
            return cli_run_file("src/app/duplicate_check/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "fix") == 0) {
            return cli_run_fix(filtered_args);
        }
        if (strcmp(_match_val, "fmt") == 0) {
            return cli_run_fmt(filtered_args);
        }
        if (strcmp(_match_val, "check") == 0) {
            long long check_args = filtered_args[1:];
            return run_check(check_args);
        }
        if (strcmp(_match_val, "doc-coverage") == 0) {
            long long dc_args = filtered_args[1:];
            return run_doc_coverage(dc_args);
        }
        if (strcmp(_match_val, "check-arch") == 0) {
            long long arch_args = filtered_args[1:];
            return run_arch_check(arch_args);
        }
        if (strcmp(_match_val, "check-dbs") == 0) {
            long long check_db_args = filtered_args[1:];
            return run_check_dbs(check_db_args);
        }
        if (strcmp(_match_val, "fix-dbs") == 0) {
            long long fix_db_args = filtered_args[1:];
            return run_fix_dbs(fix_db_args);
        }
        if (strcmp(_match_val, "grammar-doc") == 0) {
            long long grammar_args = filtered_args[1:];
            return cli_run_file("src/app/grammar_doc/mod.spl", grammar_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "i18n") == 0) {
            return cli_run_i18n(filtered_args);
        }
        if (strcmp(_match_val, "migrate") == 0) {
            return cli_run_migrate(filtered_args);
        }
        if (strcmp(_match_val, "mcp") == 0) {
            return cli_run_mcp(filtered_args);
        }
        if (strcmp(_match_val, "lsp") == 0) {
            return cli_run_lsp(filtered_args);
        }
        if (strcmp(_match_val, "diff") == 0) {
            return cli_run_diff(filtered_args);
        }
        if (strcmp(_match_val, "constr") == 0) {
            return cli_constr(filtered_args);
        }
        if (strcmp(_match_val, "query") == 0) {
            return cli_run_query(filtered_args);
        }
        if (strcmp(_match_val, "info") == 0) {
            return cli_info(filtered_args);
        }
        if (strcmp(_match_val, "spec-coverage") == 0) {
            return cli_run_spec_coverage(filtered_args);
        }
        if (strcmp(_match_val, "replay") == 0) {
            return cli_replay(filtered_args);
        }
        if (strcmp(_match_val, "gen-lean") == 0) {
            return cli_gen_lean(filtered_args);
        }
        if (strcmp(_match_val, "feature-gen") == 0) {
            return cli_run_feature_gen(filtered_args);
        }
        if (strcmp(_match_val, "task-gen") == 0) {
            return cli_run_task_gen(filtered_args);
        }
        if (strcmp(_match_val, "spec-gen") == 0) {
            return cli_run_spec_gen(filtered_args);
        }
        if (strcmp(_match_val, "sspec-docgen") == 0) {
            return cli_run_sspec_docgen(filtered_args);
        }
        if (strcmp(_match_val, "feature-doc") == 0) {
            return cli_run_feature_doc(filtered_args);
        }
        if (strcmp(_match_val, "todo-scan") == 0) {
            return cli_todo_scan(filtered_args);
        }
        if (strcmp(_match_val, "todo-gen") == 0) {
            return cli_run_todo_gen(filtered_args);
        }
        if (strcmp(_match_val, "brief") == 0) {
            return cli_run_brief(filtered_args);
        }
        if (strcmp(_match_val, "stats") == 0) {
            run_stats(filtered_args[1:]);
            return 0;
        }
        if (strcmp(_match_val, "ffi-gen") == 0) {
            return cli_run_ffi_gen(filtered_args);
        }
        if (strcmp(_match_val, "wrapper-gen") == 0) {
            return cli_run_file("src/app/wrapper_gen/mod.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "desugar") == 0) {
            return cli_run_file("src/app/desugar/mod.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "dashboard") == 0) {
            long long dashboard_args = filtered_args[1:];
            return cli_run_file("src/app/dashboard/main.spl", dashboard_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "verify") == 0) {
            return cli_run_verify(filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "diagram") == 0) {
            return cli_handle_diagram(filtered_args);
        }
        if (strcmp(_match_val, "build") == 0) {
            long long build_args = filtered_args[1:];
            return handle_build(build_args);
        }
        if (strcmp(_match_val, "init") == 0) {
            return handle_init(filtered_args);
        }
        if (strcmp(_match_val, "add") == 0) {
            return cli_run_file("src/app/add/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "remove") == 0) {
            return cli_run_file("src/app/remove/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "install") == 0) {
            return cli_run_file("src/app/install/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "update") == 0) {
            return cli_run_file("src/app/update/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "list") == 0) {
            return cli_run_file("src/app/list/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "tree") == 0) {
            return cli_run_file("src/app/tree/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "cache") == 0) {
            return cli_run_file("src/app/cache/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "env") == 0) {
            return cli_run_file("src/app/env/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "lock") == 0) {
            return cli_run_file("src/app/lock/main.spl", filtered_args, flags.gc_log, flags.gc_off);
        }
        if (strcmp(_match_val, "run") == 0) {
            return cli_handle_run(filtered_args, flags.gc_log, flags.gc_off);
        /* default: */
            if (cli_file_exists(first)) {
                SimpleIntArray program_args = simple_new_int_array(); simple_int_push(&program_args, first);
                long long j = 1;
                while (j < filtered_args.len) {
                    /* program_args.push(filtered_args[j]) */;
                    j = j + 1;
                }
                return cli_run_file(first, program_args, flags.gc_log, flags.gc_off);
            } else {
                print_error_with_help(simple_str_concat("file not found: ", simple_int_to_str(first)));
                return 1;
            }
        }
    }
    return 0;
}
