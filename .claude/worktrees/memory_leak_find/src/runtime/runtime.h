/*
 * Simple Bootstrap Runtime Library
 *
 * Provides the core data types and operations needed by the bootstrap compiler:
 * - Tagged values (SplValue): nil, bool, i64, f64, text, array, dict
 * - String operations with interning-friendly hashing
 * - Dynamic arrays (heterogeneous via SplValue, or typed i64/text)
 * - Hash-table dictionaries (open addressing, text keys)
 * - File I/O and formatting
 *
 * Design: All functions use spl_ prefix. Values are passed by pointer
 * or as opaque i64 handles. The bootstrap compiler emits C code that
 * calls these functions directly.
 */

#ifndef SPL_RUNTIME_H
#define SPL_RUNTIME_H

#ifdef __cplusplus
extern "C" {
#endif

#include <stdint.h>
#include <stddef.h>
#include <stdbool.h>

/* Include threading library */
#include "runtime_thread.h"

/* Include memory tracking */
#include "runtime_memtrack.h"

/* Include fork-without-exec support */
#include "runtime_fork.h"

/* ===== Tagged Value System ===== */

typedef enum {
    SPL_NIL = 0,
    SPL_BOOL,
    SPL_INT,
    SPL_FLOAT,
    SPL_STRING,
    SPL_ARRAY,
    SPL_DICT
} SplTag;

/* Forward declarations */
typedef struct SplArray SplArray;
typedef struct SplDict SplDict;

typedef struct SplValue {
    SplTag tag;
    union {
        int64_t as_bool;    /* 0 or 1 */
        int64_t as_int;
        double  as_float;
        char*   as_str;     /* owned, heap-allocated, null-terminated */
        SplArray* as_array;
        SplDict*  as_dict;
    };
} SplValue;

/* ===== Value Constructors ===== */

SplValue spl_nil(void);
SplValue spl_bool(int64_t b);
SplValue spl_int(int64_t n);
SplValue spl_float(double f);
SplValue spl_str(const char* s);       /* copies the string */
SplValue spl_str_own(char* s);         /* takes ownership (no copy) */
SplValue spl_array_val(SplArray* a);
SplValue spl_dict_val(SplDict* d);

/* ===== Value Accessors (unchecked — caller must verify tag) ===== */

int64_t  spl_as_bool(SplValue v);
int64_t  spl_as_int(SplValue v);
double   spl_as_float(SplValue v);
const char* spl_as_str(SplValue v);
SplArray*   spl_as_array(SplValue v);
SplDict*    spl_as_dict(SplValue v);

/* ===== Value Operations ===== */

int      spl_is_truthy(SplValue v);
int      spl_eq(SplValue a, SplValue b);
SplValue spl_to_string(SplValue v);     /* convert any value to text */
void     spl_free_value(SplValue v);    /* deep free */

/* ===== String Operations ===== */

char*    spl_str_new(const char* s);             /* strdup wrapper */
char*    spl_str_concat(const char* a, const char* b);
int64_t  spl_str_len(const char* s);
int      spl_str_eq(const char* a, const char* b);
int      spl_str_cmp(const char* a, const char* b);  /* strcmp wrapper */
char*    spl_str_slice(const char* s, int64_t start, int64_t end);
char*    spl_str_index_char(const char* s, int64_t idx); /* single char as string */
uint64_t spl_str_hash(const char* s);            /* FNV-1a hash */
int      spl_str_contains(const char* s, const char* needle);
int      spl_str_starts_with(const char* s, const char* prefix);
int      spl_str_ends_with(const char* s, const char* suffix);
char*    spl_str_replace(const char* s, const char* old_s, const char* new_s);
char*    spl_str_trim(const char* s);
int64_t  spl_str_index_of(const char* s, const char* needle);
int64_t  spl_str_last_index_of(const char* s, const char* needle);
char*    spl_str_to_upper(const char* s);
char*    spl_str_to_lower(const char* s);

/* ===== Dynamic Array ===== */

struct SplArray {
    SplValue* items;
    int64_t   len;
    int64_t   cap;
};

SplArray* spl_array_new(void);
SplArray* spl_array_new_cap(int64_t cap);
SplArray* spl_array_push(SplArray* a, SplValue v);
SplValue  spl_array_get(SplArray* a, int64_t idx);
void      spl_array_set(SplArray* a, int64_t idx, SplValue v);
int64_t   spl_array_len(SplArray* a);
SplValue  spl_array_pop(SplArray* a);
SplArray* spl_array_slice(SplArray* a, int64_t start, int64_t end);
SplArray* spl_array_concat(SplArray* a, SplArray* b);
void      spl_array_free(SplArray* a);  /* deep free all elements */
int       spl_array_contains_str(SplArray* a, const char* needle);
SplArray* spl_str_split(const char* s, const char* delim);
char*     spl_str_join(SplArray* arr, const char* delim);

/* Typed convenience: i64 arrays */
SplArray* spl_array_new_i64(void);
void      spl_array_push_i64(SplArray* a, int64_t n);
int64_t   spl_array_get_i64(SplArray* a, int64_t idx);
void      spl_array_set_i64(SplArray* a, int64_t idx, int64_t n);

/* Typed convenience: text arrays */
SplArray* spl_array_new_text(void);
void      spl_array_push_text(SplArray* a, const char* s);
const char* spl_array_get_text(SplArray* a, int64_t idx);

/* ===== Hash-Table Dictionary (text keys -> SplValue) ===== */

typedef struct {
    char*    key;       /* owned string, NULL = empty slot */
    SplValue value;
    uint64_t hash;      /* cached hash */
    int      occupied;  /* 1 = occupied, 0 = empty, -1 = tombstone */
} SplDictEntry;

struct SplDict {
    SplDictEntry* entries;
    int64_t       cap;       /* always power of 2 */
    int64_t       len;       /* number of live entries */
    int64_t       tombstones;
};

SplDict*  spl_dict_new(void);
SplDict*  spl_dict_new_cap(int64_t cap);
void      spl_dict_set(SplDict* d, const char* key, SplValue value);
SplValue  spl_dict_get(SplDict* d, const char* key);  /* returns spl_nil() if missing */
int       spl_dict_contains(SplDict* d, const char* key);
SplArray* spl_dict_keys(SplDict* d);   /* returns text array */
SplArray* spl_dict_values(SplDict* d); /* returns value array */
int64_t   spl_dict_len(SplDict* d);
void      spl_dict_remove(SplDict* d, const char* key);
void      spl_dict_free(SplDict* d);   /* deep free all entries */

/* ===== File I/O ===== */

char*    spl_file_read(const char* path);
int      spl_file_write(const char* path, const char* content);
int      spl_file_append(const char* path, const char* content);
int      spl_file_exists(const char* path);
int      spl_file_delete(const char* path);
int64_t  spl_file_size(const char* path);

/* ===== Directory Operations ===== */

bool     rt_dir_create(const char* path, bool recursive);
bool     rt_dir_remove_all(const char* path);
const char** rt_dir_list(const char* path, int64_t* out_count);
void     rt_dir_list_free(const char** entries, int64_t count);

/* ===== File Locking ===== */

int64_t  rt_file_lock(const char* path, int64_t timeout_secs);
bool     rt_file_unlock(int64_t handle);

/* ===== Offset-based File I/O ===== */

const char* rt_file_read_text_at(const char* path, int64_t offset, int64_t size);
int64_t     rt_file_write_text_at(const char* path, int64_t offset, const char* data);

/* ===== Memory-Mapped File I/O ===== */

void*    rt_mmap(const char* path, int64_t size, int64_t offset, bool readonly);
bool     rt_munmap(void* addr, int64_t size);
bool     rt_madvise(void* addr, int64_t size, int64_t advice);
bool     rt_msync(void* addr, int64_t size);

/* ===== High-Resolution Time ===== */

int64_t  rt_time_now_nanos(void);   /* Nanosecond precision monotonic time */
int64_t  rt_time_now_micros(void);  /* Microsecond precision monotonic time */

/* ===== Output ===== */

void     spl_print(const char* s);
void     spl_println(const char* s);
void     spl_print_i64(int64_t n);
void     spl_print_f64(double f);

/* ===== Formatting ===== */

char*    spl_i64_to_str(int64_t n);
char*    spl_f64_to_str(double f);

/* ===== Bit-cast Helpers (f64 <-> i64 for DynLoader) ===== */

int64_t  spl_f64_to_bits(double f);
double   spl_bits_to_f64(int64_t bits);
int64_t  spl_str_ptr(const char* s);           /* cast text pointer to i64 */

char*    spl_sprintf(const char* fmt, ...);

/* ===== Process ===== */

int64_t  spl_shell(const char* cmd);
char*    spl_shell_output(const char* cmd);  /* capture stdout */

/* ===== Process Async ===== */

int64_t  rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count);
int64_t  rt_process_wait(int64_t pid, int64_t timeout_ms);
bool     rt_process_is_running(int64_t pid);
bool     rt_process_kill(int64_t pid);

/* ===== Environment ===== */

const char* spl_env_get(const char* key);
const char* rt_env_get(const char* key);
void        spl_env_set(const char* key, const char* value);
bool        rt_env_set(const char* key, const char* value);

/* ===== Cross-Platform System Functions ===== */

char*    rt_getcwd(void);
bool     rt_is_dir(const char* path);
bool     rt_rename(const char* src, const char* dst);
void     rt_sleep_ms_native(int64_t ms);
int64_t  rt_getpid(void);
char*    rt_hostname(void);
int64_t  rt_thread_available_parallelism(void);
int64_t  rt_time_now_unix_micros(void);

/* ===== Memory ===== */

void*    spl_malloc(int64_t size);
void     spl_free(void* ptr);
char*    spl_strdup(const char* s);

/* ===== Command-Line Arguments ===== */

void        spl_init_args(int argc, char** argv);
int64_t     spl_arg_count(void);
const char* spl_get_arg(int64_t idx);

/* ===== rt_ Aliases (FFI-compatible wrappers) ===== */

const char* rt_file_read_text(const char* path);
int         rt_file_exists(const char* path);
int         rt_file_write(const char* path, const char* content);
int         rt_file_append(const char* path, const char* content);
int         rt_file_delete(const char* path);
int         rt_file_copy(const char* src, const char* dst);
int64_t     rt_file_size(const char* path);
int64_t     rt_file_stat(const char* path);
const char* rt_shell_output(const char* cmd);
SplArray*   rt_cli_get_args(void);
SplArray*   rt_dir_walk(const char* path);
SplArray*   rt_dir_list_array(const char* path);

/* ===== Dynamic Loading (WFFI) ===== */

void*    spl_dlopen(const char* path);
void*    spl_dlsym(void* handle, const char* name);
int64_t  spl_dlclose(void* handle);
int64_t  spl_wffi_call_i64(void* fptr, int64_t* args, int64_t nargs);

/* ===== JIT Exec Manager (stubs) ===== */

int64_t  rt_exec_manager_create(const char* backend);
const char* rt_exec_manager_compile(int64_t handle, const char* mir_data);
int64_t  rt_exec_manager_execute(int64_t handle, const char* name, SplArray* args);
bool     rt_exec_manager_has_function(int64_t handle, const char* name);
void     rt_exec_manager_cleanup(int64_t handle);

/* ===== Stderr output ===== */
void     spl_eprintln(const char* s);

/* ===== Panic / Abort ===== */

#ifdef _MSC_VER
__declspec(noreturn) void spl_panic(const char* msg);
#else
void     spl_panic(const char* msg) __attribute__((noreturn));
#endif

#ifdef __cplusplus
}
#endif

#endif /* SPL_RUNTIME_H */
