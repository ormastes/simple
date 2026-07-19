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

/* ===== Runtime Configuration ===== */

void rt_set_macro_trace(bool enabled);
bool rt_is_macro_trace_enabled(void);
void rt_set_debug_mode(bool enabled);
bool rt_is_debug_mode_enabled(void);

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
char*    spl_str_append(char* dest, const char* suffix); /* in-place realloc append */
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
int64_t     rt_file_write_text_at(int64_t path_value, int64_t offset_value, int64_t data_value);
int         rt_file_fsync(const char* path);
int         rt_file_fsync_cached(const char* path);

/* ===== Memory-Mapped File I/O ===== */

void*    rt_mmap(const char* path, int64_t size, int64_t offset, bool readonly);
bool     rt_munmap(void* addr, int64_t size);
void     rt_invlpg(uint64_t addr);
uint64_t unsafe_addr_of(int64_t value);
uint64_t rt_read_cr3(void);
void     rt_write_cr3(uint64_t value);
uint64_t rt_read_cr3_raw(void);
void     rt_write_cr3_raw(uint64_t value);
int64_t  rt_volatile_read_u8(int64_t addr);
int64_t  rt_volatile_read_u16(int64_t addr);
int64_t  rt_volatile_read_u32(int64_t addr);
int64_t  rt_volatile_read_u64(int64_t addr);
void     rt_volatile_write_u8(int64_t addr, int64_t value);
void     rt_volatile_write_u16(int64_t addr, int64_t value);
void     rt_volatile_write_u32(int64_t addr, int64_t value);
void     rt_volatile_write_u64(int64_t addr, int64_t value);
void     rt_memory_barrier(void);
void     rt_load_barrier(void);
void     rt_store_barrier(void);
bool     rt_madvise(void* addr, int64_t size, int64_t advice);
bool     rt_msync(void* addr, int64_t size);

/* ===== Raw mmap/mprotect Syscall Wrappers (address-based, for SMF loader) ===== */

int64_t  rt_mmap_raw(int64_t addr, int64_t length, int64_t prot, int64_t flags, int64_t fd, int64_t offset);
int64_t  rt_munmap_raw(int64_t addr, int64_t length);
int64_t  rt_mprotect(int64_t addr, int64_t length, int64_t prot);
int64_t  rt_madvise_raw(int64_t addr, int64_t length, int64_t advice);
int64_t  rt_msync_flags(int64_t addr, int64_t length, int64_t flags);
int64_t  rt_mlock(int64_t addr, int64_t length);
int64_t  rt_munlock(int64_t addr, int64_t length);
int64_t  rt_open_fd(const char* path, int64_t flags, int64_t mode);
int64_t  rt_close_fd(int64_t fd);
int64_t  rt_page_size(void);

/* ===== High-Resolution Time ===== */

int64_t  rt_time_now_nanos(void);   /* Nanosecond precision monotonic time */
int64_t  rt_time_now_micros(void);  /* Microsecond precision monotonic time */
int64_t  rt_time_now_monotonic_ms(void);
int64_t  rt_time_ms(void);          /* Unix epoch milliseconds */

/* ===== Stdin/Stdout I/O ===== */

char*    rt_stdin_read_line(void);         /* reads line from stdin, NULL on EOF */
int64_t  rt_stdin_read_line_text(void);    /* reads line from stdin as tagged text, empty on EOF */
int64_t  rt_stdin_read_chars_text(int64_t count); /* reads up to count bytes from stdin as tagged text */
int64_t  rt_stdin_read_mcp_message_text(void); /* reads one MCP framed or JSON-lines message body */
int64_t  rt_mcp_initialize_response_text(int64_t message); /* native fast path for MCP initialize */
void     rt_mcp_write_framed_text(int64_t body); /* writes Content-Length framed tagged text */
int64_t  stdin_read_char(void);            /* reads one byte from stdin as tagged text */
int64_t  rt_stdout_write_text(const char* s); /* writes text without newline, returns len */
int64_t  print_raw(int64_t value);         /* writes tagged RuntimeValue to stdout */
int64_t  rt_stdout_write(int64_t value);   /* writes tagged RuntimeValue to stdout */
void     rt_stdout_flush(void);            /* flushes stdout */
int64_t  rt_stderr_write(int64_t value);   /* writes tagged RuntimeValue to stderr */
void     rt_stderr_flush(void);            /* flushes stderr */

/* ===== Minimal RuntimeValue ABI for core-c lane ===== */

void     __simple_runtime_init(void);
void     __simple_runtime_shutdown(void);
int64_t  rt_value_int(int64_t value);
int64_t  rt_value_as_int(int64_t value);
int64_t  rt_value_float(int64_t raw_bits);
int64_t  rt_value_bool(int64_t value);
int64_t  rt_value_nil(void);
void*    rt_alloc(int64_t size);
void*    rt_realloc(void* ptr, int64_t size);
void     rt_free(void* ptr);
void*    rt_memcpy(void* dst, const void* src, int64_t n);
void*    copy_mem(void* dst, const void* src, int64_t n);
void*    rt_memset(void* dst, int8_t val, int64_t n);
void     rt_exit(int64_t code);
int64_t  rt_time_now_unix(void);
int64_t  rt_entropy_hardware_ready(void);
void     rt_sleep_ms(int64_t ms);
void     rt_sleep_secs(int64_t seconds);
void     rt_panic(const char* msg);
int64_t  rt_string_new(const uint8_t* bytes, uint64_t len);
int64_t  rt_string_len(int64_t string);
const uint8_t* rt_string_data(int64_t string);
const char* rt_interp_cstr(int64_t value);
int64_t  rt_string_bytes(int64_t string);
int64_t  rt_string_chars(int64_t string);
int64_t  rt_string_builder_new(void);
int64_t  rt_string_builder_push(int64_t handle, int64_t string);
int64_t  rt_string_builder_finish(int64_t handle);
int64_t  rt_string_builder_len(int64_t handle);
void     rt_string_builder_free(int64_t handle);
int64_t  rt_string_char_code_at(int64_t string, int64_t index);
int64_t  rt_string_char_at(int64_t string, int64_t index);
int64_t  rt_string_concat(int64_t left, int64_t right);
int64_t  rt_strcat_tagged(int64_t left, int64_t right);
int64_t  rt_any_add(int64_t left, int64_t right);
int64_t  rt_len(int64_t value);
int64_t  rt_to_string(int64_t value);
int64_t  rt_raw_u64_to_string(int64_t raw);
int64_t  rt_raw_i64_to_string(int64_t raw);
int64_t  rt_value_to_string(int64_t value);
int64_t  rt_function_not_found(const uint8_t* name, uint64_t len);
int64_t  rt_interp_call(const uint8_t* name, uint64_t len, int64_t argc, int64_t argv);
SplArray* rt_array_new(int64_t cap);
SplArray* rt_array_new_uninit(int64_t cap);
SplArray* rt_array_new_with_cap_u64(int64_t cap);
SplArray* rt_byte_array_new(uint64_t cap);
SplArray* rt_byte_array_new_len(uint64_t len);
SplArray* rt_bytes_alloc(int64_t len);
int64_t  rt_array_len(SplArray* array);
int64_t  rt_array_len_safe(int64_t value);
int64_t  rt_array_get(SplArray* array, int64_t idx);
int64_t  rt_array_get_text(SplArray* array, int64_t idx);
void     rt_array_set(SplArray* array, int64_t idx, int64_t value);
int8_t   rt_array_set_text(SplArray* array, int64_t idx, int64_t value);
int8_t   rt_array_push(SplArray* array, int64_t value);
int8_t   rt_array_clear(SplArray* array);
int8_t   rt_array_push_i64_raw(SplArray* array, int64_t value);
int64_t  rt_array_get_i64_raw(SplArray* array, int64_t index);
SplArray* rt_array_concat(SplArray* a, SplArray* b);
SplArray* rt_array_repeat(int64_t value, int64_t count);
int64_t  rt_array_data_ptr(SplArray* array);
int64_t  rt_array_data_ptr_text(SplArray* array);
int64_t  rt_array_data_ptr_u8(SplArray* array);
int64_t  rt_array_header_ptr(SplArray* array);
int8_t   rt_array_set_len_known(int64_t header_ptr, int64_t len);
int8_t   rt_array_set_len_known_text(int64_t header_ptr, int64_t len);

/* ===== Hosted ROCm/HIP runtime ===== */

bool     rt_rocm_init(void);
bool     rt_rocm_shutdown(void);
bool     rt_rocm_is_available(void);
int64_t  rt_rocm_device_count(void);
int64_t  rt_rocm_device_get(int64_t id);
int64_t  rt_rocm_device_name(int64_t device);
int64_t  rt_rocm_device_memory(int64_t device);
int64_t  rt_rocm_device_identity(int64_t device);
bool     rt_rocm_set_device(int64_t device);
int64_t  rt_rocm_get_device(void);
int64_t  rt_rocm_malloc(int64_t size);
int64_t  rt_rocm_mem_alloc(int64_t size);
bool     rt_rocm_free(int64_t ptr);
bool     rt_rocm_mem_free(int64_t ptr);
bool     rt_rocm_memcpy_h2d(int64_t dst, int64_t src, int64_t size);
bool     rt_rocm_memcpy_htod(int64_t dst, int64_t src, int64_t size);
bool     rt_rocm_memcpy_d2h(int64_t dst, int64_t src, int64_t size);
bool     rt_rocm_memcpy_dtoh(int64_t dst, int64_t src, int64_t size);
bool     rt_rocm_memcpy_d2d(int64_t dst, int64_t src, int64_t size);
bool     rt_rocm_memset(int64_t ptr, int64_t value, int64_t size);
int64_t  rt_rocm_compile_hsaco(int64_t source);
int64_t  rt_rocm_module_load(int64_t source);
int64_t  rt_rocm_get_function(int64_t module, int64_t name);
int64_t  rt_rocm_kernel_get(int64_t module, int64_t name);
bool     rt_rocm_launch_kernel(int64_t function, int64_t grid_x, int64_t grid_y,
                              int64_t grid_z, int64_t block_x, int64_t block_y,
                              int64_t block_z, int64_t shared_mem, int64_t args);
bool     rt_rocm_unload_module(int64_t module);
bool     rt_rocm_synchronize(void);
int64_t  rt_rocm_create_stream(void);
bool     rt_rocm_destroy_stream(int64_t stream);
bool     rt_rocm_stream_synchronize(int64_t stream);
int64_t  rt_rocm_get_last_error(void);
int64_t  rt_engine2d_rocm_upload_pixels(int64_t dst, int64_t pixels, int64_t count);
int64_t  rt_engine2d_rocm_download_pixels(int64_t src, int64_t pixels, int64_t byte_size);
int64_t  rt_engine2d_rocm_upload_host_buf(int64_t dst, int64_t host_buf, int64_t byte_size);

int64_t  rt_bytes_u8_at(SplArray* array, int64_t idx);
int64_t  rt_bytes_u32_le_at(SplArray* array, int64_t idx);
int64_t  rt_bytes_u64_le_at(SplArray* array, int64_t idx);
int8_t   rt_bytes_u8_set(SplArray* array, int64_t idx, int64_t value);
int8_t   rt_typed_bytes_u8_push(SplArray* array, int64_t value);
int64_t  rt_typed_bytes_u8_unchecked(SplArray* array, int64_t idx);
int64_t  rt_typed_bytes_u32_le_at(SplArray* array, int64_t idx);
int64_t  rt_typed_bytes_u64_le_at(SplArray* array, int64_t idx);
int64_t  rt_typed_bytes_u64_le_unchecked(SplArray* array, int64_t idx);
int8_t   rt_typed_bytes_u32_le_set(SplArray* array, int64_t idx, int64_t value);
int8_t   rt_typed_bytes_u64_le_set(SplArray* array, int64_t idx, int64_t value);
int64_t  rt_typed_words_u32_at(SplArray* array, int64_t idx);
int8_t   rt_typed_words_u32_push(SplArray* array, int64_t value);
int8_t   rt_typed_words_u32_set(SplArray* array, int64_t idx, int64_t value);
int64_t  rt_typed_words_u64_at(SplArray* array, int64_t idx);
int8_t   rt_typed_words_u64_push(SplArray* array, int64_t value);
int8_t   rt_typed_words_u64_set(SplArray* array, int64_t idx, int64_t value);
int64_t  rt_typed_words_u64_raw_data_at(int64_t data_ptr, int64_t idx);
int8_t   rt_typed_words_u64_store_known_data_at(
    int64_t header_ptr,
    int64_t data_ptr,
    int64_t idx,
    int64_t value);
int64_t  rt_tuple_new(int64_t len);
int8_t   rt_tuple_set(int64_t tuple, int64_t idx, int64_t value);
int64_t  rt_tuple_get(int64_t tuple, int64_t idx);
int64_t  rt_tuple_len(int64_t tuple);
int64_t  rt_path_parent(const uint8_t* path_ptr, int64_t path_len);
int64_t  rt_path_filename(int64_t path_value);
int64_t  rt_path_extension(int64_t path_value);
int64_t  rt_http_get(int64_t url);
int64_t  rt_http_request(int64_t method, int64_t url, int64_t headers, int64_t body);
int64_t  rt_http_download(int64_t url, int64_t output_path);
int64_t  rt_http_client_create(void);
bool     rt_http_client_set_timeout(int64_t client, int64_t timeout_ms);
int64_t  rt_http_client_request(int64_t client, int64_t method, int64_t url,
                                int64_t headers, int64_t body);
void     rt_http_client_destroy(int64_t client);
int64_t  rt_gui_get_glyph_8x16(int32_t codepoint);
int64_t  rt_jit_cleanup(int64_t handle);
int64_t  rt_enum_new(int32_t enum_id, int32_t discriminant, int64_t payload);
int64_t  rt_enum_id(int64_t value);
int64_t  rt_enum_discriminant(int64_t value);
int64_t  rt_enum_payload(int64_t value);
int64_t  rt_closure_new(int64_t func_ptr, int64_t capture_count);
int64_t  rt_closure_set_capture(int64_t closure, int64_t index, int64_t value);
int64_t  rt_closure_get_capture(int64_t closure, int64_t index);
int64_t  rt_closure_func_ptr(int64_t closure);
int8_t   rt_enum_check_discriminant(int64_t value, int64_t expected);
int64_t  rt_hash_text(int64_t value);
int64_t  rt_text_eq_fast(int64_t left, int64_t right);
int64_t  rt_index_get(int64_t collection, int64_t idx);
int8_t   rt_index_set(int64_t collection, int64_t idx, int64_t value);
int64_t  rt_string_eq(int64_t left, int64_t right);
int64_t  rt_native_eq(int64_t left, int64_t right);
int64_t  rt_native_neq(int64_t left, int64_t right);
int64_t  rt_text_eq_any(int64_t left, int64_t right);
int64_t  rt_slice(int64_t value, int64_t start, int64_t end, int64_t step);
int64_t  rt_string_starts_with(int64_t value, int64_t prefix);
int64_t  rt_string_ends_with(int64_t value, int64_t suffix);
int64_t  rt_string_find(int64_t value, int64_t needle);
int64_t  rt_text_find(int64_t value, int64_t needle, int64_t start);
int64_t  rt_string_rfind(int64_t value, int64_t needle);
int64_t  rt_string_to_lower(int64_t value);
int64_t  rt_string_to_upper(int64_t value);
int64_t  rt_string_split(int64_t value, int64_t delimiter);
int64_t  rt_string_join(int64_t array, int64_t separator);
int8_t   rt_contains(int64_t collection, int64_t value);
int64_t  rt_unwrap_or_self(int64_t value);
int8_t   rt_is_none(int64_t value);
int8_t   rt_is_some(int64_t value);
double   rt_math_pow(double base, double exponent);
int8_t   rt_dict_insert(int64_t dict, int64_t key, int64_t value);
int64_t  rt_dict_get_i64_raw(int64_t dict, int64_t key);
int8_t   rt_dict_set_i64_raw(int64_t dict, int64_t key, int64_t value);
int64_t  rt_string_replace(int64_t value, int64_t old_value, int64_t new_value);
int64_t  rt_string_trim(int64_t value);
int64_t  rt_string_trim_end(int64_t value);
int64_t  rt_string_to_int(int64_t value);
int64_t  rt_string_to_int_lenient(int64_t value);
void     rt_print_str(const uint8_t* ptr, uint64_t len);
void     rt_println_str(const uint8_t* ptr, uint64_t len);
void     rt_eprint_str(const uint8_t* ptr, uint64_t len);
void     rt_eprintln_str(const uint8_t* ptr, uint64_t len);
void     rt_print_value(int64_t value);
void     rt_println_value(int64_t value);
void     serial_println(int64_t value);
void     rt_eprint_value(int64_t value);
void     rt_eprintln_value(int64_t value);

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
SplArray* rt_process_run(const char* cmd, uint64_t cmd_len, SplArray* args);
int64_t   rt_process_run_inherit(const char* cmd, uint64_t cmd_len, SplArray* args);
int64_t   rt_process_run_inherit_value(int64_t cmd, SplArray* args);
SplArray* rt_process_run_timeout(const char* cmd, uint64_t cmd_len, SplArray* args, int64_t timeout_ms);
SplArray* rt_process_run_bounded(const char* cmd, uint64_t cmd_len, SplArray* args,
                                 int64_t timeout_ms, int64_t max_output_bytes);
#ifdef _WIN32
char* rt_windows_build_command_line(const char* cmd, const char** args, int64_t arg_count);
#endif

/* ===== Process Async ===== */

int64_t  rt_process_spawn_async(const char* cmd, const char** args, int64_t arg_count);
int64_t  rt_process_wait(int64_t pid, int64_t timeout_ms);
bool     rt_process_is_running(int64_t pid);
bool     rt_process_kill(int64_t pid);

/* ===== Process Piped (editor LSP transport) ===== */

int64_t     rt_process_spawn_piped(const char* cmd, SplArray* args);
bool        rt_process_write_stdin(int64_t pid, const char* data);
const char* rt_process_read_stdout(int64_t pid);
bool        rt_process_is_alive(int64_t pid);
int64_t     rt_editor_spawn_simple_dap(void);
bool        rt_editor_start_simple_dap(int64_t pid);
bool        rt_editor_poll_simple_dap_stopped(int64_t pid);
bool        rt_editor_wait_simple_dap_stopped(int64_t pid);

/* ===== Environment ===== */

const char* spl_env_get(const char* key);
int64_t     rt_env_get(const uint8_t* key, uint64_t key_len);
int64_t     rt_env_get_i64(const uint8_t* key, uint64_t key_len, int64_t default_value);
void        spl_env_set(const char* key, const char* value);
bool        rt_env_set(const uint8_t* key, uint64_t key_len, const uint8_t* value, uint64_t value_len);
bool        rt_lexer_source_set(const uint8_t* source, uint64_t source_len);
int64_t     rt_lexer_source_slice(int64_t start, int64_t end);
const char* rt_platform_name(void);
int64_t     rt_term_enable_ansi(void);
int64_t     rt_path_join(const uint8_t* left, uint64_t left_len, const uint8_t* right, uint64_t right_len);

/* ===== Cross-Platform System Functions ===== */

char*    rt_getcwd(void);
char*    rt_env_cwd(void);
bool     rt_is_dir(const char* path);
bool     rt_rename(const char* src, const char* dst);
void     rt_sleep_ms_native(int64_t ms);
int64_t  rt_getpid(void);
char*    rt_hostname(void);
int64_t  rt_thread_available_parallelism(void);
void     rt_thread_sleep(int64_t millis);
int64_t  rt_time_now_unix_micros(void);

int64_t  rt_signal_install(int64_t signal_num);
int64_t  rt_signal_check(int64_t signal_num);
int64_t  rt_atexit_install(void);
int64_t  rt_atexit_check(void);

/* ===== Memory ===== */

void*    spl_malloc(int64_t size);
void     spl_free(void* ptr);
char*    spl_strdup(const char* s);

/* ===== Atomic Handles ===== */

int64_t  rt_atomic_int_new(int64_t initial);
int64_t  rt_atomic_int_load(int64_t handle);
void     rt_atomic_int_store(int64_t handle, int64_t value);
int64_t  rt_atomic_int_swap(int64_t handle, int64_t value);
bool     rt_atomic_int_compare_exchange(int64_t handle, int64_t current, int64_t new_value);
int64_t  rt_atomic_int_fetch_add(int64_t handle, int64_t value);
int64_t  rt_atomic_int_fetch_sub(int64_t handle, int64_t value);
int64_t  rt_atomic_int_fetch_and(int64_t handle, int64_t value);
int64_t  rt_atomic_int_fetch_or(int64_t handle, int64_t value);
int64_t  rt_atomic_int_fetch_xor(int64_t handle, int64_t value);
void     rt_atomic_int_free(int64_t handle);
int64_t  rt_atomic_bool_new(bool initial);
bool     rt_atomic_bool_load(int64_t handle);
void     rt_atomic_bool_store(int64_t handle, bool value);
bool     rt_atomic_bool_swap(int64_t handle, bool value);
void     rt_atomic_bool_free(int64_t handle);
void     rt_bdd_describe_start_rv(int64_t name_rv);
void     rt_bdd_describe_end(void);
void     rt_bdd_it_start_rv(int64_t name_rv);
void     rt_bdd_it_end(int64_t passed);
int64_t  rt_bdd_has_failure(void);
void     rt_bdd_expect_fail(int64_t msg_ptr, int64_t msg_len);
void     rt_bdd_expect_eq_rv(int64_t actual, int64_t expected);
void     rt_bdd_expect_truthy_rv(int64_t value);
int64_t  rt_bdd_format_results(void);
void     rt_bdd_clear_state(void);

/* ===== Command-Line Arguments ===== */

void        spl_init_args(int argc, char** argv);
int64_t     spl_arg_count(void);
const char* spl_get_arg(int64_t idx);
void        rt_set_args(int argc, char** argv);
int32_t     rt_get_argc(void);
SplArray*   rt_get_args(void);

/* ===== File Prefetch (CLI keyword support) ===== */

void        spl_prefetch_start(const char* path);  /* warm page cache via fork+madvise */
void        spl_prefetch_wait(void);               /* reap prefetch child */
void        rt_prefetch_start(const char* path);   /* FFI alias */
void        rt_prefetch_wait(void);                /* FFI alias */

/* ===== rt_ Aliases (FFI-compatible wrappers) ===== */

const char* rt_file_read_text(const char* path);
int64_t     rt_file_read_text_rv(int64_t path);
int         rt_file_exists(const char* path);
int         rt_dir_exists(const char* path);
int         rt_file_write(const char* path, const char* content);
int         rt_file_write_text(const uint8_t* path, uint64_t path_len, const uint8_t* content, uint64_t content_len);
int         rt_file_append(const char* path, const char* content);
int         rt_file_append_text(const uint8_t* path, uint64_t path_len, const uint8_t* content, uint64_t content_len);
int         rt_file_delete(const char* path);
int         rt_file_copy(const char* src, const char* dst);
int64_t     rt_file_size(const char* path);
int         rt_file_fsync(const char* path);
int         rt_file_fsync_cached(const char* path);
int         rt_file_sync(const char* path, int64_t path_len);
int64_t     rt_crc32_text(const char* text, int64_t text_len);
int         rt_file_create_excl(const char* path, int64_t path_len,
                                const char* content, int64_t content_len);
int64_t     rt_file_stat(const char* path);
const char* rt_shell_output(const char* cmd);
SplArray*   rt_cli_get_args(void);
int64_t     rt_cli_arg_count(void);
#if defined(SPL_LEGACY_VALUE_RUNTIME)
SplValue    rt_cli_arg_at(int64_t index);
#else
int64_t     rt_cli_arg_at(int64_t index);
#endif
SplArray*   rt_dir_walk(const char* path);
SplArray*   rt_dir_list_array(const char* path);
int         rt_dir_create_all(const char* path);
int         rt_mkdir_p(const char* path);

/* ===== Dynamic Loading (WFFI) ===== */
int64_t spl_dlopen(int64_t path_value);
int64_t spl_dlsym(int64_t handle, int64_t name_value);
int64_t spl_dlclose(int64_t handle);

/* ===== JIT Exec Manager (stubs) ===== */

int64_t  rt_exec_manager_create(const char* backend);
const char* rt_exec_manager_compile(int64_t handle, const char* mir_data);
int64_t  rt_exec_manager_execute(int64_t handle, const char* name, SplArray* args);
bool     rt_exec_manager_has_function(int64_t handle, const char* name);
void     rt_exec_manager_cleanup(int64_t handle);

/* ===== Stderr output ===== */
void     spl_eprintln(const char* s);

/* ===== Power ===== */
int64_t  __simple_pow(int64_t base, int64_t exp);

/* ===== Intrinsics (C backend stubs) ===== */
int64_t  __simple_intrinsic_unreachable(void);
int64_t  __simple_intrinsic_trap(void);
int64_t  __simple_intrinsic_assume(int64_t cond);
int64_t  __simple_intrinsic_likely(int64_t cond);
int64_t  __simple_intrinsic_unlikely(int64_t cond);
int64_t  __simple_intrinsic_bounds_check(int64_t index, int64_t len);
int64_t  __simple_intrinsic_prefetch(void* ptr);
int64_t  __simple_intrinsic_memcpy(void* dst, const void* src, int64_t n);
int64_t  __simple_intrinsic_memset(void* dst, int64_t val, int64_t n);

/* ===== Async I/O Driver (FFI bridge) ===== */
/* Handle-based API: Simple's FFI passes i64, not pointers.               */
/* rt_driver_poll_* return completion fields by index since Simple can't   */
/* receive C structs directly.                                            */

int64_t     rt_driver_create(int64_t queue_depth);
void        rt_driver_destroy(int64_t handle);
int64_t     rt_driver_submit_accept(int64_t handle, int64_t listen_fd);
int64_t     rt_driver_submit_connect(int64_t handle, int64_t fd, const char* addr,
                                      int64_t addr_len, int64_t port);
int64_t     rt_driver_submit_recv(int64_t handle, int64_t fd, int64_t buf_size);
int64_t     rt_driver_submit_send(int64_t handle, int64_t fd, const char* data, int64_t len);
int64_t     rt_driver_submit_sendfile(int64_t handle, int64_t sock_fd, int64_t file_fd,
                                       int64_t offset, int64_t len);
int64_t     rt_driver_submit_read(int64_t handle, int64_t fd, int64_t buf_size, int64_t offset);
int64_t     rt_driver_submit_write(int64_t handle, int64_t fd, const char* data,
                                    int64_t len, int64_t offset);
int64_t     rt_driver_submit_open(int64_t handle, const char* path, int64_t path_len,
                                   int64_t flags, int64_t mode);
int64_t     rt_driver_submit_close(int64_t handle, int64_t fd);
int64_t     rt_driver_submit_fsync(int64_t handle, int64_t fd);
int64_t     rt_driver_submit_timeout(int64_t handle, int64_t timeout_ms);
int64_t     rt_driver_flush(int64_t handle);
int64_t     rt_driver_poll(int64_t handle, int64_t max, int64_t timeout_ms);
int64_t     rt_driver_poll_id(int64_t handle, int64_t index);
int64_t     rt_driver_poll_result(int64_t handle, int64_t index);
int64_t     rt_driver_poll_flags(int64_t handle, int64_t index);
bool        rt_driver_cancel(int64_t handle, int64_t op_id);
int64_t     rt_driver_backend_name(int64_t handle);
bool        rt_driver_supports_sendfile(int64_t handle);
bool        rt_driver_supports_zero_copy(int64_t handle);

/* ===== QMP Unix-Socket Primitives ===== */

int64_t     rt_unix_socket_connect(const char* path);
int64_t     rt_fd_write(int64_t fd, const char* data, int64_t len);
const char* rt_fd_read_until(int64_t fd, uint8_t stop_byte, int64_t max);
bool        rt_fd_close(int64_t fd);

/* ===== Legacy epoll/socket FFI (event_loop.spl) ===== */

int64_t     rt_epoll_create(void);
int64_t     rt_epoll_ctl(int64_t epfd, int64_t op, int64_t fd, int64_t events);
SplArray*   rt_epoll_wait(int64_t epfd, int64_t max_events, int64_t timeout_ms);
bool        rt_socket_set_nonblocking(int64_t fd, bool enabled);

/* ===== Raw 32-bit framebuffer operations ===== */

void        rt_fb_fill32(uint64_t dst_addr, uint64_t pixel_count, uint64_t color);
void        rt_fb_blit32(uint64_t dst_addr, uint64_t dst_stride_pixels,
                         uint64_t src_addr, uint64_t src_stride_pixels,
                         uint64_t copy_w, uint64_t copy_h);

/* ===== Audio (miniaudio backend) ===== */

int64_t  rt_audio_init(void);
void     rt_audio_shutdown(void);
int64_t  rt_audio_load_sound(const char* path);
void     rt_audio_unload_sound(int64_t handle);
int64_t  rt_audio_play(int64_t sound_handle);
int64_t  rt_audio_play_looped(int64_t sound_handle);
void     rt_audio_stop(int64_t playback_handle);
void     rt_audio_pause(int64_t playback_handle);
void     rt_audio_resume(int64_t playback_handle);
void     rt_audio_set_volume(int64_t playback_handle, double volume);
void     rt_audio_set_master_volume(double volume);
double   rt_audio_get_master_volume(void);
int64_t  rt_audio_is_playing(int64_t playback_handle);

/* ===== Audio spatial (3D positioning) ===== */

void     rt_audio_set_sound_position(int64_t playback_handle, double x, double y, double z);
void     rt_audio_set_spatialization_enabled(int64_t playback_handle, int64_t enabled);
void     rt_audio_set_listener_position(double x, double y, double z);
void     rt_audio_set_listener_direction(double x, double y, double z);
void     rt_audio_set_listener_world_up(double x, double y, double z);
void     rt_audio_set_sound_min_distance(int64_t playback_handle, double distance);
void     rt_audio_set_sound_max_distance(int64_t playback_handle, double distance);

/* ===== Image Loading (stb_image backend) ===== */

int64_t  rt_image_load(const char* path);
void     rt_image_free(int64_t handle);
int64_t  rt_image_width(int64_t handle);
int64_t  rt_image_height(int64_t handle);
int64_t  rt_image_channels(int64_t handle);
int64_t  rt_image_get_pixel(int64_t handle, int64_t x, int64_t y);

/* ===== Font Rendering (stb_truetype backend) ===== */

int64_t  rt_font_load(const char* path);
int64_t  rt_font_load_bytes(int64_t data_ptr, int64_t size);
void     rt_font_free(int64_t handle);
int64_t  rt_font_glyph_bitmap(int64_t font_handle, int64_t codepoint, double size);
int64_t  rt_font_glyph_index(int64_t font_handle, int64_t codepoint);
int64_t  rt_font_glyph_bitmap_index(int64_t font_handle, int64_t glyph_index, double size);
int64_t  rt_font_bitmap_width(int64_t bitmap_handle);
int64_t  rt_font_bitmap_height(int64_t bitmap_handle);
int64_t  rt_font_bitmap_xoff(int64_t bitmap_handle);
int64_t  rt_font_bitmap_yoff(int64_t bitmap_handle);
int64_t  rt_font_bitmap_get_pixel(int64_t bitmap_handle, int64_t x, int64_t y);
void     rt_font_bitmap_free(int64_t bitmap_handle);
int64_t  rt_font_glyph_advance(int64_t font_handle, int64_t codepoint, double size);
int64_t  rt_font_glyph_advance_index(int64_t font_handle, int64_t glyph_index, double size);
int64_t  rt_font_line_height(int64_t font_handle, double size);
int64_t  rt_font_ascent(int64_t font_handle, double size);
int64_t  rt_font_descent(int64_t font_handle, double size);
int64_t  rt_font_line_gap(int64_t font_handle, double size);

/* ===== SDL2 Windowing Runtime ===== */

/* Initialization */
int64_t  rt_sdl2_init(void);
void     rt_sdl2_quit(void);

/* Window management */
int64_t  rt_sdl2_create_window(const char* title, int64_t width, int64_t height);
void     rt_sdl2_destroy_window(int64_t handle);
int64_t  rt_sdl2_get_window_width(int64_t handle);
int64_t  rt_sdl2_get_window_height(int64_t handle);
void     rt_sdl2_set_window_title(int64_t handle, const char* title);

/* Framebuffer present (pixels = SplArray* of packed i64 RGBA) */
bool     rt_sdl2_present_rgba(int64_t window_handle, SplArray* pixels,
                              int64_t width, int64_t height);

/* Event polling (returns event type code: 0=none, 1=quit, 2=keydown, etc.) */
int64_t  rt_sdl2_poll_event(void);
int64_t  rt_sdl2_event_key_code(void);
int64_t  rt_sdl2_event_key_sym(void);
int64_t  rt_sdl2_event_key_mod(void);
const char* rt_sdl2_event_text(void);
int64_t  rt_sdl2_event_mouse_x(void);
int64_t  rt_sdl2_event_mouse_y(void);
int64_t  rt_sdl2_event_mouse_button(void);
int64_t  rt_sdl2_event_wheel_x(void);
int64_t  rt_sdl2_event_wheel_y(void);

/* Keyboard state (polled) */
int64_t  rt_sdl2_is_key_pressed(int64_t scancode);

/* Mouse state (polled) */
int64_t  rt_sdl2_get_mouse_x(void);
int64_t  rt_sdl2_get_mouse_y(void);
int64_t  rt_sdl2_is_mouse_button_pressed(int64_t button);

/* Time */
int64_t  rt_sdl2_get_ticks_ms(void);
int64_t  rt_sdl2_get_ticks_ns(void);

/* Window state */
int64_t  rt_sdl2_window_should_close(void);
void     rt_sdl2_clear_quit(void);

/* SDL editor-facing aliases. These forward to the existing SDL2 backend. */
int64_t  rt_sdl_init(void);
void     rt_sdl_quit(void);
int64_t  rt_sdl_create_window(const char* title, int64_t width, int64_t height);
void     rt_sdl_destroy_window(int64_t handle);
int64_t  rt_sdl_get_window_width(int64_t handle);
int64_t  rt_sdl_get_window_height(int64_t handle);
void     rt_sdl_set_window_title(int64_t handle, const char* title);
bool     rt_sdl_present_rgba(int64_t window_handle, SplArray* pixels,
                             int64_t width, int64_t height);
int64_t  rt_sdl_poll_event(void);
int64_t  rt_sdl_event_key_sym(void);
int64_t  rt_sdl_event_key_mod(void);
const char* rt_sdl_event_text(void);
int64_t  rt_sdl_event_mouse_x(void);
int64_t  rt_sdl_event_mouse_y(void);
int64_t  rt_sdl_event_mouse_button(void);
int64_t  rt_sdl_window_should_close(void);
void     rt_sdl_clear_quit(void);
int64_t  rt_sdl_event_window_event_id(void);
int64_t  rt_sdl_event_window_data1(void);
int64_t  rt_sdl_event_window_data2(void);

/* Window events */
int64_t  rt_sdl2_event_window_event_id(void);
int64_t  rt_sdl2_event_window_data1(void);
int64_t  rt_sdl2_event_window_data2(void);

/* Window properties */
void     rt_sdl2_set_window_resizable(int64_t handle, int64_t resizable);
void     rt_sdl2_set_window_fullscreen(int64_t handle, int64_t fullscreen);
void     rt_sdl2_set_window_size(int64_t handle, int64_t width, int64_t height);
void     rt_sdl2_set_window_position(int64_t handle, int64_t x, int64_t y);
int64_t  rt_sdl2_get_window_position_x(int64_t handle);
int64_t  rt_sdl2_get_window_position_y(int64_t handle);
void     rt_sdl2_show_window(int64_t handle);
void     rt_sdl2_hide_window(int64_t handle);

/* Cursor */
void     rt_sdl2_set_cursor_visible(int64_t visible);
void     rt_sdl2_set_cursor_grab(int64_t handle, int64_t grab);
void     rt_sdl2_warp_mouse(int64_t handle, int64_t x, int64_t y);

/* Clipboard */
const char* rt_sdl2_clipboard_get(void);
bool     rt_sdl2_clipboard_set(const char* text);
bool     rt_sdl2_clipboard_has_text(void);

/* Display info */
int64_t  rt_sdl2_get_num_displays(void);
const char* rt_sdl2_get_display_name(int64_t index);
int64_t  rt_sdl2_get_display_bounds_x(int64_t index);
int64_t  rt_sdl2_get_display_bounds_y(int64_t index);
int64_t  rt_sdl2_get_display_bounds_w(int64_t index);
int64_t  rt_sdl2_get_display_bounds_h(int64_t index);
double   rt_sdl2_get_display_dpi(int64_t index);
int64_t  rt_sdl2_get_display_usable_x(int64_t index);
int64_t  rt_sdl2_get_display_usable_y(int64_t index);
int64_t  rt_sdl2_get_display_usable_w(int64_t index);
int64_t  rt_sdl2_get_display_usable_h(int64_t index);

/* ===== Panic / Abort ===== */

#ifdef _MSC_VER
__declspec(noreturn) void spl_panic(const char* msg);
#else
void     spl_panic(const char* msg) __attribute__((noreturn));
#endif
void     panic(int64_t msg);

/* ===== SIMD Text Dispatch ===== */

void     simd_text_init(void);
bool     rt_simd_has_sse(void);
bool     rt_simd_has_avx(void);
bool     rt_simd_has_avx2(void);
bool     rt_simd_has_neon(void);
bool     rt_simd_has_rvv(void);

/* ===== Engine2D CPU SIMD Span Kernels ===== */

int64_t  rt_engine2d_simd_fill_u32(SplArray* dst, int64_t offset, int64_t count, int64_t color);
int64_t  rt_engine2d_simd_copy_u32(SplArray* dst, int64_t dst_off, SplArray* src, int64_t src_off, int64_t count);
SplArray* rt_engine2d_simd_fill_span_u32(SplArray* dst, int64_t offset, int64_t count, int64_t color);
SplArray* rt_engine2d_simd_copy_span_u32(SplArray* dst, int64_t dst_off, SplArray* src, int64_t src_off, int64_t count);

/* RETURN-style row kernels: build and return a NEW SplArray of packed i64 pixels. */
SplArray* rt_engine2d_simd_fill_row_u32(int64_t count, int64_t color);
SplArray* rt_engine2d_simd_fill_rows_u32(int64_t width, int64_t height,
                                         int64_t color, int64_t worker_limit);
SplArray* rt_engine2d_simd_copy_row_u32(SplArray* src);
SplArray* rt_engine2d_simd_blend_row_u32(SplArray* dst, SplArray* src);

/* ===== Generic OpenCL ICD Runtime Hooks ===== */

bool     rt_opencl_is_available(void);
int64_t  rt_opencl_platform_count(void);
int64_t  rt_opencl_create_context(int64_t platform);
int64_t  rt_opencl_create_queue(int64_t context);
int64_t  rt_opencl_create_program(int64_t context, const char* source);
bool     rt_opencl_build_program(int64_t program);
int64_t  rt_opencl_create_kernel(int64_t program, const char* name);
int64_t  rt_opencl_mem_alloc(int64_t context, int64_t size);
bool     rt_opencl_mem_free(int64_t buffer);
bool     rt_opencl_write_buffer(int64_t queue, int64_t buffer, int64_t host_ptr, int64_t size);
bool     rt_opencl_write_buffer_at(int64_t queue, int64_t buffer, int64_t host_ptr, int64_t size, int64_t offset);
bool     rt_opencl_read_buffer(int64_t queue, int64_t buffer, int64_t host_ptr, int64_t size);
bool     rt_opencl_set_kernel_arg_i64(int64_t kernel, int64_t index, int64_t value);
bool     rt_opencl_set_kernel_arg_buffer(int64_t kernel, int64_t index, int64_t buffer);
bool     rt_opencl_enqueue_ndrange(int64_t queue, int64_t kernel, int64_t gx, int64_t gy, int64_t gz, int64_t lx, int64_t ly, int64_t lz);
bool     rt_opencl_finish(int64_t queue);
bool     rt_opencl_release_kernel(int64_t kernel);
bool     rt_opencl_release_program(int64_t program);
bool     rt_opencl_release_queue(int64_t queue);
bool     rt_opencl_release_context(int64_t context);

/* ===== SIMD UTF-8 Operations ===== */

int64_t  rt_text_count_codepoints_cached(int64_t value);
int64_t  rt_text_count_codepoints(int64_t value);
int64_t  rt_text_validate_utf8(int64_t value);
int64_t  rt_text_find_invalid_utf8(int64_t value);

/* ===== SIMD String Search & Equality ===== */

int64_t  rt_simd_str_search(int64_t haystack, int64_t needle);
int64_t  rt_simd_str_last_index_of(int64_t haystack, int64_t needle);
int64_t  rt_simd_str_equal(int64_t a, int64_t b);

/* ===== SIMD ASCII Case Operations ===== */

int64_t  rt_text_is_ascii(int64_t value);
int64_t  rt_text_to_upper_ascii(int64_t value);
int64_t  rt_text_to_lower_ascii(int64_t value);

/* ===== String Index (char↔byte offset conversion) ===== */

int64_t  rt_swi_build(int64_t value);
int64_t  rt_swi_char_to_byte(int64_t handle, int64_t char_idx);
int64_t  rt_swi_byte_to_char(int64_t handle, int64_t byte_idx);
void     rt_swi_free(int64_t handle);

int64_t  rt_rank_select_build(int64_t value);
int64_t  rt_rank_query(int64_t handle, int64_t pos);
int64_t  rt_select_query(int64_t handle, int64_t k);
void     rt_rank_select_free(int64_t handle);

/* ===== Reserved-Field Cache Helpers ===== */

/* Forward decl: RtCoreString is defined in runtime_native.c */
struct RtCoreString;
void     rt_str_cache_cp_count(struct RtCoreString* s, uint64_t count);
int64_t  rt_str_cached_cp_count(struct RtCoreString* s);
void     rt_str_set_ascii_flag(struct RtCoreString* s, int is_ascii);
int      rt_str_is_ascii_cached(struct RtCoreString* s);

#ifdef __cplusplus
}
#endif

#endif /* SPL_RUNTIME_H */
