/* Simple FFI Wrapper - C Header
 *
 * Auto-generated header for Simple FFI functions.
 * Include this in C/C++ code to call Simple runtime functions.
 *
 * Usage:
 *   #include "simple_ffi.h"
 *
 *   int main() {
 *       rt_gc_init();
 *       int64_t pid = rt_getpid();
 *       printf("PID: %ld\n", pid);
 *       return 0;
 *   }
 */

#ifndef SIMPLE_FFI_H
#define SIMPLE_FFI_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* ==========================================================================
 * GC (Garbage Collection)
 * ========================================================================== */

void rt_gc_init(void);
void rt_gc_collect(void);
void* rt_gc_malloc(size_t size);
void* rt_gc_realloc(void* ptr, size_t size);
void rt_gc_free(void* ptr);

/* ==========================================================================
 * Process Execution
 * ========================================================================== */

char* rt_process_run(const char* cmd, size_t cmd_len, const char* args);
char* rt_process_run_timeout(const char* cmd, size_t cmd_len, const char* args, int64_t timeout_ms);
char* rt_process_output(const char* cmd, size_t cmd_len, const char* args);
char* rt_shell(const char* cmd, size_t cmd_len);
int64_t rt_shell_exec(const char* cmd, size_t cmd_len);
void rt_eprintln(const char* msg, size_t msg_len);

/* ==========================================================================
 * Time Operations
 * ========================================================================== */

int64_t rt_time_now_unix_micros(void);
int64_t _current_time_unix(void);
int64_t rt_current_time_ms(void);
int32_t rt_timestamp_get_year(int64_t micros);
int32_t rt_timestamp_get_month(int64_t micros);
int32_t rt_timestamp_get_day(int64_t micros);
int32_t rt_timestamp_get_hour(int64_t micros);
int32_t rt_timestamp_get_minute(int64_t micros);
int32_t rt_timestamp_get_second(int64_t micros);

/* ==========================================================================
 * System Operations
 * ========================================================================== */

int64_t rt_getpid(void);
char* rt_hostname(void);
int64_t rt_system_cpu_count(void);
char* rt_path_basename(const char* path, size_t path_len);
char* sys_get_args(void);
char* rt_cli_get_args(void);
void sys_exit(int64_t code);
void rt_cli_exit(int64_t code);
bool rt_cli_file_exists(const char* path, size_t path_len);
char* rt_cli_read_file(const char* path, size_t path_len);

/* ==========================================================================
 * File I/O
 * ========================================================================== */

bool rt_file_exists(const char* path, size_t path_len);
char* rt_file_read_text(const char* path, size_t path_len);
bool rt_file_write_text(const char* path, size_t path_len, const char* content, size_t content_len);
bool rt_file_delete(const char* path, size_t path_len);
void rt_string_free(char* ptr);

/* ==========================================================================
 * Directory Operations
 * ========================================================================== */

bool rt_dir_create(const char* path, size_t path_len);
bool rt_dir_create_all(const char* path, size_t path_len);
char* rt_dir_list(const char* path, size_t path_len);
char* rt_dir_walk(const char* path, size_t path_len);
bool rt_dir_remove(const char* path, size_t path_len);
bool rt_package_remove_dir_all(const char* path, size_t path_len);
bool rt_package_is_dir(const char* path, size_t path_len);
int64_t rt_package_file_size(const char* path, size_t path_len);

/* ==========================================================================
 * Environment
 * ========================================================================== */

char* rt_env_get(const char* name, size_t name_len);
bool rt_env_set(const char* name, size_t name_len, const char* value, size_t value_len);
char* rt_env_cwd(void);
char* rt_env_home(void);

/* ==========================================================================
 * Glob
 * ========================================================================== */

char* rt_glob(const char* pattern, size_t pattern_len);

/* ==========================================================================
 * Cargo Operations
 * ========================================================================== */

char* rt_cargo_build(const char* profile, size_t profile_len, const char* features, int64_t feature_count);
char* rt_cargo_check(void);
int64_t rt_cargo_clean(void);
char* rt_cargo_test(const char* package, size_t package_len, const char* filter, size_t filter_len);
char* rt_cargo_test_doc(const char* package, size_t package_len);
char* rt_cargo_lint(int64_t fix);
char* rt_cargo_fmt(int64_t check_only);

/* ==========================================================================
 * Coverage
 * ========================================================================== */

bool rt_coverage_enabled(void);
void rt_coverage_clear(void);
bool rt_coverage_dump_sdn(const char* path, size_t path_len);

/* ==========================================================================
 * Fault Detection
 * ========================================================================== */

void rt_fault_set_stack_overflow_detection(bool enabled);
void rt_fault_set_max_recursion_depth(int64_t depth);
void rt_fault_set_timeout(int64_t timeout_ms);
void rt_fault_set_execution_limit(int64_t max_instructions);

/* ==========================================================================
 * Runtime Value (opaque type)
 * ========================================================================== */

typedef struct RuntimeValue RuntimeValue;

RuntimeValue* rt_value_none(void);
RuntimeValue* rt_value_bool(bool val);
RuntimeValue* rt_value_int(int64_t val);
RuntimeValue* rt_value_float(double val);
RuntimeValue* rt_value_string(const char* ptr, size_t len);
void rt_value_free(RuntimeValue* val);

#ifdef __cplusplus
}
#endif

#endif /* SIMPLE_FFI_H */
