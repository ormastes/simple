/*
 * Auto-generated stubs for Simple functions that are called but not defined
 * in the C backend compiler binary. These functions exist in other Simple
 * modules but are not part of the compile_c_entry.spl dependency tree.
 *
 * All stubs return 0 (nil). When the native compiler actually needs a
 * function, it will abort with a clear error message.
 */

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

/* Forward declarations for runtime helpers */
extern int64_t rt_string_new(int64_t ptr, int64_t len);
extern int64_t rt_array_new(int64_t hint_cap);
extern int64_t rt_array_push(int64_t arr, int64_t val);
extern int64_t rt_tuple_len(int64_t v);
extern int64_t rt_contains(int64_t c, int64_t i);
extern int64_t rt_string_eq(int64_t a, int64_t b);
extern int64_t rt_dict_get(int64_t d, int64_t k);

static int64_t str_from(const char *s) {
    return rt_string_new((int64_t)(intptr_t)s, (int64_t)strlen(s));
}

/* ================================================================
 * Missing rt_* functions (not in bootstrap_runtime.c)
 * ================================================================ */

/* OS-level stubs using int64_t tagged value system (NOT const char*) */
int64_t rt_cli_get_args(void) { return rt_array_new(0); }
int64_t rt_dir_remove_all(int64_t path) { (void)path; return 0; }
int64_t rt_dir_walk(int64_t path) { (void)path; return rt_array_new(0); }
int64_t rt_file_copy(int64_t src, int64_t dst) { (void)src; (void)dst; return 0; }
int64_t rt_file_delete(int64_t path) { (void)path; return 0; }
int64_t rt_file_lock(int64_t path, int64_t timeout) { (void)path; (void)timeout; return 0; }
int64_t rt_file_read_text_at(int64_t path, int64_t off, int64_t sz) { (void)path; (void)off; (void)sz; return 0; }
int64_t rt_file_size(int64_t path) { (void)path; return 0; }
int64_t rt_file_stat(int64_t path) { (void)path; return 0; }
int64_t rt_file_unlock(int64_t handle) { (void)handle; return 0; }
int64_t rt_file_write_text_at(int64_t path, int64_t off, int64_t data) { (void)path; (void)off; (void)data; return 0; }
int64_t rt_getpid(void) { return (int64_t)getpid(); }
int64_t rt_hostname(void) { return str_from("localhost"); }
int64_t rt_madvise(int64_t a, int64_t s, int64_t ad) { (void)a; (void)s; (void)ad; return 0; }
int64_t rt_mmap(int64_t p, int64_t s, int64_t o, int64_t r) { (void)p; (void)s; (void)o; (void)r; return 0; }
int64_t rt_msync(int64_t a, int64_t s) { (void)a; (void)s; return 0; }
int64_t rt_munmap(int64_t a, int64_t s) { (void)a; (void)s; return 0; }
int64_t rt_process_is_running(int64_t pid) { (void)pid; return 0; }
int64_t rt_process_kill(int64_t pid) { (void)pid; return 0; }
int64_t rt_process_spawn_async(int64_t cmd, int64_t args) { (void)cmd; (void)args; return 0; }
int64_t rt_shell_output(int64_t cmd) { (void)cmd; return str_from(""); }
int64_t rt_time_now_micros(void) { return 0; }
int64_t rt_time_now_nanos(void) { return 0; }
int64_t rt_time_now_unix_micros(void) { return 0; }
/* (old DUPE comments removed — now defined above) */

/* spl_int: value constructor used by compiled code */
int64_t spl_int(int64_t v) { return v; }

/* ================================================================
 * Key Simple functions that need real implementations
 * ================================================================ */

/* `len` is ubiquitous - delegates to __spl_method_len which handles arrays/tuples/strings/dicts */
extern int64_t __spl_method_len(int64_t);
int64_t len(int64_t v) { return __spl_method_len(v); }

/* String helpers */
int64_t str(int64_t v) {
    if (v == 0) return str_from("nil");
    /* If already a string, return as-is */
    /* Otherwise convert int to string */
    char buf[64];
    snprintf(buf, sizeof(buf), "%ld", (long)v);
    return str_from(buf);
}

int64_t s_len(int64_t v) { return rt_tuple_len(v); }
int64_t s_bytes(int64_t v) { (void)v; return rt_array_new(0); }
int64_t text_len(int64_t v) { return rt_tuple_len(v); }
int64_t text_index_of(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return -1; }

int64_t key_len(int64_t v) { return rt_tuple_len(v); }
int64_t line_len(int64_t v) { return rt_tuple_len(v); }
int64_t line_trim(int64_t v) { return v; }
int64_t line_trim_start(int64_t v) { return v; }
int64_t trimmed_len(int64_t v) { return rt_tuple_len(v); }
int64_t keyword_len(int64_t v) { return rt_tuple_len(v); }
int64_t str_bytes_len(int64_t v) { return rt_tuple_len(v); }
int64_t body_line_len(int64_t v) { return rt_tuple_len(v); }
int64_t code_len(int64_t v) { return rt_tuple_len(v); }
int64_t id_str_len(int64_t v) { return rt_tuple_len(v); }
int64_t name_type_len(int64_t v) { return rt_tuple_len(v); }
int64_t param_str_len(int64_t v) { return rt_tuple_len(v); }
int64_t part_trim(int64_t v) { return v; }

/* Collection length helpers */
int64_t a_len(int64_t v) { return rt_tuple_len(v); }
int64_t a_keys(int64_t v) { (void)v; return rt_array_new(0); }
int64_t b_len(int64_t v) { return rt_tuple_len(v); }
int64_t b_keys(int64_t v) { (void)v; return rt_array_new(0); }
int64_t b_contains_key(int64_t d, int64_t k) { return rt_contains(d, k); }
int64_t keys_a_len(int64_t v) { return rt_tuple_len(v); }
int64_t keys_b_len(int64_t v) { return rt_tuple_len(v); }
int64_t args_len(int64_t v) { return rt_tuple_len(v); }
int64_t params_enumerate(int64_t v) { (void)v; return rt_array_new(0); }
int64_t elements_len(int64_t v) { return rt_tuple_len(v); }
int64_t fields_len(int64_t v) { return rt_tuple_len(v); }
int64_t targets_len(int64_t v) { return rt_tuple_len(v); }
int64_t indices_len(int64_t v) { return rt_tuple_len(v); }
int64_t operands_len(int64_t v) { return rt_tuple_len(v); }
int64_t parts_len(int64_t v) { return rt_tuple_len(v); }
int64_t exp_parts_len(int64_t v) { return rt_tuple_len(v); }
int64_t tokens_push(int64_t arr, int64_t tok) { return rt_array_push(arr, tok); }
int64_t sorted_len(int64_t v) { return rt_tuple_len(v); }
int64_t local_syms_len(int64_t v) { return rt_tuple_len(v); }
int64_t new_blocks_len(int64_t v) { return rt_tuple_len(v); }
int64_t expected_errors_len(int64_t v) { return rt_tuple_len(v); }
int64_t active_len(int64_t v) { return rt_tuple_len(v); }
int64_t data_data_len(int64_t v) { return rt_tuple_len(v); }
int64_t text_data_len(int64_t v) { return rt_tuple_len(v); }
int64_t rodata_data_len(int64_t v) { return rt_tuple_len(v); }
int64_t section_syms_len(int64_t v) { return rt_tuple_len(v); }
int64_t block_start_len(int64_t v) { return rt_tuple_len(v); }
int64_t block_end_len(int64_t v) { return rt_tuple_len(v); }

/* Bit operations */
int64_t bit_shl(int64_t a, int64_t b) { return a << b; }
int64_t bit_shr(int64_t a, int64_t b) { return a >> b; }
int64_t ch_ord(int64_t c) { return c; }

/* Result helpers */
int64_t result_is_err(int64_t v) { return v == 0 ? 1 : 0; }
int64_t result_push(int64_t arr, int64_t val) { return rt_array_push(arr, val); }
int64_t result_replace(int64_t a, int64_t b, int64_t c) { (void)a;(void)b; return c; }
int64_t result_unwrap_err(int64_t v) { return v; }
int64_t backends_push(int64_t arr, int64_t val) { return rt_array_push(arr, val); }
int64_t shaders_push(int64_t arr, int64_t val) { return rt_array_push(arr, val); }

/* Contains/check */
int64_t offsets_contains(int64_t c, int64_t v) { return rt_contains(c, v); }
int64_t intervals_contains(int64_t c, int64_t v) { return rt_contains(c, v); }
int64_t intervals_keys(int64_t c) { (void)c; return rt_array_new(0); }
int64_t block_start_pos_contains(int64_t c, int64_t v) { return rt_contains(c, v); }
int64_t existing_contains(int64_t c, int64_t v) { return rt_contains(c, v); }
int64_t actual_msg_contains(int64_t s, int64_t sub) { return rt_contains(s, sub); }
int64_t messages_map(int64_t c, int64_t fn) { (void)fn; return c; }

/* Eval stub */
int64_t eval(int64_t code) { (void)code; return 0; }

/* Compile helpers */
int64_t compileoptions_default_options(void) { return 0; }

/* Parse helpers */
int64_t parse_int_literal(int64_t s) { (void)s; return 0; }
int64_t parse_json(int64_t s) { (void)s; return 0; }
int64_t parse_shell_commands(int64_t s) { (void)s; return rt_array_new(0); }
int64_t parse_sql_query(int64_t s) { (void)s; return 0; }
int64_t json_to_const(int64_t j) { (void)j; return 0; }
int64_t sql_keywords(void) { return rt_array_new(0); }

/* Pipeline and optimization */
int64_t check_exhaustiveness(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 1; }

/* Architecture */
int64_t all_target_archs(void) { return rt_array_new(0); }
int64_t get_host_os(void) { return str_from("linux"); }
int64_t backend_supports_target(int64_t backend, int64_t target) { (void)backend; (void)target; return 1; }
int64_t match_target_spec(int64_t a,int64_t b,int64_t c,int64_t d,int64_t e,int64_t f,int64_t g,int64_t h,int64_t i,int64_t j,int64_t k,int64_t l,int64_t m,int64_t n) { (void)a;(void)b;(void)c;(void)d;(void)e;(void)f;(void)g;(void)h;(void)i;(void)j;(void)k;(void)l;(void)m;(void)n; return 0; }
int64_t preferred_value_supports_target(int64_t pref, int64_t target) { (void)pref; (void)target; return 1; }
int64_t mode_default_optimization(int64_t mode) { (void)mode; return 0; }
int64_t target_is_cuda(int64_t t) { (void)t; return 0; }
int64_t target_is_vulkan(int64_t t) { (void)t; return 0; }
int64_t target_vulkan_version(int64_t t) { (void)t; return 0; }

/* LLVM tool detection stubs */
int64_t llvm_find_llc(void) { return str_from("llc"); }
int64_t llvm_find_opt(void) { return str_from("opt"); }
int64_t llvm_find_wasi_sysroot(void) { return str_from(""); }
int64_t llvm_find_wasm_ld(void) { return str_from("wasm-ld"); }
int64_t llvm_find_wasm_opt(void) { return str_from("wasm-opt"); }
int64_t llvm_llc_available(void) { return 0; }
int64_t llvm_opt_available(void) { return 0; }

/* Arch-specific register helpers */
int64_t aarch64_arg_regs_len(void) { return 8; }
int64_t rv_arg_regs_len(void) { return 8; }

/* Type helpers */
int64_t type__size_bytes(int64_t t) { (void)t; return 8; }
int64_t type__to_text(int64_t t) { return str_from("i64"); }
int64_t value_type_name(int64_t v) { (void)v; return str_from("i64"); }

/* Block definitions */
int64_t block_def_kind(int64_t b) { (void)b; return 0; }
int64_t block_def_eval_const(int64_t b, int64_t c) { (void)b; (void)c; return 0; }
int64_t block_def_parse_payload(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; }
int64_t block_def_validate(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 1; }
int64_t blockerror_parse(int64_t msg) { return msg; }
int64_t blockerror_parse_at(int64_t msg, int64_t pos) { (void)pos; return msg; }
int64_t blockcontext_test(int64_t ctx) { (void)ctx; return 0; }
int64_t register_builtin_blocks(int64_t reg) { return reg; }

/* SPIRV builder stubs */
int64_t builder_alloc_id(int64_t b) { (void)b; return 0; }
int64_t builder_build(int64_t b) { return b; }
int64_t builder_emit_capabilities(int64_t b) { return b; }
int64_t builder_emit_composite_extract(int64_t a, int64_t b, int64_t c, int64_t d) { (void)a;(void)b;(void)c;(void)d; return 0; }
int64_t builder_emit_const_false(int64_t a, int64_t b) { (void)a;(void)b; return 0; }
int64_t builder_emit_const_float(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; }
int64_t builder_emit_const_int(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; }
int64_t builder_emit_const_true(int64_t a, int64_t b) { (void)a;(void)b; return 0; }
int64_t builder_emit_decorate_builtin(int64_t b, int64_t id, int64_t dec) { (void)b; (void)id; (void)dec; return 0; }
int64_t builder_emit_entry_point(int64_t a, int64_t b, int64_t c, int64_t d) { (void)a;(void)b;(void)c;(void)d; return 0; }
int64_t builder_emit_execution_mode(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; }
int64_t builder_emit_extensions(int64_t b) { return b; }
int64_t builder_emit_function_end(int64_t b) { return b; }
int64_t builder_emit_header(int64_t b) { return b; }
int64_t builder_emit_label(int64_t a) { (void)a; return 0; }
int64_t builder_emit_load(int64_t b, int64_t ptr, int64_t ty) { (void)b; (void)ptr; (void)ty; return 0; }
int64_t builder_emit_memory_model(int64_t b) { return b; }
int64_t builder_emit_return(int64_t b) { return b; }
int64_t builder_emit_type_bool(int64_t b) { (void)b; return 0; }
int64_t builder_emit_type_float(int64_t b, int64_t bits) { (void)b; (void)bits; return 0; }
int64_t builder_emit_type_function(int64_t b, int64_t ret, int64_t params) { (void)b; (void)ret; (void)params; return 0; }
int64_t builder_emit_type_int(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; }
int64_t builder_emit_type_vector(int64_t b, int64_t elem, int64_t n) { (void)b; (void)elem; (void)n; return 0; }
int64_t builder_emit_type_void(int64_t b) { (void)b; return 0; }

/* MachReg / Operand kind enum constructors */
int64_t machregkind_Physical(int64_t v) { return v; }
int64_t machregkind_Virtual(int64_t v) { return v; }
int64_t operandkind_Imm(int64_t v) { return v; }
int64_t operandkind_Label(int64_t v) { return v; }
int64_t operandkind_Mem(int64_t v, int64_t v2) { (void)v2; return v; }
int64_t operandkind_Reg(int64_t v) { return v; }
int64_t operandkind_Sym(int64_t v) { return v; }
int64_t device_CUDA(int64_t v) { return v; }

/* Misc stubs */
int64_t _BreakpointEntry(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e, int64_t f, int64_t g, int64_t h, int64_t i) {
    (void)a;(void)b;(void)c;(void)d;(void)e;(void)f;(void)g;(void)h;(void)i; return 0;
}
int64_t _CliProcessResult(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; }
int64_t lexer_create_internal(int64_t a, int64_t b) { (void)a;(void)b; return 0; }
int64_t parser_get_instructions(int64_t p) { (void)p; return rt_array_new(0); }
/* parser_parse: legacy parser, not used by bridge (bridge uses Parser__parse) */
int64_t parser_parse(int64_t src) { (void)src; return 0; }
/* p_advance: called by create_parser(), no-op stub */
int64_t p_advance(int64_t p) { return p; }
int64_t reg_register(int64_t reg, int64_t item) { (void)item; return reg; }
int64_t reg_unregister(int64_t reg, int64_t item) { (void)item; return reg; }
int64_t completer(int64_t a, int64_t b) { (void)a;(void)b; return a; }
int64_t highlighter(int64_t v) { return v; }
int64_t hover_fn(int64_t a, int64_t b) { (void)a;(void)b; return a; }
int64_t validator(int64_t a, int64_t b) { (void)a;(void)b; return a; }
int64_t vars_items(int64_t v) { (void)v; return rt_array_new(0); }
int64_t cudatypemapper_create_sm(int64_t sm, int64_t b) { (void)sm; (void)b; return 0; }
int64_t vulkantypemapper_create_version(int64_t a, int64_t b, int64_t c, int64_t d) { (void)a;(void)b;(void)c;(void)d; return 0; }

/* Additional missing functions discovered during link */
int64_t attr_effective_align(int64_t attr, int64_t b) { (void)attr; (void)b; return 8; }
int64_t errors_len(int64_t errors) { return rt_tuple_len(errors); }

/* Architecture info stubs (default to x86_64) */
int64_t arch_pointer_bytes(int64_t arch) { (void)arch; return 8; }
int64_t arch_bits(int64_t arch) { (void)arch; return 64; }

/* MIR optimization pass stubs */
int64_t dce_run_on_function(int64_t pass, int64_t func) { (void)pass; (void)func; return func; }
int64_t cf_run_on_function(int64_t pass, int64_t func) { (void)pass; (void)func; return func; }
int64_t pipeline_optimize(int64_t pipe, int64_t mod_) { (void)pipe; (void)mod_; return mod_; }
int64_t compileerror_backend_error(int64_t a, int64_t b) { (void)a; (void)b; return 0; }
int64_t compileerror_target_unsupported(int64_t a, int64_t b) { (void)a; (void)b; return 0; }

/* rt_indirect_call arity variants */
int64_t rt_indirect_call_1(int64_t fn_) { (void)fn_; return 0; }
int64_t rt_indirect_call_2(int64_t fn_, int64_t arg) { (void)fn_; (void)arg; return 0; }
int64_t rt_indirect_call_3(int64_t fn_, int64_t a, int64_t b) { (void)fn_; (void)a; (void)b; return 0; }

/* rt_process arity variants */
int64_t rt_process_wait_1(int64_t pid) { (void)pid; return 0; }
int64_t rt_process_wait_2(int64_t pid, int64_t timeout) { (void)pid; (void)timeout; return 0; }
/* DUPE: int64_t rt_process_output(int64_t a, int64_t b) { (void)a;(void)b; return str_from(""); } */

/* rt_time stubs */
/* DUPE: int64_t rt_time_year(void) { return 2026; } */
/* DUPE: int64_t rt_time_month(void) { return 2; } */
/* DUPE: int64_t rt_time_day(void) { return 26; } */
/* DUPE: int64_t rt_time_hour(void) { return 0; } */
/* DUPE: int64_t rt_time_minute(void) { return 0; } */
/* DUPE: int64_t rt_time_second(void) { return 0; } */
/* DUPE: int64_t rt_random_uniform(int64_t a, int64_t b) { return a; } */

/* Missing rt_* stubs */
/* DUPE: int64_t rt_args_get(void) { return 0; } */
/* DUPE: int64_t rt_dir_remove(int64_t a, int64_t b) { (void)a;(void)b; return 0; } */
/* DUPE: int64_t rt_execute_native(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; } */
/* DUPE: int64_t rt_list_dir_recursive(int64_t a, int64_t b) { (void)a;(void)b; return rt_array_new(0); } */
/* DUPE: int64_t rt_log_emit(int64_t a, int64_t b, int64_t c, int64_t d, int64_t e) { (void)a;(void)b;(void)c;(void)d;(void)e; return 0; } */
/* DUPE: int64_t rt_log_get_scope_level(int64_t a, int64_t b) { (void)a;(void)b; return 0; } */
/* DUPE: int64_t rt_log_is_enabled(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; } */
/* DUPE: int64_t rt_log_set_scope_level(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; } */

/* text_* function stubs */
extern int64_t __spl_method_split(int64_t, int64_t);
extern int64_t __spl_method_replace(int64_t, int64_t, int64_t);
int64_t text__split(int64_t s) { return __spl_method_split(s, str_from(" ")); }
int64_t text__replace(int64_t a, int64_t b) { (void)a;(void)b; return a; }
int64_t text__len(void) { return 0; }

/* __spl_method_* stubs for remaining unresolved methods */
extern int64_t __spl_to_string(int64_t);
/* DUPE: __spl_method_substring defined in bootstrap_runtime.c */
/* DUPE: int64_t __spl_method_blocks_contains_key(int64_t self_, int64_t k, int64_t v) { (void)self_; (void)k; (void)v; return 0; } */
/* DUPE: int64_t __spl_method_blocks_remove(int64_t self_, int64_t k, int64_t v) { (void)self_; (void)k; (void)v; return 0; } */
/* DUPE: int64_t __spl_method_emit_module_header(int64_t self_, int64_t name) { (void)self_; (void)name; return 0; } */
/* DUPE: int64_t __spl_method_end_namespace(int64_t self_, int64_t name) { (void)self_; (void)name; return 0; } */
/* DUPE: int64_t __spl_method__examples_push(int64_t self_, int64_t a, int64_t b) { (void)self_; (void)a; (void)b; return 0; } */
/* DUPE: int64_t __spl_method_message_contains(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; } */
/* DUPE: int64_t __spl_method_operands_len(int64_t self_, int64_t a) { (void)self_; (void)a; return 0; } */
/* DUPE: int64_t __spl_method_registry_register(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; } */
/* DUPE: int64_t __spl_method_registry_unregister(int64_t a, int64_t b, int64_t c) { (void)a;(void)b;(void)c; return 0; } */
/* DUPE: int64_t __spl_method_stats_record_pass_run(int64_t self_, int64_t a, int64_t b) { (void)self_; (void)a; (void)b; return 0; } */
/* DUPE: int64_t __spl_method_test(int64_t a, int64_t b) { (void)a;(void)b; return 0; } */
/* DUPE: int64_t __spl_method_to_lean_spec(int64_t a, int64_t b, int64_t c, int64_t d) { (void)a;(void)b;(void)c;(void)d; return str_from(""); } */
/* __spl_method_validation defined in bootstrap_runtime.c */

/* (SPIR-V builder stubs already defined above) */

/* ================================================================
 * Parser__parse BRIDGE
 *
 * Converts core parser array-based AST to typed Module struct
 * expected by the Simple HIR lowering pipeline.
 *
 * Core parser (core/parser.spl) is fully compiled and working.
 * This bridge calls parse_module(), reads declarations from
 * global arena arrays via accessor functions, and constructs
 * typed objects (Module, Function, Block, Stmt, Expr).
 * ================================================================ */

/* Runtime functions */
extern int64_t rt_object_new(int64_t type_id, int64_t field_count);
extern int64_t rt_object_field_get(int64_t obj, int64_t idx);
extern int64_t rt_object_field_set(int64_t obj, int64_t idx, int64_t val);
extern int64_t rt_array_new(int64_t cap);
extern int64_t rt_array_push(int64_t arr, int64_t val);
extern int64_t rt_array_get(int64_t arr, int64_t idx);
extern int64_t rt_array_len(int64_t arr);
extern int64_t rt_dict_new(int64_t cap);
extern int64_t rt_dict_set(int64_t dict, int64_t key, int64_t val);
extern int64_t rt_dict_keys(int64_t dict);
extern int64_t rt_enum_new(int64_t type_id, int64_t disc, int64_t payload);
extern int64_t rt_tuple_new(int64_t size);
extern int64_t rt_tuple_set(int64_t tup, int64_t idx, int64_t val);

/* Core parser functions (compiled from Simple source) */
extern int64_t parse_module(int64_t source, int64_t path);
extern int64_t module_get_decls(void);

/* Core AST accessor functions */
extern int64_t decl_get_tag(int64_t idx);
extern int64_t decl_get_name(int64_t idx);
extern int64_t decl_get_param_names(int64_t idx);
extern int64_t decl_get_param_types(int64_t idx);
extern int64_t decl_get_ret_type(int64_t idx);
extern int64_t decl_get_body(int64_t idx);
extern int8_t  decl_get_is_pub(int64_t idx);
extern int64_t decl_get_is_async(int64_t idx);
extern int64_t decl_get_type_params(int64_t idx);
extern int64_t decl_get_fields(int64_t idx);
extern int64_t decl_get_field_types(int64_t idx);
extern int64_t decl_get_field_defaults(int64_t idx);
extern int64_t decl_get_imports(int64_t idx);

extern int64_t stmt_get_tag(int64_t idx);
extern int64_t stmt_get_expr(int64_t idx);
extern int64_t stmt_get_name(int64_t idx);
extern int64_t stmt_get_type(int64_t idx);
extern int64_t stmt_get_body(int64_t idx);

extern int64_t expr_get_tag(int64_t idx);
extern int64_t expr_get_int(int64_t idx);
extern int64_t expr_get_float(int64_t idx);
extern int64_t expr_get_str(int64_t idx);
extern int64_t expr_get_left(int64_t idx);
extern int64_t expr_get_right(int64_t idx);
extern int64_t expr_get_extra(int64_t idx);
extern int64_t expr_get_args(int64_t idx);
extern int64_t expr_get_stmts(int64_t idx);

/* elif chain accessors */
extern int64_t elif_get_cond(int64_t idx);
extern int64_t elif_get_body(int64_t idx);
extern int64_t elif_get_else(int64_t idx);

/* match arm accessors */
extern int64_t arm_get_pattern(int64_t idx);
extern int64_t arm_get_guard(int64_t idx);
extern int64_t arm_get_body(int64_t idx);
extern int64_t arm_get_binding(int64_t idx);

/* Core AST tags */
#define CORE_DECL_FN         1
#define CORE_DECL_EXTERN_FN  2
#define CORE_DECL_STRUCT     3
#define CORE_DECL_VAL        4
#define CORE_DECL_VAR        5
#define CORE_DECL_USE        6
#define CORE_DECL_EXPORT     7
#define CORE_DECL_ENUM       8
#define CORE_DECL_IMPL       9
#define CORE_DECL_CLASS     10

#define CORE_STMT_EXPR       1
#define CORE_STMT_VAL        2
#define CORE_STMT_VAR        3
#define CORE_STMT_ASSIGN     4
#define CORE_STMT_RETURN     5
#define CORE_STMT_IF         6
#define CORE_STMT_FOR        7
#define CORE_STMT_WHILE      8
#define CORE_STMT_MATCH      9
#define CORE_STMT_BLOCK     10
#define CORE_STMT_BREAK     11
#define CORE_STMT_CONTINUE  12
#define CORE_STMT_COMPOUND_ASSIGN 13

#define CORE_EXPR_INT_LIT    1
#define CORE_EXPR_FLOAT_LIT  2
#define CORE_EXPR_STRING_LIT 3
#define CORE_EXPR_BOOL_LIT   4
#define CORE_EXPR_NIL_LIT    5
#define CORE_EXPR_IDENT      6
#define CORE_EXPR_BINARY     7
#define CORE_EXPR_UNARY      8
#define CORE_EXPR_CALL       9
#define CORE_EXPR_INDEX     10
#define CORE_EXPR_FIELD     11
#define CORE_EXPR_METHOD    12
#define CORE_EXPR_ARRAY     13
#define CORE_EXPR_IF        14
#define CORE_EXPR_MATCH     15
#define CORE_EXPR_FOR       16
#define CORE_EXPR_WHILE     17
#define CORE_EXPR_BLOCK     18
#define CORE_EXPR_RETURN    19
#define CORE_EXPR_BREAK     20
#define CORE_EXPR_CONTINUE  21
#define CORE_EXPR_RANGE     22
#define CORE_EXPR_ASSIGN    23
#define CORE_EXPR_COMPOUND  24
#define CORE_EXPR_DICT      25
#define CORE_EXPR_LAMBDA    26
#define CORE_EXPR_STRUCT    27
#define CORE_EXPR_TUPLE     28
#define CORE_EXPR_SLICE     29
#define CORE_EXPR_NULL_COAL 30
#define CORE_EXPR_OPT_CHAIN 31
#define CORE_EXPR_CAST      32
#define CORE_EXPR_UNIT      33
#define CORE_EXPR_INTERP    34
#define CORE_EXPR_PASS      35
#define CORE_EXPR_DO_BLOCK  44

/* Typed ExprKind discriminants */
#define TK_INTLIT     0
#define TK_FLOATLIT   1
#define TK_STRLIT     2
#define TK_BOOLLIT    3
#define TK_NILLIT     4
#define TK_ARRAYLIT   5
#define TK_TUPLELIT   6
#define TK_DICTLIT    7
#define TK_SETLIT     8
#define TK_IDENT      9
#define TK_FIELD     10
#define TK_INDEX     11
#define TK_OPTCHAIN  12
#define TK_NULLCOAL  13
#define TK_EXISTS    14
#define TK_BINARY    15
#define TK_UNARY     16
#define TK_RANGE     17
#define TK_CALL      18
#define TK_METHCALL  19
#define TK_IF        20
#define TK_MATCH     21
#define TK_TRY       22
#define TK_TRYCATCH  23
#define TK_LAMBDA    24
#define TK_BLOCK     25
#define TK_LISTCOMP  26
#define TK_DICTCOMP  27
#define TK_AWAIT     28
#define TK_SPAWN     29
#define TK_YIELD     30
#define TK_RETURN    31
#define TK_BREAK     32
#define TK_CONTINUE  33
#define TK_THROW     34
#define TK_STRUCTLIT 35
#define TK_ENUMLIT   36
#define TK_ERROR     46

/* Typed StmtKind discriminants */
#define TS_EXPR       0
#define TS_VAL        1
#define TS_VAR        2
#define TS_SVAL       3
#define TS_SVAR       4
#define TS_ASSIGN     5
#define TS_FOR        6
#define TS_WHILE      7
#define TS_LOOP       8
#define TS_BREAK      9
#define TS_CONTINUE  10
#define TS_RETURN    11
#define TS_YIELD     12
#define TS_THROW     13

/* Core type tags */
#define CORETYPE_VOID  0
#define CORETYPE_BOOL  1
#define CORETYPE_I64   2
#define CORETYPE_F64   3
#define CORETYPE_TEXT  4

/* Field index to byte offset: compiled C uses byte offsets for rt_object_field_* */
#define FI(n) ((int64_t)((n) * 8))

/* Forward declarations for recursive conversion */
static int64_t bridge_convert_expr(int64_t core_idx);
static int64_t bridge_convert_stmt(int64_t core_idx);
static int64_t bridge_convert_block(int64_t core_stmt_array);

/* ---- Helper: default Span (4 fields) ---- */
static int64_t bridge_make_span(void) {
    int64_t s = rt_object_new(0, 4);
    rt_object_field_set(s, FI(0), 0);  /* start */
    rt_object_field_set(s, FI(1), 0);  /* end */
    rt_object_field_set(s, FI(2), 1);  /* line */
    rt_object_field_set(s, FI(3), 1);  /* col */
    return s;
}

/* ---- Helper: make TypeKind::Named(name, []) ---- */
static int64_t bridge_make_type(const char *name) {
    int64_t nm = str_from(name);
    int64_t args = rt_array_new(0);
    int64_t payload = rt_tuple_new(2);
    rt_tuple_set(payload, 0, nm);
    rt_tuple_set(payload, 1, args);
    int64_t kind = rt_enum_new(0, 0, payload); /* TypeKind::Named = disc 0 */
    int64_t type_obj = rt_object_new(0, 2);
    rt_object_field_set(type_obj, FI(0), kind);
    rt_object_field_set(type_obj, FI(1), bridge_make_span());
    return type_obj;
}

/* ---- Helper: convert core type tag to typed Type ---- */
static int64_t bridge_convert_type(int64_t core_type) {
    switch (core_type) {
        case CORETYPE_VOID: return bridge_make_type("void");
        case CORETYPE_BOOL: return bridge_make_type("bool");
        case CORETYPE_I64:  return bridge_make_type("i64");
        case CORETYPE_F64:  return bridge_make_type("f64");
        case CORETYPE_TEXT: return bridge_make_type("text");
        default:            return bridge_make_type("Any");
    }
}

/* ---- Helper: make a CallArg ---- */
static int64_t bridge_make_call_arg(int64_t expr) {
    int64_t ca = rt_object_new(0, 4);
    rt_object_field_set(ca, FI(0), 0);             /* has_name = false */
    rt_object_field_set(ca, FI(1), str_from(""));  /* name = "" */
    rt_object_field_set(ca, FI(2), expr);          /* value */
    rt_object_field_set(ca, FI(3), bridge_make_span());
    return ca;
}

/* ---- Convert core expression → typed Expr ---- */
static int64_t bridge_convert_expr(int64_t ci) {
    if (ci < 0) return 0; /* nil */
    int64_t tag = expr_get_tag(ci);
    int64_t kind;

    switch (tag) {
    case CORE_EXPR_INT_LIT: {
        kind = rt_enum_new(0, TK_INTLIT, expr_get_int(ci));
        break;
    }
    case CORE_EXPR_FLOAT_LIT: {
        /* Store float text as string, wrapped in tuple */
        kind = rt_enum_new(0, TK_FLOATLIT, 0);
        break;
    }
    case CORE_EXPR_STRING_LIT: {
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, expr_get_str(ci));
        rt_tuple_set(payload, 1, 0); /* no interpolations */
        kind = rt_enum_new(0, TK_STRLIT, payload);
        break;
    }
    case CORE_EXPR_BOOL_LIT: {
        kind = rt_enum_new(0, TK_BOOLLIT, expr_get_int(ci));
        break;
    }
    case CORE_EXPR_NIL_LIT: {
        kind = rt_enum_new(0, TK_NILLIT, 0);
        break;
    }
    case CORE_EXPR_IDENT: {
        kind = rt_enum_new(0, TK_IDENT, expr_get_str(ci));
        break;
    }
    case CORE_EXPR_BINARY: {
        int64_t left  = bridge_convert_expr(expr_get_left(ci));
        int64_t right = bridge_convert_expr(expr_get_right(ci));
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, expr_get_int(ci)); /* BinOp raw */
        rt_tuple_set(payload, 1, left);
        rt_tuple_set(payload, 2, right);
        kind = rt_enum_new(0, TK_BINARY, payload);
        break;
    }
    case CORE_EXPR_UNARY: {
        int64_t operand = bridge_convert_expr(expr_get_left(ci));
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, expr_get_int(ci)); /* UnaryOp raw */
        rt_tuple_set(payload, 1, operand);
        kind = rt_enum_new(0, TK_UNARY, payload);
        break;
    }
    case CORE_EXPR_CALL: {
        int64_t callee = bridge_convert_expr(expr_get_left(ci));
        int64_t ca = expr_get_args(ci);
        int64_t n = rt_array_len(ca);
        int64_t typed_args = rt_array_new(n);
        for (int64_t i = 0; i < n; i++) {
            int64_t ae = bridge_convert_expr(rt_array_get(ca, i));
            rt_array_push(typed_args, bridge_make_call_arg(ae));
        }
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, callee);
        rt_tuple_set(payload, 1, typed_args);
        kind = rt_enum_new(0, TK_CALL, payload);
        break;
    }
    case CORE_EXPR_INDEX: {
        int64_t obj = bridge_convert_expr(expr_get_left(ci));
        int64_t idx = bridge_convert_expr(expr_get_right(ci));
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, obj);
        rt_tuple_set(payload, 1, idx);
        kind = rt_enum_new(0, TK_INDEX, payload);
        break;
    }
    case CORE_EXPR_FIELD: {
        int64_t obj = bridge_convert_expr(expr_get_left(ci));
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, obj);
        rt_tuple_set(payload, 1, expr_get_str(ci));
        kind = rt_enum_new(0, TK_FIELD, payload);
        break;
    }
    case CORE_EXPR_METHOD: {
        int64_t obj = bridge_convert_expr(expr_get_left(ci));
        int64_t ca = expr_get_args(ci);
        int64_t n = rt_array_len(ca);
        int64_t typed_args = rt_array_new(n);
        for (int64_t i = 0; i < n; i++) {
            int64_t ae = bridge_convert_expr(rt_array_get(ca, i));
            rt_array_push(typed_args, bridge_make_call_arg(ae));
        }
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, obj);
        rt_tuple_set(payload, 1, expr_get_str(ci));
        rt_tuple_set(payload, 2, typed_args);
        kind = rt_enum_new(0, TK_METHCALL, payload);
        break;
    }
    case CORE_EXPR_ARRAY: {
        int64_t ca = expr_get_args(ci);
        int64_t n = rt_array_len(ca);
        int64_t elems = rt_array_new(n);
        for (int64_t i = 0; i < n; i++)
            rt_array_push(elems, bridge_convert_expr(rt_array_get(ca, i)));
        kind = rt_enum_new(0, TK_ARRAYLIT, elems);
        break;
    }
    case CORE_EXPR_DICT: {
        /* Dict literal: args are alternating key,value pairs */
        int64_t ca = expr_get_args(ci);
        int64_t n = rt_array_len(ca);
        int64_t pairs = rt_array_new(n / 2);
        for (int64_t i = 0; i + 1 < n; i += 2) {
            int64_t k = bridge_convert_expr(rt_array_get(ca, i));
            int64_t v = bridge_convert_expr(rt_array_get(ca, i + 1));
            int64_t pair = rt_tuple_new(2);
            rt_tuple_set(pair, 0, k);
            rt_tuple_set(pair, 1, v);
            rt_array_push(pairs, pair);
        }
        kind = rt_enum_new(0, TK_DICTLIT, pairs);
        break;
    }
    case CORE_EXPR_IF: {
        int64_t cond = bridge_convert_expr(expr_get_left(ci));
        int64_t then_stmts = expr_get_stmts(ci);
        int64_t then_block = bridge_convert_block(then_stmts);
        /* else/elif chain via expr_extra (elif index) */
        int64_t elif_idx = expr_get_extra(ci);
        int64_t else_block = 0;
        if (elif_idx >= 0) {
            int64_t else_stmts = elif_get_else(elif_idx);
            if (rt_array_len(else_stmts) > 0)
                else_block = bridge_convert_block(else_stmts);
            /* TODO: handle elif chains */
        }
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, cond);
        rt_tuple_set(payload, 1, then_block);
        rt_tuple_set(payload, 2, else_block);
        kind = rt_enum_new(0, TK_IF, payload);
        break;
    }
    case CORE_EXPR_MATCH: {
        int64_t scrutinee = bridge_convert_expr(expr_get_left(ci));
        int64_t arm_indices = expr_get_args(ci);
        int64_t n = rt_array_len(arm_indices);
        int64_t typed_arms = rt_array_new(n);
        for (int64_t i = 0; i < n; i++) {
            int64_t ai = rt_array_get(arm_indices, i);
            int64_t pat = bridge_convert_expr(arm_get_pattern(ai));
            int64_t body_stmts = arm_get_body(ai);
            int64_t body = bridge_convert_block(body_stmts);
            /* MatchArm: {pattern, guard, body, binding} → just create object */
            int64_t arm = rt_object_new(0, 4);
            rt_object_field_set(arm, FI(0), pat);
            rt_object_field_set(arm, FI(1), 0); /* guard = nil */
            rt_object_field_set(arm, FI(2), body);
            rt_object_field_set(arm, FI(3), arm_get_binding(ai));
            rt_array_push(typed_arms, arm);
        }
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, scrutinee);
        rt_tuple_set(payload, 1, typed_arms);
        kind = rt_enum_new(0, TK_MATCH, payload);
        break;
    }
    case CORE_EXPR_RANGE: {
        int64_t start = bridge_convert_expr(expr_get_left(ci));
        int64_t end   = bridge_convert_expr(expr_get_right(ci));
        int64_t inclusive = expr_get_int(ci); /* 1 = inclusive */
        int64_t step  = bridge_convert_expr(expr_get_extra(ci));
        int64_t payload = rt_tuple_new(4);
        rt_tuple_set(payload, 0, start);
        rt_tuple_set(payload, 1, end);
        rt_tuple_set(payload, 2, inclusive);
        rt_tuple_set(payload, 3, step);
        kind = rt_enum_new(0, TK_RANGE, payload);
        break;
    }
    case CORE_EXPR_LAMBDA: {
        /* Lambda: left = body expr, args = param names, s_val = ? */
        int64_t body_expr = bridge_convert_expr(expr_get_left(ci));
        int64_t param_names = expr_get_args(ci);
        int64_t n = rt_array_len(param_names);
        int64_t typed_params = rt_array_new(n);
        for (int64_t i = 0; i < n; i++) {
            int64_t pname = rt_array_get(param_names, i);
            /* LambdaParam: {name, type} - 2 fields */
            int64_t lp = rt_object_new(0, 2);
            rt_object_field_set(lp, FI(0), pname);
            rt_object_field_set(lp, FI(1), 0); /* type = nil */
            rt_array_push(typed_params, lp);
        }
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, typed_params);
        rt_tuple_set(payload, 1, body_expr);
        kind = rt_enum_new(0, TK_LAMBDA, payload);
        break;
    }
    case CORE_EXPR_STRUCT: {
        /* Struct literal: s_val = type name, args = alternating field_name, field_expr */
        int64_t type_name = expr_get_str(ci);
        int64_t ca = expr_get_args(ci);
        int64_t n = rt_array_len(ca);
        int64_t fields = rt_array_new(n / 2);
        for (int64_t i = 0; i + 1 < n; i += 2) {
            int64_t fname = rt_array_get(ca, i);
            int64_t fexpr = bridge_convert_expr(rt_array_get(ca, i + 1));
            int64_t pair = rt_tuple_new(2);
            rt_tuple_set(pair, 0, fname);
            rt_tuple_set(pair, 1, fexpr);
            rt_array_push(fields, pair);
        }
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, type_name);
        rt_tuple_set(payload, 1, fields);
        kind = rt_enum_new(0, TK_STRUCTLIT, payload);
        break;
    }
    case CORE_EXPR_TUPLE: {
        int64_t ca = expr_get_args(ci);
        int64_t n = rt_array_len(ca);
        int64_t elems = rt_array_new(n);
        for (int64_t i = 0; i < n; i++)
            rt_array_push(elems, bridge_convert_expr(rt_array_get(ca, i)));
        kind = rt_enum_new(0, TK_TUPLELIT, elems);
        break;
    }
    case CORE_EXPR_SLICE: {
        int64_t obj  = bridge_convert_expr(expr_get_left(ci));
        int64_t lo   = bridge_convert_expr(expr_get_right(ci));
        int64_t hi   = bridge_convert_expr(expr_get_extra(ci));
        /* Represent as MethodCall("slice", [lo, hi]) for now */
        int64_t args = rt_array_new(2);
        rt_array_push(args, bridge_make_call_arg(lo));
        rt_array_push(args, bridge_make_call_arg(hi));
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, obj);
        rt_tuple_set(payload, 1, str_from("slice"));
        rt_tuple_set(payload, 2, args);
        kind = rt_enum_new(0, TK_METHCALL, payload);
        break;
    }
    case CORE_EXPR_NULL_COAL: {
        int64_t left  = bridge_convert_expr(expr_get_left(ci));
        int64_t right = bridge_convert_expr(expr_get_right(ci));
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, left);
        rt_tuple_set(payload, 1, right);
        kind = rt_enum_new(0, TK_NULLCOAL, payload);
        break;
    }
    case CORE_EXPR_OPT_CHAIN: {
        int64_t obj = bridge_convert_expr(expr_get_left(ci));
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, obj);
        rt_tuple_set(payload, 1, expr_get_str(ci));
        kind = rt_enum_new(0, TK_OPTCHAIN, payload);
        break;
    }
    case CORE_EXPR_ASSIGN: {
        int64_t target = bridge_convert_expr(expr_get_left(ci));
        int64_t value  = bridge_convert_expr(expr_get_right(ci));
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, target);
        rt_tuple_set(payload, 1, 0); /* op = nil (simple assign) */
        rt_tuple_set(payload, 2, value);
        /* Wrap assign as StmtKind-like expr */
        kind = rt_enum_new(0, TK_IDENT, str_from("__assign__"));
        break;
    }
    case CORE_EXPR_RETURN: {
        int64_t val = bridge_convert_expr(expr_get_left(ci));
        kind = rt_enum_new(0, TK_RETURN, val);
        break;
    }
    case CORE_EXPR_BREAK: {
        kind = rt_enum_new(0, TK_BREAK, 0);
        break;
    }
    case CORE_EXPR_CONTINUE: {
        kind = rt_enum_new(0, TK_CONTINUE, 0);
        break;
    }
    case CORE_EXPR_UNIT: {
        kind = rt_enum_new(0, TK_NILLIT, 0);
        break;
    }
    case CORE_EXPR_PASS:
    case CORE_EXPR_DO_BLOCK: {
        kind = rt_enum_new(0, TK_NILLIT, 0);
        break;
    }
    case CORE_EXPR_INTERP: {
        /* Interpolated string: treat as string for now */
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, expr_get_str(ci));
        rt_tuple_set(payload, 1, 0);
        kind = rt_enum_new(0, TK_STRLIT, payload);
        break;
    }
    default:
        fprintf(stderr, "[bridge] unhandled expr tag: %ld\n", (long)tag);
        kind = rt_enum_new(0, TK_ERROR, 0);
        break;
    }

    int64_t expr = rt_object_new(0, 2);
    rt_object_field_set(expr, FI(0), kind);
    rt_object_field_set(expr, FI(1), bridge_make_span());
    return expr;
}

/* ---- Convert array of core stmt indices → typed Block ---- */
static int64_t bridge_convert_block(int64_t core_stmts) {
    int64_t n = rt_array_len(core_stmts);
    int64_t typed = rt_array_new(n);
    for (int64_t i = 0; i < n; i++) {
        int64_t si = rt_array_get(core_stmts, i);
        rt_array_push(typed, bridge_convert_stmt(si));
    }
    int64_t block = rt_object_new(0, 2);
    rt_object_field_set(block, FI(0), typed);  /* stmts */
    rt_object_field_set(block, FI(1), bridge_make_span());
    return block;
}

/* ---- Convert core statement → typed Stmt ---- */
static int64_t bridge_convert_stmt(int64_t ci) {
    int64_t tag = stmt_get_tag(ci);
    int64_t kind;

    switch (tag) {
    case CORE_STMT_EXPR: {
        int64_t expr = bridge_convert_expr(stmt_get_expr(ci));
        kind = rt_enum_new(0, TS_EXPR, expr);
        break;
    }
    case CORE_STMT_VAL: {
        int64_t name = stmt_get_name(ci);
        int64_t tt = stmt_get_type(ci);
        int64_t init = bridge_convert_expr(stmt_get_expr(ci));
        int64_t type_obj = (tt > 0) ? bridge_convert_type(tt) : 0;
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, name);
        rt_tuple_set(payload, 1, type_obj);
        rt_tuple_set(payload, 2, init);
        kind = rt_enum_new(0, TS_VAL, payload);
        break;
    }
    case CORE_STMT_VAR: {
        int64_t name = stmt_get_name(ci);
        int64_t tt = stmt_get_type(ci);
        int64_t ei = stmt_get_expr(ci);
        int64_t init = (ei >= 0) ? bridge_convert_expr(ei) : 0;
        int64_t type_obj = (tt > 0) ? bridge_convert_type(tt) : 0;
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, name);
        rt_tuple_set(payload, 1, type_obj);
        rt_tuple_set(payload, 2, init);
        kind = rt_enum_new(0, TS_VAR, payload);
        break;
    }
    case CORE_STMT_ASSIGN: {
        int64_t target = bridge_convert_expr(stmt_get_expr(ci));
        /* The assigned value is stored in stmt_body[ci][0] as an expr index */
        int64_t body = stmt_get_body(ci);
        int64_t value = 0;
        if (rt_array_len(body) > 0)
            value = bridge_convert_expr(rt_array_get(body, 0));
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, target);
        rt_tuple_set(payload, 1, 0); /* AssignOp = nil (simple assign) */
        rt_tuple_set(payload, 2, value);
        kind = rt_enum_new(0, TS_ASSIGN, payload);
        break;
    }
    case CORE_STMT_RETURN: {
        int64_t ei = stmt_get_expr(ci);
        int64_t val = (ei >= 0) ? bridge_convert_expr(ei) : 0;
        kind = rt_enum_new(0, TS_RETURN, val);
        break;
    }
    case CORE_STMT_IF: {
        int64_t cond = bridge_convert_expr(stmt_get_expr(ci));
        int64_t body = bridge_convert_block(stmt_get_body(ci));
        /* elif chain via stmt_type_tag = elif_idx */
        int64_t elif_idx = stmt_get_type(ci);
        int64_t else_block = 0;
        if (elif_idx >= 0) {
            int64_t econd = elif_get_cond(elif_idx);
            int64_t ebody = elif_get_body(elif_idx);
            int64_t eelse = elif_get_else(elif_idx);
            if (econd >= 0) {
                /* elif: create nested if expr */
                int64_t elif_cond_e = bridge_convert_expr(econd);
                int64_t elif_body_b = bridge_convert_block(ebody);
                int64_t elif_else_b = (rt_array_len(eelse) > 0) ? bridge_convert_block(eelse) : 0;
                int64_t ep = rt_tuple_new(3);
                rt_tuple_set(ep, 0, elif_cond_e);
                rt_tuple_set(ep, 1, elif_body_b);
                rt_tuple_set(ep, 2, elif_else_b);
                int64_t elif_kind = rt_enum_new(0, TK_IF, ep);
                int64_t elif_expr = rt_object_new(0, 2);
                rt_object_field_set(elif_expr, FI(0), elif_kind);
                rt_object_field_set(elif_expr, FI(1), bridge_make_span());
                /* Wrap in block with single stmt */
                int64_t elif_stmt_kind = rt_enum_new(0, TS_EXPR, elif_expr);
                int64_t elif_stmt = rt_object_new(0, 2);
                rt_object_field_set(elif_stmt, FI(0), elif_stmt_kind);
                rt_object_field_set(elif_stmt, FI(1), bridge_make_span());
                int64_t stmts = rt_array_new(1);
                rt_array_push(stmts, elif_stmt);
                else_block = rt_object_new(0, 2);
                rt_object_field_set(else_block, FI(0), stmts);
                rt_object_field_set(else_block, FI(1), bridge_make_span());
            } else if (rt_array_len(eelse) > 0) {
                else_block = bridge_convert_block(eelse);
            }
        }
        /* Wrap as ExprKind::If inside StmtKind::Expr */
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, cond);
        rt_tuple_set(payload, 1, body);
        rt_tuple_set(payload, 2, else_block);
        int64_t if_kind = rt_enum_new(0, TK_IF, payload);
        int64_t if_expr = rt_object_new(0, 2);
        rt_object_field_set(if_expr, FI(0), if_kind);
        rt_object_field_set(if_expr, FI(1), bridge_make_span());
        kind = rt_enum_new(0, TS_EXPR, if_expr);
        break;
    }
    case CORE_STMT_FOR: {
        int64_t name = stmt_get_name(ci);
        int64_t iter = bridge_convert_expr(stmt_get_expr(ci));
        int64_t body = bridge_convert_block(stmt_get_body(ci));
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, name);
        rt_tuple_set(payload, 1, iter);
        rt_tuple_set(payload, 2, body);
        kind = rt_enum_new(0, TS_FOR, payload);
        break;
    }
    case CORE_STMT_WHILE: {
        int64_t cond = bridge_convert_expr(stmt_get_expr(ci));
        int64_t body = bridge_convert_block(stmt_get_body(ci));
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, cond);
        rt_tuple_set(payload, 1, body);
        kind = rt_enum_new(0, TS_WHILE, payload);
        break;
    }
    case CORE_STMT_MATCH: {
        int64_t scrutinee = bridge_convert_expr(stmt_get_expr(ci));
        int64_t arm_indices = stmt_get_body(ci);
        int64_t n = rt_array_len(arm_indices);
        int64_t typed_arms = rt_array_new(n);
        for (int64_t i = 0; i < n; i++) {
            int64_t ai = rt_array_get(arm_indices, i);
            int64_t pat = bridge_convert_expr(arm_get_pattern(ai));
            int64_t abody = arm_get_body(ai);
            int64_t bblock = bridge_convert_block(abody);
            int64_t arm = rt_object_new(0, 4);
            rt_object_field_set(arm, FI(0), pat);
            rt_object_field_set(arm, FI(1), 0);
            rt_object_field_set(arm, FI(2), bblock);
            rt_object_field_set(arm, FI(3), arm_get_binding(ai));
            rt_array_push(typed_arms, arm);
        }
        int64_t payload = rt_tuple_new(2);
        rt_tuple_set(payload, 0, scrutinee);
        rt_tuple_set(payload, 1, typed_arms);
        int64_t match_kind = rt_enum_new(0, TK_MATCH, payload);
        int64_t match_expr = rt_object_new(0, 2);
        rt_object_field_set(match_expr, FI(0), match_kind);
        rt_object_field_set(match_expr, FI(1), bridge_make_span());
        kind = rt_enum_new(0, TS_EXPR, match_expr);
        break;
    }
    case CORE_STMT_BREAK: {
        kind = rt_enum_new(0, TS_BREAK, 0);
        break;
    }
    case CORE_STMT_CONTINUE: {
        kind = rt_enum_new(0, TS_CONTINUE, 0);
        break;
    }
    case CORE_STMT_COMPOUND_ASSIGN: {
        /* compound assign: target = stmt_expr, op = stmt_type_tag, value = stmt_body[0] */
        int64_t target = bridge_convert_expr(stmt_get_expr(ci));
        int64_t op = stmt_get_type(ci);
        int64_t body = stmt_get_body(ci);
        int64_t value = 0;
        if (rt_array_len(body) > 0)
            value = bridge_convert_expr(rt_array_get(body, 0));
        int64_t payload = rt_tuple_new(3);
        rt_tuple_set(payload, 0, target);
        rt_tuple_set(payload, 1, op);
        rt_tuple_set(payload, 2, value);
        kind = rt_enum_new(0, TS_ASSIGN, payload);
        break;
    }
    default:
        fprintf(stderr, "[bridge] unhandled stmt tag: %ld\n", (long)tag);
        kind = rt_enum_new(0, TS_EXPR, 0);
        break;
    }

    int64_t stmt = rt_object_new(0, 2);
    rt_object_field_set(stmt, FI(0), kind);
    rt_object_field_set(stmt, FI(1), bridge_make_span());
    return stmt;
}

/* ---- Convert core function decl → typed Function (18 fields) ---- */
static int64_t bridge_convert_function(int64_t di) {
    int64_t name         = decl_get_name(di);
    int64_t ret_type_tag = decl_get_ret_type(di);
    int64_t core_body    = decl_get_body(di);
    int64_t is_pub       = (int64_t)decl_get_is_pub(di);
    int64_t is_async_v   = decl_get_is_async(di);
    int64_t pnames       = decl_get_param_names(di);
    int64_t ptypes       = decl_get_param_types(di);

    /* Build params (Param: 6 fields) */
    int64_t params = rt_array_new(0);
    int64_t np = rt_array_len(pnames);
    for (int64_t i = 0; i < np; i++) {
        int64_t pn = rt_array_get(pnames, i);
        int64_t pt_tag = rt_array_get(ptypes, i);
        int64_t param = rt_object_new(0, 6);
        rt_object_field_set(param, FI(0), pn);              /* name */
        rt_object_field_set(param, FI(1), pt_tag > 0 ? 1 : 0); /* has_type_ */
        rt_object_field_set(param, FI(2), pt_tag > 0 ? bridge_convert_type(pt_tag) : 0);
        rt_object_field_set(param, FI(3), 0);                /* has_default */
        rt_object_field_set(param, FI(4), 0);                /* default = nil */
        rt_object_field_set(param, FI(5), bridge_make_span());
        rt_array_push(params, param);
    }

    int64_t has_ret  = (ret_type_tag > 0) ? 1 : 0;
    int64_t ret_type = has_ret ? bridge_convert_type(ret_type_tag) : 0;
    int64_t body     = bridge_convert_block(core_body);

    int64_t fn = rt_object_new(0, 18);
    rt_object_field_set(fn, FI(0), name);
    rt_object_field_set(fn, FI(1), rt_array_new(0));   /* type_params */
    rt_object_field_set(fn, FI(2), params);
    rt_object_field_set(fn, FI(3), has_ret);
    rt_object_field_set(fn, FI(4), ret_type);
    rt_object_field_set(fn, FI(5), body);
    rt_object_field_set(fn, FI(6), is_async_v);
    rt_object_field_set(fn, FI(7), 0);                 /* is_static */
    rt_object_field_set(fn, FI(8), is_pub);
    rt_object_field_set(fn, FI(9), 0);                 /* is_method */
    rt_object_field_set(fn, FI(10), 0);                 /* is_mutable */
    rt_object_field_set(fn, FI(11), 0);                 /* is_const */
    rt_object_field_set(fn, FI(12), 0);                 /* is_kernel */
    rt_object_field_set(fn, FI(13), 0);                 /* is_extern */
    rt_object_field_set(fn, FI(14), rt_array_new(0));   /* attributes */
    rt_object_field_set(fn, FI(15), 0);                 /* has_doc_comment */
    rt_object_field_set(fn, FI(16), str_from(""));      /* doc_comment */
    rt_object_field_set(fn, FI(17), bridge_make_span());
    return fn;
}

/* ---- Convert core struct decl → typed Struct ---- */
static int64_t bridge_convert_struct(int64_t di) {
    int64_t name   = decl_get_name(di);
    int64_t fnames = decl_get_fields(di);
    int64_t ftypes = decl_get_field_types(di);
    int64_t fdefs  = decl_get_field_defaults(di);
    int64_t nf = rt_array_len(fnames);

    /* Build fields array */
    int64_t fields = rt_array_new(nf);
    for (int64_t i = 0; i < nf; i++) {
        int64_t fn_ = rt_array_get(fnames, i);
        int64_t ft  = rt_array_get(ftypes, i);
        int64_t fd  = (i < rt_array_len(fdefs)) ? rt_array_get(fdefs, i) : -1;
        /* Field: {name, type, default, has_default} or similar */
        int64_t field = rt_object_new(0, 4);
        rt_object_field_set(field, FI(0), fn_);
        rt_object_field_set(field, FI(1), (ft > 0) ? bridge_convert_type(ft) : 0);
        rt_object_field_set(field, FI(2), (fd >= 0) ? bridge_convert_expr(fd) : 0);
        rt_object_field_set(field, FI(3), bridge_make_span());
        rt_array_push(fields, field);
    }

    /* Struct: {name, type_params, fields, methods, is_public, span} */
    int64_t s = rt_object_new(0, 6);
    rt_object_field_set(s, FI(0), name);
    rt_object_field_set(s, FI(1), rt_array_new(0));   /* type_params */
    rt_object_field_set(s, FI(2), fields);
    rt_object_field_set(s, FI(3), rt_array_new(0));   /* methods */
    rt_object_field_set(s, FI(4), (int64_t)decl_get_is_pub(di));
    rt_object_field_set(s, FI(5), bridge_make_span());
    return s;
}

/* ================================================================
 * Parser__parse — Main bridge entry point
 *
 * Called from compiled code instead of the weak constructor stub.
 * Extracts source from Parser object, calls core parser,
 * converts result to typed Module struct.
 * ================================================================ */
int64_t Parser__parse(int64_t self_) {
    /* Extract source text from Parser object (field 0) */
    int64_t source = rt_object_field_get(self_, FI(0));

    fprintf(stderr, "[bridge] Parser__parse: source=%ld, calling core parser...\n", (long)source);

    /* Call core parser */
    parse_module(source, str_from("main"));

    /* Get parsed declarations */
    int64_t decls = module_get_decls();
    fprintf(stderr, "[bridge] decls=%ld (type_tag=%d)\n", (long)decls,
            decls ? *(int32_t*)((char*)(intptr_t)decls - 16) : -1);
    int64_t n_decls = rt_array_len(decls);
    /* Also check with len() */
    extern int64_t len(int64_t);
    int64_t n_decls2 = len(decls);
    fprintf(stderr, "[bridge] rt_array_len=%ld, len()=%ld\n", (long)n_decls, (long)n_decls2);

    fprintf(stderr, "[bridge] parsed %ld declarations\n", (long)n_decls);

    /* Build dictionaries for Module fields */
    int64_t functions = rt_dict_new(0);
    int64_t classes   = rt_dict_new(0);
    int64_t structs   = rt_dict_new(0);
    int64_t enums     = rt_dict_new(0);

    for (int64_t i = 0; i < n_decls; i++) {
        int64_t di  = rt_array_get(decls, i);
        int64_t tag = decl_get_tag(di);

        switch (tag) {
        case CORE_DECL_FN: {
            int64_t fn = bridge_convert_function(di);
            int64_t fname = decl_get_name(di);
            /* Check if fname is a proper SplString by reading its header */
            if (fname != 0 && (uint64_t)fname >= 0x10000ULL) {
                int32_t otype = *(int32_t*)(intptr_t)fname;
                fprintf(stderr, "[bridge]   fn name raw=%ld obj_type=%d first_bytes=%02x%02x%02x%02x\n",
                        (long)fname, otype,
                        ((unsigned char*)(intptr_t)fname)[0], ((unsigned char*)(intptr_t)fname)[1],
                        ((unsigned char*)(intptr_t)fname)[2], ((unsigned char*)(intptr_t)fname)[3]);
                if (otype == 1) { /* OBJ_STRING */
                    int64_t slen = *(int64_t*)((char*)(intptr_t)fname + 8);
                    char *sdata = (char*)(intptr_t)fname + 16;
                    fprintf(stderr, "[bridge]   fn name str='%.*s' (len=%ld)\n", (int)(slen > 50 ? 50 : slen), sdata, (long)slen);
                }
            }
            rt_dict_set(functions, fname, fn);
            fprintf(stderr, "[bridge]   fn: added\n");
            break;
        }
        case CORE_DECL_EXTERN_FN: {
            int64_t fn = bridge_convert_function(di);
            rt_object_field_set(fn, FI(13), 1); /* is_extern = true */
            rt_dict_set(functions, decl_get_name(di), fn);
            fprintf(stderr, "[bridge]   extern fn: added\n");
            break;
        }
        case CORE_DECL_STRUCT:
        case CORE_DECL_CLASS: {
            int64_t s = bridge_convert_struct(di);
            if (tag == CORE_DECL_CLASS)
                rt_dict_set(classes, decl_get_name(di), s);
            else
                rt_dict_set(structs, decl_get_name(di), s);
            break;
        }
        case CORE_DECL_ENUM: {
            int64_t e = rt_object_new(0, 4);
            rt_object_field_set(e, FI(0), decl_get_name(di));
            rt_object_field_set(e, FI(1), decl_get_fields(di)); /* variant names */
            rt_object_field_set(e, FI(2), rt_array_new(0));
            rt_object_field_set(e, FI(3), bridge_make_span());
            rt_dict_set(enums, decl_get_name(di), e);
            break;
        }
        case CORE_DECL_VAL:
        case CORE_DECL_VAR:
        case CORE_DECL_USE:
        case CORE_DECL_EXPORT:
        case CORE_DECL_IMPL:
            /* Skip for now */
            break;
        default:
            fprintf(stderr, "[bridge] skipping decl tag %ld\n", (long)tag);
            break;
        }
    }

    /* Build Module struct (18 fields) */
    int64_t module = rt_object_new(0, 18);
    rt_object_field_set(module, FI(0), str_from("main"));
    rt_object_field_set(module, FI(1), rt_array_new(0));    /* imports */
    rt_object_field_set(module, FI(2), rt_array_new(0));    /* exports */
    rt_object_field_set(module, FI(3), functions);
    rt_object_field_set(module, FI(4), classes);
    rt_object_field_set(module, FI(5), rt_dict_new(0));     /* actors */
    rt_object_field_set(module, FI(6), structs);
    rt_object_field_set(module, FI(7), enums);
    rt_object_field_set(module, FI(8), rt_dict_new(0));     /* bitfields */
    rt_object_field_set(module, FI(9), rt_dict_new(0));     /* traits */
    rt_object_field_set(module, FI(10), rt_array_new(0));    /* impls */
    rt_object_field_set(module, FI(11), rt_dict_new(0));     /* type_aliases */
    rt_object_field_set(module, FI(12), rt_dict_new(0));     /* constants */
    rt_object_field_set(module, FI(13), rt_array_new(0));    /* static_asserts */
    rt_object_field_set(module, FI(14), rt_array_new(0));    /* aop_advices */
    rt_object_field_set(module, FI(15), rt_array_new(0));    /* di_bindings */
    rt_object_field_set(module, FI(16), rt_array_new(0));    /* arch_rules */
    rt_object_field_set(module, FI(17), rt_array_new(0));    /* mock_decls */

    fprintf(stderr, "[bridge] Module created with %ld functions\n",
            (long)rt_array_len(rt_dict_keys(functions)));

    return module;
}

/* Debug trace for SymbolTable operations */
extern int64_t rt_object_field_get(int64_t obj, int64_t idx);
extern int64_t rt_dict_len(int64_t d);
typedef struct { int32_t obj_type_; int32_t extra_; } HeapHdr2;
typedef struct { HeapHdr2 hdr; int64_t len; char data[]; } SString2;
static int dbg_is_heap(int64_t v) {
    return (v != 0) && ((v & 7) == 0) && (v > 0x10000) && (v < (int64_t)0x7fffffffffff);
}
static int dbg_obj_type(int64_t v) {
    if (!dbg_is_heap(v)) return 0;
    return ((HeapHdr2*)(intptr_t)v)->obj_type_;
}
static const char *dbg_str(int64_t v) {
    if (dbg_is_heap(v) && dbg_obj_type(v) == 1) return ((SString2*)(intptr_t)v)->data;
    if (v == 0) return "(nil)";
    static char buf[64];
    snprintf(buf, sizeof(buf), "(int:%ld)", (long)v);
    return buf;
}

void __dbg_st_define(int64_t self, int64_t name) {
    int64_t syms = rt_object_field_get(self, 0);
    int64_t scopes = rt_object_field_get(self, 8);
    fprintf(stderr, "[ST::define] name='%s' syms_len=%ld scopes_len=%ld\n",
            dbg_str(name), (long)rt_dict_len(syms), (long)rt_dict_len(scopes));
}

void __dbg_st_lookup(int64_t self, int64_t name) {
    int64_t syms = rt_object_field_get(self, 0);
    int64_t scopes = rt_object_field_get(self, 8);
    int64_t cur_scope = rt_object_field_get(self, 16);
    fprintf(stderr, "[ST::lookup] name='%s' syms_len=%ld scopes_len=%ld cur_scope=%ld\n",
            dbg_str(name), (long)rt_dict_len(syms), (long)rt_dict_len(scopes),
            (long)cur_scope);
}

