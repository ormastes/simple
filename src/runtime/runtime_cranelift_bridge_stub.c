/* Cranelift JIT bridge: NAMED-TRAP stubs for the core-C-bootstrap lane.
 *
 * Bug: doc/08_tracking/bug/stage2_link_full_undefined_symbol_census_2026-09-07.md
 * ("Bucket 2 deferred: cranelift JIT bridge", 75 symbols).
 *
 * `src/lib/nogc_sync_mut/sffi/codegen.spl` declares `extern fn rt_cranelift_*`
 * wrappers around the compiler's Cranelift-backed JIT/AOT codegen path
 * (`compiler.backend.backend.cranelift_codegen_adapter`,
 * `compiler.backend.codegen`). The REAL implementations of every one of these
 * symbols already exist -- in Rust, in
 * `src/compiler_rust/compiler/src/codegen/cranelift_sffi.rs` and
 * `src/compiler_rust/compiler/src/interpreter_extern/cranelift.rs` -- backed
 * by the actual `cranelift-codegen`/`cranelift-jit`/`cranelift-object` crates.
 * They are exported from `libsimple_compiler.so` (the hosted/Stage4 lane) and
 * from `native_all` (the Windows/hosted native lane).
 *
 * The `core-c-bootstrap` runtime bundle used by Stage 2/3's `native-build`
 * (`build_core_c_runtime_library` / `native_project::tools::build_c_runtime_library`
 * with `include_stage4_hosted = false`) links NEITHER of those -- it is a
 * plain static archive of hand-written C, with no Cranelift crate and no
 * concept of a JIT at all. Stage 2's own default backend is LLVM
 * (`scripts/bootstrap/bootstrap-from-scratch.sh`: `backend=llvm` unless
 * `--backend=cranelift` is passed explicitly), so every one of these 75
 * symbols is DEAD CODE for that lane: `codegen.spl` is part of the compiler's
 * full closure and gets compiled in, but `compile_cranelift_function` and
 * friends (`src/compiler/70.backend/codegen.spl`) are never reached at
 * runtime unless a caller explicitly asks for the cranelift backend.
 *
 * Re-implementing real Cranelift IR-builder semantics in C without linking
 * the actual `cranelift-codegen` crate would mean inventing behaviour for a
 * JIT compiler backend -- exactly what CLAUDE.md forbids ("do not invent
 * behaviour"). Porting the real Rust crate into this lane was evaluated and
 * rejected: it is the same class of design decision as the sqlite lane's
 * deliberate exclusion (avoid forcing a heavy dependency onto every native
 * binary built by this bundle) and does not fit a mechanical, safely
 * verifiable change.
 *
 * So every symbol here is a NAMED LOUD TRAP via the existing
 * `rt_trap_unimplemented(const char *symbol)` helper (declared in
 * `runtime.h`, defined in `runtime_native.c`, already used for the GPU
 * intrinsics and pattern-matching traps in that file for the identical
 * reason: a fabricated return value would corrupt the caller's state,
 * while a loud abort naming the symbol is honest and strictly better than
 * the previous behaviour -- an unresolved external that the native link
 * either refused outright or (worse, on a lenient linker) turned into a
 * NULL-GOT SIGSEGV with no diagnostic at all.
 *
 * This file is registered ONLY in `build_core_c_runtime_library`'s member
 * list (`native_project/tools.rs`, the `!include_stage4_hosted` branch) --
 * never in `build_stage4_c_runtime_library`'s list and never in the Rust
 * crate's own build. The Stage4/hosted/native_all lanes already define the
 * real symbols; adding a second definition there would be an instant
 * "symbol is already defined" break. Kept in its own translation unit
 * (not appended to `runtime_native.c`) specifically to avoid collision with
 * a concurrent change to that file (see the census doc's handoff notes).
 */

#include "runtime.h"

/* ---- Module Management -------------------------------------------------- */

int64_t rt_cranelift_new_module(int64_t name_ptr, int64_t name_len, int64_t target) {
    (void)name_ptr; (void)name_len; (void)target;
    rt_trap_unimplemented("rt_cranelift_new_module");
    return 0;
}

int64_t rt_cranelift_new_aot_module_triple(int64_t name_ptr, int64_t name_len, int64_t target_ptr, int64_t target_len) {
    (void)name_ptr; (void)name_len; (void)target_ptr; (void)target_len;
    rt_trap_unimplemented("rt_cranelift_new_aot_module_triple");
    return 0;
}

int64_t rt_cranelift_finalize_module(int64_t module) {
    (void)module;
    rt_trap_unimplemented("rt_cranelift_finalize_module");
    return 0;
}

void rt_cranelift_free_module(int64_t module) {
    (void)module;
    rt_trap_unimplemented("rt_cranelift_free_module");
}

int64_t rt_cranelift_declare_string_data(int64_t module, int64_t bytes_ptr, int64_t bytes_len) {
    (void)module; (void)bytes_ptr; (void)bytes_len;
    rt_trap_unimplemented("rt_cranelift_declare_string_data");
    return 0;
}

int64_t rt_cranelift_declare_global_data(int64_t module, int64_t name_ptr, int64_t name_len, int64_t type_, int64_t initial_bits) {
    (void)module; (void)name_ptr; (void)name_len; (void)type_; (void)initial_bits;
    rt_trap_unimplemented("rt_cranelift_declare_global_data");
    return 0;
}

int64_t rt_cranelift_declare_global_data_v2(int64_t module, int64_t name_ptr, int64_t name_len, int64_t type_, int64_t initial_bits, int64_t linkage, int64_t alignment) {
    (void)module; (void)name_ptr; (void)name_len; (void)type_; (void)initial_bits; (void)linkage; (void)alignment;
    rt_trap_unimplemented("rt_cranelift_declare_global_data_v2");
    return 0;
}

int64_t rt_cranelift_data_addr_in_func(int64_t ctx, int64_t data_id) {
    (void)ctx; (void)data_id;
    rt_trap_unimplemented("rt_cranelift_data_addr_in_func");
    return 0;
}

int64_t rt_cranelift_function_addr_in_func(int64_t ctx, int64_t name_ptr, int64_t name_len) {
    (void)ctx; (void)name_ptr; (void)name_len;
    rt_trap_unimplemented("rt_cranelift_function_addr_in_func");
    return 0;
}

/* ---- Function Building ---------------------------------------------------*/

int64_t rt_cranelift_begin_function(int64_t module, int64_t name_ptr, int64_t name_len, int64_t sig) {
    (void)module; (void)name_ptr; (void)name_len; (void)sig;
    rt_trap_unimplemented("rt_cranelift_begin_function");
    return 0;
}

int64_t rt_cranelift_end_function(int64_t ctx) {
    (void)ctx;
    rt_trap_unimplemented("rt_cranelift_end_function");
    return 0;
}

bool rt_cranelift_define_function(int64_t module, int64_t func_id, int64_t ctx) {
    (void)module; (void)func_id; (void)ctx;
    rt_trap_unimplemented("rt_cranelift_define_function");
    return false;
}

/* ---- Signature Building --------------------------------------------------*/

int64_t rt_cranelift_new_signature(int64_t call_conv) {
    (void)call_conv;
    rt_trap_unimplemented("rt_cranelift_new_signature");
    return 0;
}

void rt_cranelift_sig_add_param(int64_t sig, int64_t type_) {
    (void)sig; (void)type_;
    rt_trap_unimplemented("rt_cranelift_sig_add_param");
}

void rt_cranelift_sig_set_return(int64_t sig, int64_t type_) {
    (void)sig; (void)type_;
    rt_trap_unimplemented("rt_cranelift_sig_set_return");
}

/* ---- Block Management -----------------------------------------------------*/

int64_t rt_cranelift_create_block(int64_t ctx) {
    (void)ctx;
    rt_trap_unimplemented("rt_cranelift_create_block");
    return 0;
}

void rt_cranelift_switch_to_block(int64_t ctx, int64_t block) {
    (void)ctx; (void)block;
    rt_trap_unimplemented("rt_cranelift_switch_to_block");
}

void rt_cranelift_seal_block(int64_t ctx, int64_t block) {
    (void)ctx; (void)block;
    rt_trap_unimplemented("rt_cranelift_seal_block");
}

void rt_cranelift_seal_all_blocks(int64_t ctx) {
    (void)ctx;
    rt_trap_unimplemented("rt_cranelift_seal_all_blocks");
}

/* ---- Block Parameters ------------------------------------------------------*/

int64_t rt_cranelift_append_block_param(int64_t ctx, int64_t block, int64_t type_) {
    (void)ctx; (void)block; (void)type_;
    rt_trap_unimplemented("rt_cranelift_append_block_param");
    return 0;
}

int64_t rt_cranelift_block_param(int64_t ctx, int64_t block, int64_t index) {
    (void)ctx; (void)block; (void)index;
    rt_trap_unimplemented("rt_cranelift_block_param");
    return 0;
}

/* ---- Value Creation ---------------------------------------------------- */

int64_t rt_cranelift_iconst(int64_t ctx, int64_t type_, int64_t value) {
    (void)ctx; (void)type_; (void)value;
    rt_trap_unimplemented("rt_cranelift_iconst");
    return 0;
}

int64_t rt_cranelift_fconst(int64_t ctx, int64_t type_, double value) {
    (void)ctx; (void)type_; (void)value;
    rt_trap_unimplemented("rt_cranelift_fconst");
    return 0;
}

int64_t rt_cranelift_bconst(int64_t ctx, bool value) {
    (void)ctx; (void)value;
    rt_trap_unimplemented("rt_cranelift_bconst");
    return 0;
}

int64_t rt_cranelift_null(int64_t ctx, int64_t type_) {
    (void)ctx; (void)type_;
    rt_trap_unimplemented("rt_cranelift_null");
    return 0;
}

/* ---- Integer Arithmetic ---------------------------------------------------*/

int64_t rt_cranelift_iadd(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_iadd");
    return 0;
}

int64_t rt_cranelift_isub(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_isub");
    return 0;
}

int64_t rt_cranelift_imul(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_imul");
    return 0;
}

int64_t rt_cranelift_sdiv(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_sdiv");
    return 0;
}

int64_t rt_cranelift_udiv(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_udiv");
    return 0;
}

int64_t rt_cranelift_srem(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_srem");
    return 0;
}

int64_t rt_cranelift_urem(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_urem");
    return 0;
}

/* ---- Floating Point Arithmetic --------------------------------------------*/

int64_t rt_cranelift_fadd(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_fadd");
    return 0;
}

int64_t rt_cranelift_fsub(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_fsub");
    return 0;
}

int64_t rt_cranelift_fmul(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_fmul");
    return 0;
}

int64_t rt_cranelift_fdiv(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_fdiv");
    return 0;
}

/* ---- Bitwise Operations ----------------------------------------------------*/

int64_t rt_cranelift_band(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_band");
    return 0;
}

int64_t rt_cranelift_bor(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_bor");
    return 0;
}

int64_t rt_cranelift_bxor(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_bxor");
    return 0;
}

int64_t rt_cranelift_bnot(int64_t ctx, int64_t a) {
    (void)ctx; (void)a;
    rt_trap_unimplemented("rt_cranelift_bnot");
    return 0;
}

int64_t rt_cranelift_ishl(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_ishl");
    return 0;
}

int64_t rt_cranelift_sshr(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_sshr");
    return 0;
}

int64_t rt_cranelift_ushr(int64_t ctx, int64_t a, int64_t b) {
    (void)ctx; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_ushr");
    return 0;
}

/* ---- Comparison ----------------------------------------------------------*/

int64_t rt_cranelift_icmp(int64_t ctx, int64_t cond, int64_t a, int64_t b) {
    (void)ctx; (void)cond; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_icmp");
    return 0;
}

int64_t rt_cranelift_fcmp(int64_t ctx, int64_t cond, int64_t a, int64_t b) {
    (void)ctx; (void)cond; (void)a; (void)b;
    rt_trap_unimplemented("rt_cranelift_fcmp");
    return 0;
}

/* ---- Memory Operations -----------------------------------------------------*/

int64_t rt_cranelift_load(int64_t ctx, int64_t type_, int64_t addr, int64_t offset) {
    (void)ctx; (void)type_; (void)addr; (void)offset;
    rt_trap_unimplemented("rt_cranelift_load");
    return 0;
}

void rt_cranelift_store(int64_t ctx, int64_t value, int64_t addr, int64_t offset) {
    (void)ctx; (void)value; (void)addr; (void)offset;
    rt_trap_unimplemented("rt_cranelift_store");
}

int64_t rt_cranelift_stack_slot(int64_t ctx, int64_t size, int64_t align) {
    (void)ctx; (void)size; (void)align;
    rt_trap_unimplemented("rt_cranelift_stack_slot");
    return 0;
}

int64_t rt_cranelift_stack_addr(int64_t ctx, int64_t slot, int64_t offset) {
    (void)ctx; (void)slot; (void)offset;
    rt_trap_unimplemented("rt_cranelift_stack_addr");
    return 0;
}

/* ---- Control Flow ----------------------------------------------------------*/

void rt_cranelift_jump(int64_t ctx, int64_t block) {
    (void)ctx; (void)block;
    rt_trap_unimplemented("rt_cranelift_jump");
}

void rt_cranelift_brif(int64_t ctx, int64_t cond, int64_t then_block, int64_t else_block) {
    (void)ctx; (void)cond; (void)then_block; (void)else_block;
    rt_trap_unimplemented("rt_cranelift_brif");
}

void rt_cranelift_return(int64_t ctx, int64_t value) {
    (void)ctx; (void)value;
    rt_trap_unimplemented("rt_cranelift_return");
}

void rt_cranelift_return_void(int64_t ctx) {
    (void)ctx;
    rt_trap_unimplemented("rt_cranelift_return_void");
}

void rt_cranelift_trap(int64_t ctx, int64_t code) {
    (void)ctx; (void)code;
    rt_trap_unimplemented("rt_cranelift_trap");
}

/* ---- Function Calls ---------------------------------------------------------*/

void rt_cranelift_call_args_clear(int64_t ctx) {
    (void)ctx;
    rt_trap_unimplemented("rt_cranelift_call_args_clear");
}

bool rt_cranelift_call_arg(int64_t ctx, int64_t value) {
    (void)ctx; (void)value;
    rt_trap_unimplemented("rt_cranelift_call_arg");
    return false;
}

int64_t rt_cranelift_call(int64_t ctx, int64_t func, int64_t args_ptr, int64_t args_len) {
    (void)ctx; (void)func; (void)args_ptr; (void)args_len;
    rt_trap_unimplemented("rt_cranelift_call");
    return 0;
}

int64_t rt_cranelift_call_indirect(int64_t ctx, int64_t sig, int64_t addr, int64_t args_ptr, int64_t args_len) {
    (void)ctx; (void)sig; (void)addr; (void)args_ptr; (void)args_len;
    rt_trap_unimplemented("rt_cranelift_call_indirect");
    return 0;
}

/* ---- JIT Execution -----------------------------------------------------------*/

int64_t rt_cranelift_get_function_ptr(int64_t module, int64_t name_ptr, int64_t name_len) {
    (void)module; (void)name_ptr; (void)name_len;
    rt_trap_unimplemented("rt_cranelift_get_function_ptr");
    return 0;
}

int64_t rt_cranelift_call_function_ptr(int64_t ptr, int64_t args_ptr, int64_t args_len) {
    (void)ptr; (void)args_ptr; (void)args_len;
    rt_trap_unimplemented("rt_cranelift_call_function_ptr");
    return 0;
}

/* ---- Function Declaration ------------------------------------------------------*/

int64_t rt_cranelift_declare_function(int64_t module, int64_t name_ptr, int64_t name_len, int64_t sig, int64_t linkage) {
    (void)module; (void)name_ptr; (void)name_len; (void)sig; (void)linkage;
    rt_trap_unimplemented("rt_cranelift_declare_function");
    return 0;
}

int64_t rt_cranelift_import_function(int64_t ctx, int64_t func_handle) {
    (void)ctx; (void)func_handle;
    rt_trap_unimplemented("rt_cranelift_import_function");
    return 0;
}

void rt_cranelift_append_func_params(int64_t ctx, int64_t block) {
    (void)ctx; (void)block;
    rt_trap_unimplemented("rt_cranelift_append_func_params");
}

/* ---- AOT Object File Emission -----------------------------------------------------*/

bool rt_cranelift_emit_object_raw(int64_t module, int64_t path_ptr, int64_t path_len) {
    (void)module; (void)path_ptr; (void)path_len;
    rt_trap_unimplemented("rt_cranelift_emit_object_raw");
    return false;
}

bool rt_cranelift_aot_define_function(int64_t module, int64_t name_ptr, int64_t name_len, int64_t ctx) {
    (void)module; (void)name_ptr; (void)name_len; (void)ctx;
    rt_trap_unimplemented("rt_cranelift_aot_define_function");
    return false;
}

/* ---- Type Conversions ---------------------------------------------------------------*/

int64_t rt_cranelift_sextend(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_sextend");
    return 0;
}

int64_t rt_cranelift_uextend(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_uextend");
    return 0;
}

int64_t rt_cranelift_ireduce(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_ireduce");
    return 0;
}

int64_t rt_cranelift_bitcast(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_bitcast");
    return 0;
}

int64_t rt_cranelift_fcvt_to_sint(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_fcvt_to_sint");
    return 0;
}

int64_t rt_cranelift_fcvt_to_uint(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_fcvt_to_uint");
    return 0;
}

int64_t rt_cranelift_fcvt_from_sint(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_fcvt_from_sint");
    return 0;
}

int64_t rt_cranelift_fcvt_from_uint(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_fcvt_from_uint");
    return 0;
}

int64_t rt_cranelift_fpromote(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_fpromote");
    return 0;
}

int64_t rt_cranelift_fdemote(int64_t ctx, int64_t to_type, int64_t value) {
    (void)ctx; (void)to_type; (void)value;
    rt_trap_unimplemented("rt_cranelift_fdemote");
    return 0;
}
