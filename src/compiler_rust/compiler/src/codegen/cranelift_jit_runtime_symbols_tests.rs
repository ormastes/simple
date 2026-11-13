//! The `rt_cranelift_*` JIT provider (the one pure-Simple code drives) links
//! runtime externs through the seed JIT's own runtime symbol table, with the
//! `RuntimeFuncSpec` signature, and fails closed on anything else.
//! Bug: doc/08_tracking/bug/pure_simple_jit_provider_registers_no_runtime_symbols_2026-11-13.md
use super::*;

#[cfg(target_arch = "x86_64")]
const HOST_TARGET: i64 = CL_TARGET_X86_64;
#[cfg(target_arch = "aarch64")]
const HOST_TARGET: i64 = CL_TARGET_AARCH64;

const MISSING_SYMBOL: &str = "simple_jit_provider_zz_symbol_defined_nowhere";

unsafe fn jit_module(name: &str) -> i64 {
    let module = rt_cranelift_new_module(name.as_ptr() as i64, name.len() as i64, HOST_TARGET);
    assert!(module > 0, "host JIT module {name}");
    module
}

/// Signature in the provider's own type codes, platform call convention.
unsafe fn signature(params: &[i64], ret: Option<i64>) -> i64 {
    let sig = rt_cranelift_new_signature(-1);
    for &param in params {
        rt_cranelift_sig_add_param(sig, param);
    }
    if let Some(ret) = ret {
        rt_cranelift_sig_set_return(sig, ret);
    }
    sig
}

unsafe fn declare_import(module: i64, name: &str, sig: i64) -> i64 {
    rt_cranelift_declare_function(module, name.as_ptr() as i64, name.len() as i64, sig, 1)
}

/// `main() -> i64` that returns `callee()`, an import of `callee: () -> i64`.
unsafe fn define_main_calling(module: i64, entry: &str, callee: &str) -> bool {
    let callee_sig = signature(&[], Some(CL_TYPE_I64));
    let handle = declare_import(module, callee, callee_sig);
    if handle == 0 {
        return false;
    }
    let main_sig = signature(&[], Some(CL_TYPE_I64));
    let ctx = rt_cranelift_begin_function(module, entry.as_ptr() as i64, entry.len() as i64, main_sig);
    assert!(ctx > 0);
    let block = rt_cranelift_create_block(ctx);
    rt_cranelift_switch_to_block(ctx, block);
    rt_cranelift_seal_block(ctx, block);
    let func_ref = rt_cranelift_import_function(ctx, handle);
    assert!(func_ref > 0);
    let value = rt_cranelift_call(ctx, func_ref, 0, 0);
    assert!(value > 0);
    rt_cranelift_return(ctx, value);
    assert_eq!(rt_cranelift_end_function(ctx), ctx);
    assert!(rt_cranelift_define_function(module, ctx, ctx));
    true
}

#[test]
fn provider_refuses_an_import_no_table_or_process_symbol_backs() {
    unsafe {
        let module = jit_module("jit_rt_missing");
        let sig = signature(&[], Some(CL_TYPE_I64));
        assert_eq!(
            declare_import(module, MISSING_SYMBOL, sig),
            0,
            "an unresolvable import must be refused at declaration, not abort the host at finalize"
        );
        assert_eq!(
            rt_cranelift_finalize_module(module),
            0,
            "the refusal latches the module"
        );
        rt_cranelift_free_module(module);
    }
}

#[test]
fn provider_refuses_a_runtime_import_whose_signature_differs_from_its_spec() {
    unsafe {
        let module = jit_module("jit_rt_bad_sig");
        // RuntimeFuncSpec: rt_getpid() -> i64.
        let wrong_arity = signature(&[CL_TYPE_I64], Some(CL_TYPE_I64));
        assert_eq!(declare_import(module, "rt_getpid", wrong_arity), 0);
        rt_cranelift_free_module(module);

        let module = jit_module("jit_rt_bad_ret");
        // RuntimeFuncSpec: rt_file_exists(ptr, len) -> i8, never i64.
        let wrong_return = signature(&[CL_TYPE_I64, CL_TYPE_I64], Some(CL_TYPE_I64));
        assert_eq!(declare_import(module, "rt_file_exists", wrong_return), 0);
        rt_cranelift_free_module(module);
    }
}

#[test]
fn provider_links_and_calls_registered_runtime_symbols() {
    unsafe {
        // finalize is only safe to reach once the provider fails closed on a miss.
        let guard = jit_module("jit_rt_guard");
        assert_eq!(
            declare_import(guard, MISSING_SYMBOL, signature(&[], Some(CL_TYPE_I64))),
            0
        );
        rt_cranelift_free_module(guard);

        let module = jit_module("jit_rt_link");
        assert!(define_main_calling(module, "jit_rt_pid", "rt_getpid"));
        assert_eq!(rt_cranelift_finalize_module(module), module);
        let name = "jit_rt_pid";
        let address = rt_cranelift_get_function_ptr(module, name.as_ptr() as i64, name.len() as i64);
        assert_ne!(address, 0);
        let function: extern "C" fn() -> i64 = std::mem::transmute(address as *const ());
        assert_eq!(function(), std::process::id() as i64);
        rt_cranelift_free_module(module);

        let module = jit_module("jit_rt_time");
        assert!(define_main_calling(module, "jit_rt_now", "rt_time_now_unix_micros"));
        assert_eq!(rt_cranelift_finalize_module(module), module);
        let name = "jit_rt_now";
        let address = rt_cranelift_get_function_ptr(module, name.as_ptr() as i64, name.len() as i64);
        let function: extern "C" fn() -> i64 = std::mem::transmute(address as *const ());
        let before = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_micros() as i64;
        let jit_now = function();
        assert!(
            jit_now >= before && jit_now - before < 60_000_000,
            "jit={jit_now} host={before}"
        );
        rt_cranelift_free_module(module);
    }
}

#[test]
fn provider_registers_the_seed_jit_runtime_symbol_table() {
    let provider = super::super::jit::default_runtime_provider();
    let seed_jit = super::super::jit::seed_jit_runtime_symbol_table(provider.as_ref());
    let registered = jit_provider_runtime_symbols();
    // One source: the provider's table is exactly the seed JIT's table.
    assert_eq!(registered.len(), seed_jit.len());
    // Names, not addresses: a dynamic provider maps its own copy per load.
    for (&(name, address), &(seed_name, _)) in registered.iter().zip(seed_jit.iter()) {
        assert_eq!(name, seed_name);
        assert!(!address.is_null(), "{name}");
    }
    let host = simple_common::target::Target::host();
    let linkable = registered
        .iter()
        .filter(|(name, _)| super::super::runtime_sffi::spec_for_target(&host, name).is_some())
        .count();
    eprintln!(
        "jit provider runtime symbols: registered={} linkable_with_spec={linkable}",
        registered.len()
    );
    assert!(linkable > 0);
    for name in [
        "rt_getpid",
        "rt_time_now_unix_micros",
        "rt_string_new_literal",
        "rt_string_len",
        "rt_file_size",
    ] {
        assert!(
            matches!(jit_runtime_import_spec(name), Some(Some(_))),
            "{name} must be registered with a spec"
        );
    }
    assert!(jit_runtime_import_spec(MISSING_SYMBOL).is_none());
}

#[test]
fn runtime_table_import_linkage_never_binds_a_process_symbol() {
    unsafe {
        let module = jit_module("jit_rt_only");
        // getpid is a libc process symbol, not a runtime-table name.
        let sig = signature(&[], Some(CL_TYPE_I32));
        let name = "getpid";
        assert_eq!(
            rt_cranelift_declare_function(
                module,
                name.as_ptr() as i64,
                name.len() as i64,
                sig,
                CRANELIFT_LINKAGE_RUNTIME_IMPORT
            ),
            0
        );
        rt_cranelift_free_module(module);

        let module = jit_module("jit_rt_only_ok");
        let sig = signature(&[], Some(CL_TYPE_I64));
        let name = "rt_getpid";
        assert!(
            rt_cranelift_declare_function(
                module,
                name.as_ptr() as i64,
                name.len() as i64,
                sig,
                CRANELIFT_LINKAGE_RUNTIME_IMPORT
            ) > 0
        );
        rt_cranelift_free_module(module);

        let aot = rt_cranelift_new_aot_module(b"aot_rt_only".as_ptr() as i64, 11, HOST_TARGET);
        let sig = signature(&[], Some(CL_TYPE_I64));
        assert_eq!(
            rt_cranelift_declare_function(
                aot,
                name.as_ptr() as i64,
                name.len() as i64,
                sig,
                CRANELIFT_LINKAGE_RUNTIME_IMPORT
            ),
            0
        );
        rt_cranelift_free_module(aot);
    }
}
