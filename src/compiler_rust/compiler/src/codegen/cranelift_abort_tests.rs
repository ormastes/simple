//! Module cancellation exercises unfinished real FunctionBuilders. Run serially:
//! registry reset intentionally owns the whole provider registry.
use super::*;

#[cfg(target_arch = "x86_64")]
const NATIVE_TEST_TARGET: i64 = CL_TARGET_X86_64;
#[cfg(target_arch = "aarch64")]
const NATIVE_TEST_TARGET: i64 = CL_TARGET_AARCH64;

unsafe fn partial_function(module: i64, name: &str, with_instruction: bool) -> (i64, i64) {
    let sig = rt_cranelift_new_signature(0);
    rt_cranelift_sig_set_return(sig, CL_TYPE_I64);
    let ctx = rt_cranelift_begin_function(module, name.as_ptr() as i64, name.len() as i64, sig);
    assert!(ctx > 0);
    let block = rt_cranelift_create_block(ctx);
    assert!(block > 0);
    rt_cranelift_switch_to_block(ctx, block);
    if with_instruction {
        assert!(rt_cranelift_iconst(ctx, CL_TYPE_I64, 42) > 0);
    }
    // Deliberately no sealing or terminator. finalize() is invalid for the
    // partially emitted case with debug assertions enabled.
    (ctx, sig)
}

fn assert_retired(ctx: i64) {
    assert!(!ACTIVE_BUILDERS.lock().unwrap().contains_key(&ctx));
    assert!(!BUILDER_BACKINGS.lock().unwrap().contains_key(&ctx));
    assert!(!FINISHED_FUNCS.lock().unwrap().contains_key(&ctx));
}

#[test]
fn abort_module_discards_unsealed_partial_builders_and_repeated_free_is_safe() {
    unsafe {
        rt_cranelift_free_module(0);
        rt_cranelift_free_module(-1);
        let foreign_target = if cfg!(target_arch = "x86_64") {
            CL_TARGET_AARCH64
        } else {
            CL_TARGET_X86_64
        };
        assert_eq!(
            rt_cranelift_new_module(b"foreign".as_ptr() as i64, 7, foreign_target),
            0,
            "foreign-architecture JIT must refuse before entering native PLT machinery"
        );
        for aot in [false, true] {
            let name = b"module_abort";
            let module = if aot {
                rt_cranelift_new_aot_module(name.as_ptr() as i64, name.len() as i64, NATIVE_TEST_TARGET)
            } else {
                rt_cranelift_new_module(name.as_ptr() as i64, name.len() as i64, NATIVE_TEST_TARGET)
            };
            assert!(module > 0);
            if aot {
                assert!(
                    AOT_MODULES
                        .lock()
                        .unwrap()
                        .get(&module)
                        .unwrap()
                        .module
                        .isa()
                        .flags()
                        .is_pic(),
                    "AOT object emission must retain PIC"
                );
            } else {
                let modules = JIT_MODULES.lock().unwrap();
                let flags = modules.get(&module).unwrap().module.isa().flags();
                assert_eq!(flags.is_pic(), cfg!(target_arch = "x86_64"));
                assert!(
                    !flags.use_colocated_libcalls(),
                    "JIT libcalls need long-range relocations"
                );
            }
            let (first, first_sig) = partial_function(module, "partial", true);
            let (second, second_sig) = partial_function(module, "empty_block", false);
            rt_cranelift_free_module(module);
            assert_retired(first);
            assert_retired(second);
            assert_eq!(rt_cranelift_end_function(first), 0);
            assert_eq!(rt_cranelift_create_block(second), 0);
            rt_cranelift_free_module(module);
            assert!(!JIT_MODULES.lock().unwrap().contains_key(&module));
            assert!(!AOT_MODULES.lock().unwrap().contains_key(&module));
            SIGNATURES.lock().unwrap().remove(&first_sig);
            SIGNATURES.lock().unwrap().remove(&second_sig);
        }
    }
}

#[test]
fn abort_stale_module_handle_cannot_cancel_another_active_builder() {
    unsafe {
        let old = rt_cranelift_new_module(b"old".as_ptr() as i64, 3, NATIVE_TEST_TARGET);
        let (old_ctx, old_sig) = partial_function(old, "old_partial", true);
        rt_cranelift_free_module(old);
        assert_retired(old_ctx);
        let next = rt_cranelift_new_module(b"next".as_ptr() as i64, 4, NATIVE_TEST_TARGET);
        assert!(next > 0 && next != old);
        let (next_ctx, next_sig) = partial_function(next, "new_partial", true);
        rt_cranelift_free_module(old);
        assert!(ACTIVE_BUILDERS.lock().unwrap().contains_key(&next_ctx));
        assert!(BUILDER_BACKINGS.lock().unwrap().contains_key(&next_ctx));
        rt_cranelift_free_module(next);
        assert_retired(next_ctx);
        SIGNATURES.lock().unwrap().remove(&old_sig);
        SIGNATURES.lock().unwrap().remove(&next_sig);
    }
}

#[test]
fn abort_module_preserves_other_finished_function_and_successful_execution() {
    unsafe {
        let discarded = rt_cranelift_new_module(b"discarded".as_ptr() as i64, 9, NATIVE_TEST_TARGET);
        let (partial, partial_sig) = partial_function(discarded, "partial", true);
        let module = rt_cranelift_new_module(b"success".as_ptr() as i64, 7, NATIVE_TEST_TARGET);
        assert!(module > 0);
        let sig = rt_cranelift_new_signature(0);
        rt_cranelift_sig_set_return(sig, CL_TYPE_I64);
        let name = b"success_after_abort";
        let ctx = rt_cranelift_begin_function(module, name.as_ptr() as i64, name.len() as i64, sig);
        assert!(ctx > 0);
        let entry = rt_cranelift_create_block(ctx);
        rt_cranelift_switch_to_block(ctx, entry);
        rt_cranelift_seal_block(ctx, entry);
        let value = rt_cranelift_iconst(ctx, CL_TYPE_I64, 42);
        rt_cranelift_return(ctx, value);
        assert_eq!(rt_cranelift_end_function(ctx), ctx);
        rt_cranelift_free_module(discarded);
        assert_retired(partial);
        assert!(FINISHED_FUNCS.lock().unwrap().contains_key(&ctx));
        assert!(rt_cranelift_define_function(module, ctx, ctx));
        assert_eq!(rt_cranelift_finalize_module(module), module);
        let address = rt_cranelift_get_function_ptr(module, name.as_ptr() as i64, name.len() as i64);
        assert_ne!(address, 0);
        let function: extern "C" fn() -> i64 = std::mem::transmute(address as *const ());
        assert_eq!(function(), 42);
        SIGNATURES.lock().unwrap().remove(&sig);
        SIGNATURES.lock().unwrap().remove(&partial_sig);
        rt_cranelift_free_module(module);
    }
}

#[test]
fn abort_registry_reset_discards_partial_builder_before_backing() {
    unsafe {
        let module = rt_cranelift_new_module(b"reset".as_ptr() as i64, 5, NATIVE_TEST_TARGET);
        let (ctx, _) = partial_function(module, "reset_partial", true);
        clear_cranelift_registries();
        assert_retired(ctx);
        assert_eq!(rt_cranelift_end_function(ctx), 0);
        assert!(!JIT_MODULES.lock().unwrap().contains_key(&module));
        clear_cranelift_registries();
    }
}
