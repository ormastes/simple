//! Provider error propagation: valid void results are not errors.
use super::*;

unsafe fn module(name: &str) -> i64 {
    rt_cranelift_new_aot_module(name.as_ptr() as i64, name.len() as i64, CL_TARGET_AARCH64)
}

unsafe fn void_body(module: i64, name: &str) -> i64 {
    let signature = rt_cranelift_new_signature(0);
    let ctx = rt_cranelift_begin_function(module, name.as_ptr() as i64, name.len() as i64, signature);
    assert!(ctx > 0);
    let entry = rt_cranelift_create_block(ctx);
    rt_cranelift_switch_to_block(ctx, entry);
    ctx
}

unsafe fn finish_void(ctx: i64) -> i64 {
    rt_cranelift_return_void(ctx);
    rt_cranelift_seal_all_blocks(ctx);
    rt_cranelift_end_function(ctx)
}

fn output_path(module: i64) -> std::path::PathBuf {
    std::env::temp_dir().join(format!("simple-cranelift-latch-{}-{module}.o", std::process::id()))
}

#[test]
fn declaration_conflict_refuses_publication_and_preserves_existing_file() {
    unsafe {
        let module = module("latch_conflict");
        let original = rt_cranelift_new_signature(0);
        let incompatible = rt_cranelift_new_signature(0);
        rt_cranelift_sig_add_param(incompatible, CL_TYPE_I64);
        let name = "callee";
        assert!(rt_cranelift_declare_function(module, name.as_ptr() as i64, name.len() as i64, original, 1) > 0);
        assert_eq!(rt_cranelift_declare_function(module, name.as_ptr() as i64, name.len() as i64, incompatible, 1), 0);
        assert_eq!(rt_cranelift_finalize_module(module), 0);
        let path = output_path(module);
        std::fs::write(&path, b"previous-output").unwrap();
        assert!(!rt_cranelift_emit_object_impl(module, path.to_str().unwrap()));
        assert_eq!(std::fs::read(&path).unwrap(), b"previous-output");
        std::fs::remove_file(path).unwrap();
        rt_cranelift_free_module(module);
        SIGNATURES.lock().unwrap().remove(&incompatible);
    }
}

#[test]
fn missing_import_refuses_finished_function_and_new_output() {
    unsafe {
        let module = module("latch_import");
        let ctx = void_body(module, "caller");
        assert_eq!(rt_cranelift_import_function(ctx, 0), 0);
        assert_eq!(finish_void(ctx), 0);
        assert!(!ACTIVE_BUILDERS.lock().unwrap().contains_key(&ctx));
        assert!(!BUILDER_BACKINGS.lock().unwrap().contains_key(&ctx));
        assert!(!FINISHED_FUNCS.lock().unwrap().contains_key(&ctx));
        assert!(!rt_cranelift_aot_define_function(module, 0, 0, ctx));
        let path = output_path(module);
        assert!(!rt_cranelift_emit_object_impl(module, path.to_str().unwrap()));
        assert!(!path.exists());
        rt_cranelift_free_module(module);
    }
}

#[test]
fn invalid_call_is_sticky_but_valid_void_zero_and_other_module_remain_valid() {
    unsafe {
        let bad = module("latch_bad_call");
        let good = module("latch_good_void");
        let bad_ctx = void_body(bad, "bad");
        assert_eq!(rt_cranelift_call(bad_ctx, 0, 0, 0), 0);
        assert_eq!(finish_void(bad_ctx), 0);
        let good_ctx = void_body(good, "good");
        let sig = rt_cranelift_new_signature(0);
        let name = "external_void";
        let declaration = rt_cranelift_declare_function(good, name.as_ptr() as i64, name.len() as i64, sig, 1);
        let reference = rt_cranelift_import_function(good_ctx, declaration);
        assert!(reference > 0);
        // A valid void call returns zero and must not poison its module.
        assert_eq!(rt_cranelift_call(good_ctx, reference, 0, 0), 0);
        let finished = finish_void(good_ctx);
        assert!(finished > 0);
        assert!(rt_cranelift_aot_define_function(good, 0, 0, finished));
        assert_eq!(rt_cranelift_finalize_module(good), good);
        let path = output_path(good);
        assert!(rt_cranelift_emit_object_impl(good, path.to_str().unwrap()));
        assert!(!std::fs::read(&path).unwrap().is_empty());
        std::fs::remove_file(path).unwrap();
        rt_cranelift_free_module(bad);
        rt_cranelift_free_module(good);
        assert!(!MODULE_FAILURES.lock().unwrap().contains_key(&bad));
        assert!(!MODULE_FAILURES.lock().unwrap().contains_key(&good));
    }
}

#[test]
fn concurrent_modules_keep_failure_ownership() {
    let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));
    let workers: Vec<_> = [false, true].into_iter().map(|fail| {
        let barrier = barrier.clone();
        std::thread::spawn(move || unsafe {
            let module = module(if fail { "parallel_bad" } else { "parallel_good" });
            if fail {
                let name = "missing_signature";
                assert_eq!(rt_cranelift_declare_function(module, name.as_ptr() as i64, name.len() as i64, 0, 1), 0);
            }
            barrier.wait();
            assert_eq!(rt_cranelift_finalize_module(module), if fail { 0 } else { module });
            rt_cranelift_free_module(module);
            assert!(!MODULE_FAILURES.lock().unwrap().contains_key(&module));
        })
    }).collect();
    for worker in workers { worker.join().unwrap(); }
}

#[test]
fn registry_reset_is_verified_in_an_isolated_test_process() {
    let full_name = format!("{}::reset_child_only", module_path!());
    let test_name = full_name.split_once("::").unwrap().1;
    let output = std::process::Command::new(std::env::current_exe().unwrap())
        .args(["--exact", test_name, "--ignored", "--nocapture", "--test-threads=1"])
        .output().unwrap();
    assert!(output.status.success(), "child stderr: {}", String::from_utf8_lossy(&output.stderr));
    assert!(String::from_utf8_lossy(&output.stdout).contains("1 passed"), "child did not execute reset case");
}

#[test]
#[ignore = "global registry reset; executed alone by registry_reset_is_verified_in_an_isolated_test_process"]
fn reset_child_only() {
    unsafe {
        let module = module("reset_poison");
        let ctx = void_body(module, "unfinished");
        assert_eq!(rt_cranelift_import_function(ctx, 0), 0);
        // This ignored case is launched by exact name in a dedicated process.
        clear_cranelift_registries();
        assert!(MODULE_FAILURES.lock().unwrap().is_empty());
        assert!(!ACTIVE_BUILDERS.lock().unwrap().contains_key(&ctx));
        assert!(!BUILDER_BACKINGS.lock().unwrap().contains_key(&ctx));
    }
}

#[test]
fn failure_after_function_end_still_blocks_definition() {
    unsafe {
        let module = module("latch_late_conflict");
        let ctx = void_body(module, "finished_before_failure");
        let finished = finish_void(ctx);
        assert!(finished > 0);
        let name = "invalid_signature";
        assert_eq!(rt_cranelift_declare_function(module, name.as_ptr() as i64, name.len() as i64, 0, 1), 0);
        assert!(!rt_cranelift_aot_define_function(module, 0, 0, finished));
        assert!(!FINISHED_FUNCS.lock().unwrap().contains_key(&finished));
        assert_eq!(rt_cranelift_finalize_module(module), 0);
        rt_cranelift_free_module(module);
    }
}

#[test]
fn missing_call_argument_value_refuses_function_completion() {
    unsafe {
        let module = module("latch_missing_value");
        let ctx = void_body(module, "caller");
        let signature = rt_cranelift_new_signature(0);
        rt_cranelift_sig_add_param(signature, CL_TYPE_I64);
        let name = "one_argument";
        let declaration = rt_cranelift_declare_function(module, name.as_ptr() as i64, name.len() as i64, signature, 1);
        let reference = rt_cranelift_import_function(ctx, declaration);
        assert!(reference > 0);
        let invalid_values = [i64::MAX];
        assert_eq!(rt_cranelift_call(ctx, reference, invalid_values.as_ptr() as i64, 1), 0);
        assert_eq!(finish_void(ctx), 0);
        assert_eq!(rt_cranelift_finalize_module(module), 0);
        rt_cranelift_free_module(module);
    }
}
