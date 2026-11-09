//! Recovered first-probe miss in `rt_cranelift_function_addr_in_func` must stay
//! silent on stderr.
//!
//! A function value naming a function defined in another module misses on the
//! first probe (only the current module's own functions are pre-declared). The
//! caller declares the import and retries, so the miss is recovered and must
//! not print `cranelift: function address missing declaration <fn>` — that
//! line reads as a codegen failure during triage.
//! Regression: doc/08_tracking/bug/cranelift_function_addr_probe_miss_diagnostic_2026-11-06.md
use simple_compiler::codegen::cranelift_sffi::*;

static STDERR_CAPTURE_MUTEX: std::sync::Mutex<()> = std::sync::Mutex::new(());

/// Redirect fd 2 to a pipe for the duration of `f`, returning everything
/// written to stderr. `eprintln!` writes straight to fd 2, so no flush is
/// needed before restoring. Serialized with a mutex because fd 2 is
/// process-wide.
fn capture_stderr_during(f: impl FnOnce()) -> String {
    struct Restore(i32);
    impl Drop for Restore {
        fn drop(&mut self) {
            unsafe {
                libc::dup2(self.0, 2);
                libc::close(self.0);
            }
        }
    }
    let _guard = STDERR_CAPTURE_MUTEX.lock().unwrap();
    unsafe {
        let mut fds = [-1i32; 2];
        assert_eq!(libc::pipe(fds.as_mut_ptr()), 0, "pipe failed");
        let original = libc::dup(2);
        assert!(original >= 0, "dup failed");
        assert_eq!(libc::dup2(fds[1], 2), 2, "dup2 failed");
        let _restore = Restore(original);
        f();
        libc::close(fds[1]);
        drop(_restore);
        use std::io::Read;
        use std::os::unix::io::FromRawFd;
        let mut file = std::fs::File::from_raw_fd(fds[0]);
        let mut out = String::new();
        file.read_to_string(&mut out).expect("read captured stderr");
        out
    }
}

fn probe_undeclared_function_addr(module: i64, holder: &str) {
    unsafe {
        let signature = rt_cranelift_new_signature(0);
        rt_cranelift_sig_set_return(signature, 4); // CL_TYPE_I64
        let ctx = rt_cranelift_begin_function(
            module,
            holder.as_ptr() as i64,
            holder.len() as i64,
            signature,
        );
        assert!(ctx > 0);
        let block = rt_cranelift_create_block(ctx);
        assert!(block > 0);
        rt_cranelift_switch_to_block(ctx, block);
        rt_cranelift_seal_block(ctx, block);
        // First probe for a cross-module function value: the miss must return
        // 0 so the caller can declare the import and retry.
        let missing = "never_declared_cross_module_fn";
        let addr = rt_cranelift_function_addr_in_func(
            ctx,
            missing.as_ptr() as i64,
            missing.len() as i64,
        );
        assert_eq!(addr, 0, "first-probe miss must return 0");
        let value = rt_cranelift_iconst(ctx, 4, 0);
        rt_cranelift_return(ctx, value);
        let function = rt_cranelift_end_function(ctx);
        assert!(function > 0);
    }
}

#[test]
fn function_addr_first_probe_miss_is_silent_jit() {
    unsafe {
        let module = rt_cranelift_new_module(
            "probe_miss_jit".as_ptr() as i64,
            "probe_miss_jit".len() as i64,
            1, // CL_TARGET_AARCH64 (host arch)
        );
        assert!(module > 0);
        let captured = capture_stderr_during(|| {
            probe_undeclared_function_addr(module, "probe_miss_jit_holder")
        });
        assert!(
            !captured.contains("function address missing declaration"),
            "recovered first-probe miss must stay silent, got stderr: {captured}"
        );
        rt_cranelift_free_module(module);
    }
}

#[test]
fn function_addr_first_probe_miss_is_silent_aot() {
    unsafe {
        let module = rt_cranelift_new_aot_module(
            "probe_miss_aot".as_ptr() as i64,
            "probe_miss_aot".len() as i64,
            1, // CL_TARGET_AARCH64 (host arch)
        );
        assert!(module > 0);
        let captured = capture_stderr_during(|| {
            probe_undeclared_function_addr(module, "probe_miss_aot_holder")
        });
        assert!(
            !captured.contains("function address missing declaration"),
            "recovered first-probe miss must stay silent, got stderr: {captured}"
        );
        rt_cranelift_free_module(module);
    }
}
