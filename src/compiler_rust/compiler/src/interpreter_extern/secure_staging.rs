//! Interpreter extern handlers for the secure-staging runtime pair.
//!
//! `rt_secure_temp_dir` and `rt_file_publish_noreplace` are implemented once,
//! in C (`src/runtime/runtime_secure_staging.c`), and were known to the seed's
//! CODEGEN (`codegen/runtime_sffi.rs`) but not to the seed INTERPRETER: calling
//! either from an interpreted program failed with
//! `semantic: unknown extern function: rt_secure_temp_dir`. That is the gap
//! `scripts/check/check-interpreter-extern-registry-gap.shs` exists to fence,
//! and it fired on both symbols
//! (declared at `src/compiler/70.backend/backend/llvm_backend_tools.spl:27-28`
//! and `src/lib/nogc_sync_mut/io/file_ops.spl:45,47`).
//!
//! These handlers do NOT reimplement the contract in Rust; they call the same C
//! objects the native lane calls. `runtime_secure_staging.c` is compiled into
//! the `simple_runtime` crate by `src/compiler_rust/runtime/build.rs`, so the
//! symbols are already in the seed binary and a Rust twin would be a second
//! implementation to keep in sync — and, worse, a place for the interpreter and
//! the native lane to disagree about a security-relevant contract (0700
//! mkdtemp; link-based no-replace publish).
//!
//! Why the return shapes matter, and why `Value::Nil` is never produced here:
//! per `doc/08_tracking/bug/unregistered_extern_silent_nil_2026-08-01.md`, an
//! extern that is not registered can silently evaluate to nil rather than
//! failing. Every caller of these two tests the C sentinels
//! (`llvm_backend_tools.spl:300`, `file_ops.spl:139`,
//! `backend_plugin/dynamic_loader.spl:62`) — `""` for a failed temp dir, and
//! `1` published / `0` destination exists / `-1` error for the publish. A nil
//! would compare unequal to `""` and take the SUCCESS branch, which is worse
//! than the loud unknown-extern error this replaces. So the failure paths below
//! return exactly the C sentinels.

use crate::error::CompileError;
use crate::value::Value;
use simple_runtime::RuntimeValue;

// `runtime_secure_staging.c`. The C returns the owned string as an `int64_t`
// handle; it is declared here as `RuntimeValue`, which is
// `#[repr(transparent)]` over `u64` (`runtime/src/value/core.rs:42-44`) and so
// is the same ABI. Going through the type rather than a bare i64 is what lets
// the crate's own `rt_string_*` accessors be used below instead of a second
// set of raw declarations, which would clash with the ones in `package.rs`
// (`clashing_extern_declarations`).
unsafe extern "C" {
    #[link_name = "rt_secure_temp_dir"]
    fn c_rt_secure_temp_dir(
        parent_ptr: *const u8,
        parent_len: u64,
        prefix_ptr: *const u8,
        prefix_len: u64,
    ) -> RuntimeValue;

    #[link_name = "rt_file_publish_noreplace"]
    fn c_rt_file_publish_noreplace(
        staged_ptr: *const u8,
        staged_len: u64,
        destination_ptr: *const u8,
        destination_len: u64,
    ) -> i64;
}

fn text_arg(args: &[Value], index: usize, symbol: &str) -> Result<String, CompileError> {
    match args.get(index) {
        Some(Value::Str(s)) => Ok(s.as_ref().clone()),
        _ => Err(CompileError::runtime(format!(
            "{symbol}: argument {index} must be text"
        ))),
    }
}

/// Copy an owned runtime string handle out into a `Value::text`, then free it.
///
/// A zero or negative length is the C failure sentinel (`rt_string_new(NULL, 0)`)
/// and yields `""` — never nil, see the module comment.
fn owned_text_out(handle: RuntimeValue) -> Value {
    let len = simple_runtime::value::rt_string_len(handle);
    if len <= 0 {
        let _ = simple_runtime::value::rt_string_free(handle);
        return Value::text(String::new());
    }
    let data = simple_runtime::value::rt_string_data(handle);
    if data.is_null() {
        let _ = simple_runtime::value::rt_string_free(handle);
        return Value::text(String::new());
    }
    let bytes = unsafe { std::slice::from_raw_parts(data, len as usize) };
    let out = String::from_utf8_lossy(bytes).into_owned();
    let _ = simple_runtime::value::rt_string_free(handle);
    Value::text(out)
}

/// `rt_secure_temp_dir(parent: text, prefix: text) -> text`
///
/// Creates a 0700 directory `<parent>/<prefix>-XXXXXX` via `mkdtemp` (a
/// bcrypt-random name with an owner-only ACL on Windows) and returns its path.
/// Returns `""` on any failure, including a `prefix` containing a path
/// separator — the rejection is the C function's, not this wrapper's.
pub fn rt_secure_temp_dir(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_secure_temp_dir";
    let parent = text_arg(args, 0, NAME)?;
    let prefix = text_arg(args, 1, NAME)?;
    let handle = unsafe {
        c_rt_secure_temp_dir(
            parent.as_ptr(),
            parent.len() as u64,
            prefix.as_ptr(),
            prefix.len() as u64,
        )
    };
    Ok(owned_text_out(handle))
}

/// `rt_file_publish_noreplace(staged_path: text, destination: text) -> i64`
///
/// Publishes `staged_path` to `destination` without ever replacing an existing
/// destination (`renameat2(RENAME_NOREPLACE)`, falling back to `link` +
/// `unlink`). Returns `1` published, `0` destination already existed, `-1`
/// error — the C sentinels, unchanged.
pub fn rt_file_publish_noreplace(args: &[Value]) -> Result<Value, CompileError> {
    const NAME: &str = "rt_file_publish_noreplace";
    let staged = text_arg(args, 0, NAME)?;
    let destination = text_arg(args, 1, NAME)?;
    let rc = unsafe {
        c_rt_file_publish_noreplace(
            staged.as_ptr(),
            staged.len() as u64,
            destination.as_ptr(),
            destination.len() as u64,
        )
    };
    Ok(Value::Int(rc))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn text(s: &str) -> Value {
        Value::text(s.to_string())
    }

    fn as_text(v: &Value) -> String {
        match v {
            Value::Str(s) => s.as_ref().clone(),
            other => panic!("expected text, got {other:?}"),
        }
    }

    // Registration must make the symbol WORK, not merely resolve: a handler
    // that returned nil (or a path that was never created) would satisfy the
    // registry gate and still break every caller.
    #[test]
    fn secure_temp_dir_creates_a_private_directory_under_the_parent() {
        let parent = std::env::temp_dir().join("spl-secure-staging-test");
        std::fs::create_dir_all(&parent).unwrap();
        let parent_text = parent.to_string_lossy().to_string();

        let value =
            rt_secure_temp_dir(&[text(&parent_text), text("probe")]).expect("handler errored");
        let path = as_text(&value);

        assert!(!path.is_empty(), "returned the failure sentinel");
        assert!(std::path::Path::new(&path).is_dir(), "{path} is not a directory");
        assert!(path.starts_with(&parent_text), "{path} escaped {parent_text}");
        assert!(
            std::path::Path::new(&path)
                .file_name()
                .unwrap()
                .to_string_lossy()
                .starts_with("probe-"),
            "{path} does not carry the requested prefix"
        );
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let mode = std::fs::metadata(&path).unwrap().permissions().mode() & 0o777;
            assert_eq!(mode, 0o700, "expected owner-only 0700, got {mode:o}");
        }
        std::fs::remove_dir_all(&path).ok();
    }

    #[test]
    fn secure_temp_dir_returns_empty_text_not_nil_on_failure() {
        // A prefix containing a separator is rejected by the C function, and an
        // absent parent cannot be mkdtemp'd. Both must be `""`, because every
        // caller tests `== ""`.
        for args in [
            [text("/nonexistent-spl-parent-dir"), text("probe")],
            [text("/tmp"), text("bad/prefix")],
        ] {
            let value = rt_secure_temp_dir(&args).expect("handler errored");
            assert!(
                matches!(value, Value::Str(_)),
                "failure produced {value:?}, not text — a nil here would take the success branch"
            );
            assert_eq!(as_text(&value), "");
        }
    }

    #[test]
    fn publish_noreplace_publishes_once_and_then_reports_the_existing_destination() {
        let dir = std::env::temp_dir().join(format!(
            "spl-publish-test-{}",
            std::process::id()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        let staged = dir.join("staged");
        let destination = dir.join("published");
        std::fs::write(&staged, b"payload").unwrap();

        let first = rt_file_publish_noreplace(&[
            text(&staged.to_string_lossy()),
            text(&destination.to_string_lossy()),
        ])
        .expect("handler errored");
        assert_eq!(first, Value::Int(1), "first publish should report 1");
        assert_eq!(std::fs::read(&destination).unwrap(), b"payload");

        std::fs::write(&staged, b"second").unwrap();
        let second = rt_file_publish_noreplace(&[
            text(&staged.to_string_lossy()),
            text(&destination.to_string_lossy()),
        ])
        .expect("handler errored");
        assert_eq!(
            second,
            Value::Int(0),
            "an existing destination must report 0 and must NOT be replaced"
        );
        assert_eq!(
            std::fs::read(&destination).unwrap(),
            b"payload",
            "no-replace was violated"
        );

        std::fs::remove_dir_all(&dir).ok();
    }

    #[test]
    fn publish_noreplace_reports_minus_one_for_a_missing_source() {
        let value = rt_file_publish_noreplace(&[
            text("/nonexistent-spl-staged-file"),
            text("/tmp/spl-publish-unreachable"),
        ])
        .expect("handler errored");
        assert_eq!(value, Value::Int(-1));
    }

    #[test]
    fn non_text_arguments_error_rather_than_returning_a_sentinel() {
        assert!(rt_secure_temp_dir(&[Value::Int(1), text("p")]).is_err());
        assert!(rt_file_publish_noreplace(&[text("a"), Value::Int(2)]).is_err());
    }
}
