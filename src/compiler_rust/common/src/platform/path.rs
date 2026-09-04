//! Cross-platform path manipulation utilities for the compiler.

use std::path::{Path, PathBuf};

/// Join two path segments.
pub fn join(base: impl AsRef<Path>, part: impl AsRef<Path>) -> PathBuf {
    base.as_ref().join(part)
}

/// Get the absolute path — avoids libc::realpath which segfaults in
/// self-hosted Cranelift binaries.
pub fn absolute(path: impl AsRef<Path>) -> std::io::Result<PathBuf> {
    let p = path.as_ref();
    let abs = if p.is_absolute() {
        p.to_path_buf()
    } else {
        std::env::current_dir()?.join(p)
    };
    let mut out = PathBuf::new();
    for comp in abs.components() {
        match comp {
            std::path::Component::ParentDir => {
                out.pop();
            }
            std::path::Component::CurDir => {}
            c => out.push(c),
        }
    }
    Ok(out)
}

/// Get the parent directory.
pub fn parent(path: impl AsRef<Path>) -> Option<PathBuf> {
    path.as_ref().parent().map(|p| p.to_path_buf())
}

/// Get the file extension (without the dot).
pub fn extension(path: impl AsRef<Path>) -> Option<String> {
    path.as_ref()
        .extension()
        .and_then(|e| e.to_str())
        .map(|s| s.to_string())
}

/// Get the file name (last component).
pub fn file_name(path: impl AsRef<Path>) -> Option<String> {
    path.as_ref()
        .file_name()
        .and_then(|n| n.to_str())
        .map(|s| s.to_string())
}

/// Get the file stem (name without extension).
pub fn stem(path: impl AsRef<Path>) -> Option<String> {
    path.as_ref()
        .file_stem()
        .and_then(|n| n.to_str())
        .map(|s| s.to_string())
}

/// Get the platform-appropriate path separator.
pub fn separator() -> char {
    std::path::MAIN_SEPARATOR
}

// ---------------------------------------------------------------------------
// Canonical-internal -> native-argument conversion.
//
// The compiler's canonical internal path form is MinGW/MSYS style: forward
// slashes with a `/<drive>/` prefix (`/c/Users/x`, `/d/foo/bar`). On Unix that
// form IS the native form, so conversion must be a no-op and must cost
// nothing. On Windows a native tool (clang-cl, link.exe, cmd.exe) rejects it
// and needs `d:\foo\bar`.
//
// The Unix/Windows split is done with `#[cfg]`, NOT a runtime `cfg!(windows)`
// branch, so the non-Windows build contains no scanning code at all: the
// function below is a borrow-only identity that inlines away.
//
// Conversion belongs at the spawn / argv / native-API BOUNDARY only. Do not
// apply it to paths held internally: backslash is a legal POSIX filename
// character, so converting everywhere would corrupt real Unix paths.
// ---------------------------------------------------------------------------

/// Convert a canonical internal (MinGW/MSYS-style) path into the form the
/// host's native tools accept.
///
/// On Unix this is the identity: the canonical form is already native, the
/// input is returned borrowed, and nothing is allocated or scanned.
///
/// On Windows:
/// - `/d/foo/bar` becomes `d:\foo\bar` (drive-prefix form)
/// - `/c` becomes `c:\`
/// - `c:/Users/x` becomes `c:\Users\x` (mixed separators normalized)
/// - relative paths, UNC, verbatim and already-native paths are returned
///   unchanged (idempotent).
#[cfg(not(windows))]
#[inline(always)]
pub fn to_native_arg(path: &str) -> std::borrow::Cow<'_, str> {
    std::borrow::Cow::Borrowed(path)
}

/// Windows implementation. See the `#[cfg(not(windows))]` twin for contract.
#[cfg(windows)]
pub fn to_native_arg(path: &str) -> std::borrow::Cow<'_, str> {
    const BS: char = '\u{5c}';
    let b = path.as_bytes();
    let is_sep = |c: u8| c == b'\\' || c == b'/';

    // UNC and verbatim paths are left strictly alone: rewriting their leading
    // separators breaks them.
    if b.len() >= 2 && is_sep(b[0]) && is_sep(b[1]) {
        return std::borrow::Cow::Borrowed(path);
    }

    // MSYS drive form: `/<letter>` optionally followed by `/` + remainder.
    // Must be `/x` exactly or `/x/...` — `/usr` and `/tmp/f` are not drives.
    let msys_drive = if b.len() >= 2
        && b[0] == b'/'
        && b[1].is_ascii_alphabetic()
        && (b.len() == 2 || b[2] == b'/')
    {
        Some(b[1] as char)
    } else {
        None
    };

    if let Some(drive) = msys_drive {
        let mut out = String::with_capacity(path.len() + 1);
        out.push(drive);
        out.push(':');
        if b.len() == 2 {
            out.push(BS);
        } else {
            for ch in path[2..].chars() {
                out.push(if ch == '/' { BS } else { ch });
            }
        }
        return std::borrow::Cow::Owned(out);
    }

    // Native drive form with forward or mixed separators: `c:/x`, `C:/a\b`.
    // Normalize so a single path never mixes separators.
    if b.len() >= 2 && b[0].is_ascii_alphabetic() && b[1] == b':' {
        if path[2..].contains('/') {
            let mut out = String::with_capacity(path.len());
            out.push_str(&path[..2]);
            for ch in path[2..].chars() {
                out.push(if ch == '/' { BS } else { ch });
            }
            return std::borrow::Cow::Owned(out);
        }
        return std::borrow::Cow::Borrowed(path);
    }

    // Relative paths and non-drive absolute paths (`/usr/lib`) are left as-is:
    // there is no drive to infer, and guessing one would be wrong.
    std::borrow::Cow::Borrowed(path)
}

/// Owned-in, owned-out variant for call sites that already hold a `String`
/// (env-var reads, for example).
///
/// This exists so such call sites cost NOTHING on Unix. Writing
/// `to_native_arg(&s).into_owned()` would allocate a fresh `String` and
/// memcpy on every call even though the Unix conversion is the identity —
/// the `to_owned()` clone survives inlining even after the conversion body
/// itself is optimized away. Here the Unix build simply moves the `String`
/// straight back out.
#[cfg(not(windows))]
#[inline(always)]
pub fn to_native_owned(s: String) -> String {
    s
}

/// Windows implementation. See the `#[cfg(not(windows))]` twin for contract.
#[cfg(windows)]
pub fn to_native_owned(s: String) -> String {
    // Two steps so the borrow of `s` ends before `s` is moved out.
    let converted = match to_native_arg(&s) {
        std::borrow::Cow::Borrowed(_) => None,
        std::borrow::Cow::Owned(o) => Some(o),
    };
    match converted {
        Some(o) => o,
        None => s,
    }
}

/// `Path`-flavoured convenience over [`to_native_arg`].
///
/// On Unix this borrows the input unchanged and allocates nothing.
#[cfg(not(windows))]
#[inline(always)]
pub fn to_native_path(path: &Path) -> std::borrow::Cow<'_, Path> {
    std::borrow::Cow::Borrowed(path)
}

/// Windows implementation. See the `#[cfg(not(windows))]` twin for contract.
#[cfg(windows)]
pub fn to_native_path(path: &Path) -> std::borrow::Cow<'_, Path> {
    match path.to_str() {
        Some(s) => match to_native_arg(s) {
            std::borrow::Cow::Borrowed(_) => std::borrow::Cow::Borrowed(path),
            std::borrow::Cow::Owned(o) => std::borrow::Cow::Owned(PathBuf::from(o)),
        },
        // Non-UTF-8 paths cannot be in the MSYS drive form we recognize.
        None => std::borrow::Cow::Borrowed(path),
    }
}

#[cfg(test)]
mod native_arg_tests {
    use super::*;

    // ---- Generalizing tests: pure string contract, every platform. ----

    #[test]
    fn relative_paths_are_untouched_on_every_platform() {
        for p in ["foo/bar.c", "./x", "../y/z", "bin/x.cmd", "a"] {
            assert_eq!(to_native_arg(p), p, "relative path must not be rewritten");
        }
    }

    #[test]
    fn empty_and_short_inputs_do_not_panic() {
        for p in ["", "/", "a", "/a", "c:"] {
            let _ = to_native_arg(p);
        }
    }

    #[test]
    fn conversion_is_idempotent() {
        let native_ab = format!("d:{0}a{0}b", '\u{5c}');
        let cases = ["/d/foo/bar", "/c/Users/x", "c:/Users/x", &native_ab, "rel/x"];
        for p in cases {
            let once = to_native_arg(p).into_owned();
            let twice = to_native_arg(&once).into_owned();
            assert_eq!(once, twice, "to_native_arg must be idempotent for {p:?}");
        }
    }

    #[cfg(not(windows))]
    #[test]
    fn unix_is_byte_identical_identity_including_backslashes() {
        // Backslash is a legal POSIX filename character. A Unix build must
        // never touch it, and must never reinterpret `/d/...` as a drive.
        let bs = '\u{5c}';
        let weird = format!("/home/u/weird{bs}name");
        let backslashed = format!("back{bs}slash");
        let cases = [
            "/d/foo/bar",
            "/c/Users/x",
            weird.as_str(),
            backslashed.as_str(),
            "c:/not/a/windows/host",
            "",
        ];
        for p in cases {
            let out = to_native_arg(p);
            assert_eq!(out, p, "unix conversion must be byte-identical");
            assert!(
                matches!(out, std::borrow::Cow::Borrowed(_)),
                "unix conversion must borrow, never allocate"
            );
        }
    }

    #[cfg(windows)]
    #[test]
    fn windows_converts_msys_drive_form() {
        let bs = '\u{5c}';
        assert_eq!(to_native_arg("/d/foo/bar"), format!("d:{bs}foo{bs}bar"));
        assert_eq!(to_native_arg("/c/Users/x"), format!("c:{bs}Users{bs}x"));
        assert_eq!(to_native_arg("/D/Foo"), format!("D:{bs}Foo"));
        assert_eq!(to_native_arg("/c"), format!("c:{bs}"));
        assert_eq!(to_native_arg("/d/foo/"), format!("d:{bs}foo{bs}"));
    }

    #[cfg(windows)]
    #[test]
    fn windows_normalizes_mixed_separators() {
        // The defect that made check-core-lib-purity count files as both new
        // and stale: a path mixing `C:/...` with backslash segments.
        let bs = '\u{5c}';
        let mixed = format!("C:/a{bs}b/c");
        assert_eq!(to_native_arg(&mixed), format!("C:{bs}a{bs}b{bs}c"));
        assert_eq!(to_native_arg("c:/Users/x"), format!("c:{bs}Users{bs}x"));
        // Already native: borrowed, unchanged.
        let native = format!("d:{bs}a{bs}b");
        let out = to_native_arg(&native);
        assert_eq!(out, native);
        assert!(matches!(out, std::borrow::Cow::Borrowed(_)));
    }

    #[cfg(windows)]
    #[test]
    fn windows_leaves_non_drive_and_unc_alone() {
        let bs = '\u{5c}';
        // `/usr/...` has no drive to infer; a multi-char segment is not a drive.
        assert_eq!(to_native_arg("/usr/lib/x"), "/usr/lib/x");
        assert_eq!(to_native_arg("/dev/null"), "/dev/null");
        // UNC and verbatim must not be rewritten.
        let unc = format!("{bs}{bs}server{bs}share");
        assert_eq!(to_native_arg(&unc), unc);
        let verbatim = format!("{bs}{bs}?{bs}C:{bs}x");
        assert_eq!(to_native_arg(&verbatim), verbatim);
    }

    /// Reproducing test: a native Windows tool REJECTS the canonical MSYS form
    /// and ACCEPTS the converted form. `cmd.exe` is used rather than clang-cl
    /// because it is always present on a Windows host.
    #[cfg(windows)]
    #[test]
    fn native_tool_rejects_msys_form_and_accepts_converted() {
        use std::process::Command;

        let dir = std::env::temp_dir().join("simple_to_native_arg_test");
        let _ = std::fs::create_dir_all(&dir);
        let file = dir.join("probe.txt");
        std::fs::write(&file, b"ok").expect("write probe");

        let native = file.to_str().unwrap().to_string();
        assert_eq!(native.as_bytes()[1], b':', "temp dir must be drive-rooted");
        // Build the canonical MSYS form from the native one.
        let drive = native.as_bytes()[0] as char;
        let msys = format!("/{}{}", drive, native[2..].replace('\u{5c}', "/"));

        // Unconverted: cmd.exe cannot resolve the MSYS form.
        let bad = Command::new("cmd")
            .args(["/C", "type", &msys])
            .output()
            .expect("spawn cmd");
        let bad_rc = bad.status.code().unwrap_or(-1);

        // Converted through the single conversion home.
        let good_path = to_native_arg(&msys).into_owned();
        let good = Command::new("cmd")
            .args(["/C", "type", &good_path])
            .output()
            .expect("spawn cmd");
        let good_rc = good.status.code().unwrap_or(-1);

        let _ = std::fs::remove_dir_all(&dir);

        assert_eq!(good_path, native, "conversion must reproduce the native form");
        assert_eq!(
            good_rc,
            0,
            "converted path must be accepted (stderr: {})",
            String::from_utf8_lossy(&good.stderr)
        );
        assert_ne!(bad_rc, 0, "unconverted MSYS path must be rejected");
    }
}
