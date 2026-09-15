//! User-facing path rendering for diagnostics.
//!
//! `std::fs::canonicalize` on Windows always returns the *verbatim*
//! (extended-length) form `\\?\C:\...`. That form is an OS-internal detail: no
//! editor, IDE, or `file:line` jump-to-error parser resolves it. The compiler
//! canonicalizes module paths during resolution and then reuses the resulting
//! `PathBuf` when naming the file in a diagnostic, so the prefix leaked into
//! every Windows error message.
//!
//! Formatting such a path with `{:?}` (Debug) makes it worse: Debug escapes
//! every backslash a second time, so the user saw `\\\\?\\C:\\Users\\...`.
//!
//! `display_path` is the display boundary: it renders with `Display`
//! semantics and strips the verbatim prefix. It is deliberately *only* for
//! display — never feed its output back to the filesystem, because the
//! verbatim form is what lifts the 260-character `MAX_PATH` limit.
//!
//! See `doc/08_tracking/bug/windows_verbatim_path_prefix_leaks_into_diagnostics_2026-08-31.md`.

use std::path::Path;

/// Windows verbatim (extended-length) path prefix.
const VERBATIM_PREFIX: &str = r"\\?\";

/// Windows verbatim UNC prefix: `\\?\UNC\server\share` denotes `\\server\share`.
const VERBATIM_UNC_PREFIX: &str = r"\\?\UNC\";

/// Render a path for a human-readable diagnostic.
///
/// Strips the Windows verbatim prefix when present and uses `Display`
/// formatting so backslashes are not doubled. On non-Windows input this is
/// just `path.display().to_string()`, since the prefix cannot occur.
pub fn display_path(path: &Path) -> String {
    display_path_str(&path.display().to_string())
}

/// String-level form of [`display_path`], for call sites that already hold a
/// rendered path.
pub fn display_path_str(rendered: &str) -> String {
    if let Some(rest) = rendered.strip_prefix(VERBATIM_UNC_PREFIX) {
        // `\\?\UNC\server\share` is the verbatim spelling of `\\server\share`.
        return format!(r"\\{rest}");
    }
    if let Some(rest) = rendered.strip_prefix(VERBATIM_PREFIX) {
        return rest.to_string();
    }
    rendered.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::path::PathBuf;

    #[test]
    fn strips_windows_verbatim_drive_prefix() {
        let p = PathBuf::from(r"\\?\C:\Users\dev\hello.spl");
        assert_eq!(display_path(&p), r"C:\Users\dev\hello.spl");
    }

    #[test]
    fn strips_windows_verbatim_unc_prefix() {
        let p = PathBuf::from(r"\\?\UNC\server\share\hello.spl");
        assert_eq!(display_path(&p), r"\\server\share\hello.spl");
    }

    #[test]
    fn leaves_ordinary_paths_untouched() {
        assert_eq!(display_path(&PathBuf::from("src/lib/hello.spl")), "src/lib/hello.spl");
        assert_eq!(display_path(&PathBuf::from(r"C:\a\b.spl")), r"C:\a\b.spl");
    }

    #[test]
    fn does_not_double_escape_backslashes() {
        // The defect was `{:?}` formatting: it renders one backslash as two.
        let p = PathBuf::from(r"\\?\C:\a\b.spl");
        let rendered = display_path(&p);
        assert!(!rendered.contains(r"\\"), "display_path must not double backslashes: {rendered}");
        assert!(!rendered.contains("?"), "verbatim marker must be gone: {rendered}");
    }
}
