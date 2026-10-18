//! Native archive commands and object response files. Kept std-only so the
//! bootstrap archive boundary can be tested with real LLVM tools in isolation.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

fn is_msvc_archive_tool(tool: &str) -> bool {
    Path::new(tool)
        .file_stem()
        .and_then(|stem| stem.to_str())
        .is_some_and(|stem| stem.eq_ignore_ascii_case("lib") || stem.eq_ignore_ascii_case("llvm-lib"))
}

pub(super) fn archive_create_command(
    tool: &str,
    archive: &Path,
    objects: &[PathBuf],
    append: bool,
    deterministic: bool,
) -> Command {
    let mut command = Command::new(tool);
    if is_msvc_archive_tool(tool) {
        command.arg("/NOLOGO").arg(format!("/OUT:{}", archive.display()));
        if append {
            command.arg(archive);
        }
    } else {
        let mode = match (append, deterministic) {
            (false, false) => "rcs",
            (true, false) => "rs",
            (false, true) => "rcsD",
            (true, true) => "rsD",
        };
        command.arg(mode).arg(archive);
    }
    command.args(objects);
    command
}

pub(super) fn archive_list_command(tool: &str, archive: &Path) -> Command {
    let mut command = Command::new(tool);
    if is_msvc_archive_tool(tool) {
        command.arg("/NOLOGO").arg("/LIST").arg(archive);
    } else {
        command.arg("t").arg(archive);
    }
    command
}

// Shared with executable-link response files. This is LLVM's POSIX response
// syntax, not shell interpolation: no shell executes the contents.
pub(super) fn quote_posix_response_path(path: &Path) -> String {
    let raw = path.to_string_lossy();
    debug_assert!(!raw.contains(['\n', '\r']));
    let escaped = raw.replace('\\', "\\\\").replace('"', "\\\"");
    format!("\"{escaped}\"")
}

fn quote_windows_response_path(path: &Path) -> String {
    let mut quoted = String::from("\"");
    let mut backslashes = 0;
    for ch in path.to_string_lossy().chars() {
        if ch == '\\' {
            backslashes += 1;
            continue;
        }
        // Backslashes are literal except before a quote (including the closing
        // quote), where Windows response parsing consumes pairs as one slash.
        quoted.extend(std::iter::repeat_n('\\', if ch == '"' { backslashes * 2 + 1 } else { backslashes }));
        quoted.push(ch);
        backslashes = 0;
    }
    quoted.extend(std::iter::repeat_n('\\', backslashes * 2));
    quoted.push('"');
    quoted
}

pub(super) fn write_object_response_file(
    response: &Path,
    objects: &[PathBuf],
    windows_quoting: bool,
) -> Result<(), String> {
    let mut quoted = Vec::with_capacity(objects.len());
    for object in objects {
        if object.to_string_lossy().contains(['\n', '\r']) {
            return Err(format!("object path contains unsupported newline: {}", object.display()));
        }
        quoted.push(if windows_quoting {
            quote_windows_response_path(object)
        } else {
            quote_posix_response_path(object)
        });
    }
    std::fs::write(response, format!("{}\n", quoted.join("\n")))
        .map_err(|e| format!("write object response file: {e}"))
}

/// The response directory belongs to this invocation and must outlive the
/// child. The caller owns cleanup, including errors. Executable-link batching
/// continues to use archive_create_command unchanged.
pub(super) fn create_archive(
    tool: &str,
    archive: &Path,
    objects: &[PathBuf],
    response_dir: &Path,
) -> Result<Output, String> {
    #[cfg(windows)]
    let mut command = {
        let response = response_dir.join("archive_objects.rsp");
        let msvc = is_msvc_archive_tool(tool);
        write_object_response_file(&response, objects, msvc)?;
        let mut command = archive_create_command(tool, archive, &[], false, false);
        // llvm-ar defaults to Windows quoting on Windows. Pin POSIX explicitly
        // to reuse the executable linker's established quoting implementation.
        if !msvc {
            command.arg("--rsp-quoting=posix");
        }
        command.arg(format!("@{}", response.display()));
        command
    };
    #[cfg(not(windows))]
    let mut command = {
        let _ = response_dir;
        archive_create_command(tool, archive, objects, false, false)
    };
    command.output().map_err(|e| format!("run archive tool {tool}: {e}"))
}

#[cfg(test)]
#[path = "archive_tests.rs"]
mod tests;
