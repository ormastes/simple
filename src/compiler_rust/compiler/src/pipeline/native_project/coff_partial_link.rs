//! COFF relocatable links require GNU PE BFD: PE LLD does not implement `-r`.
//! This selection applies only to the intermediate closure, never the final PE.

use std::process::Command;

/// Resolve GNU tools past LLVM-MinGW compatibility aliases earlier on PATH.
pub(crate) fn gnu_tool(names: &[&str], kind: &str) -> Option<String> {
    let path = std::env::var_os("PATH")?;
    for name in names {
        for directory in std::env::split_paths(&path) {
            let candidate = directory.join(if cfg!(windows) { format!("{name}.exe") } else { name.to_string() });
            let Ok(version) = Command::new(&candidate).arg("--version").output() else { continue };
            if version.status.success() && is_gnu_banner(&String::from_utf8_lossy(&version.stdout), kind) {
                return Some(candidate.to_string_lossy().into_owned());
            }
        }
    }
    None
}

fn is_gnu_banner(banner: &str, kind: &str) -> bool {
    banner.starts_with(&format!("GNU {kind} "))
}

pub(crate) fn command(windows_gnu: bool, arch: &str) -> Result<Option<Command>, String> {
    if !windows_gnu {
        return Ok(None);
    }
    let (qualified, emulation) = match arch {
        "x86_64" => ("x86_64-w64-mingw32-ld", "i386pep"),
        "i686" => ("i686-w64-mingw32-ld", "i386pe"),
        // Other Windows GNU architectures retain their existing linker path.
        _ => return Ok(None),
    };
    for program in [qualified, "ld"] {
        let Ok(version) = Command::new(program).arg("--version").output() else { continue };
        if !version.status.success() || !String::from_utf8_lossy(&version.stdout).contains("GNU ld") {
            continue;
        }
        let Ok(formats) = Command::new(program).arg("-V").output() else { continue };
        let output = format!("{}\n{}", String::from_utf8_lossy(&formats.stdout), String::from_utf8_lossy(&formats.stderr));
        if !formats.status.success() || !output.split_whitespace().any(|word| word == emulation) {
            continue;
        }
        let mut command = Command::new(program);
        command.args(["-m", emulation, "-r"]);
        return Ok(Some(command));
    }
    Err(format!("COFF partial link requires GNU PE BFD `{qualified}` supporting {emulation}; final Clang/LLD selection is unchanged"))
}

#[cfg(test)]
mod tests {
    #[test]
    fn compatibility_banners_are_not_gnu_tools() {
        assert!(super::is_gnu_banner("GNU objcopy (GNU Binutils) 2.42", "objcopy"));
        assert!(super::is_gnu_banner("GNU nm (GNU Binutils) 2.42", "nm"));
        assert!(!super::is_gnu_banner("llvm-objcopy, compatible with GNU objcopy\nLLVM version 23", "objcopy"));
        assert!(!super::is_gnu_banner("llvm-nm, compatible with GNU nm\nLLVM version 23", "nm"));
    }
    #[test]
    fn out_of_scope_targets_keep_existing_path() {
        assert!(super::command(true, "aarch64").unwrap().is_none());
        assert!(super::command(false, "x86_64").unwrap().is_none());
    }
}
