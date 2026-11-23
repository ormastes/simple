//! COFF relocatable links require GNU PE BFD: PE LLD does not implement `-r`.
//! This selection applies only to the intermediate closure, never the final PE.

use std::process::Command;

pub(crate) fn command(arch: &str) -> Result<Command, String> {
    let (qualified, emulation) = match arch {
        "x86_64" => ("x86_64-w64-mingw32-ld", "i386pep"),
        "i686" => ("i686-w64-mingw32-ld", "i386pe"),
        _ => return Err(format!("COFF partial link has no GNU PE emulation for {arch}")),
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
        return Ok(command);
    }
    Err(format!("COFF partial link requires GNU PE BFD `{qualified}` supporting {emulation}; final Clang/LLD selection is unchanged"))
}

#[cfg(test)]
mod tests {
    #[test]
    fn unsupported_machine_fails_closed() {
        assert!(super::command("aarch64").unwrap_err().contains("no GNU PE emulation"));
    }
}
