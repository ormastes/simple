//! Keep compile-only ambient MSVC options out of archive linking.

/// Remove the global force-C switch, not per-file `/Tc...` options or text
/// inside a quoted define/path. Preserve every other byte of the option list.
fn link_cl_options(cl: &str) -> String {
    let mut result = String::with_capacity(cl.len());
    let mut start = 0;
    let mut quoted = false;
    let mut backslashes = 0;
    for (index, character) in cl.char_indices() {
        if character == '"' && backslashes % 2 == 0 {
            quoted = !quoted;
        }
        if character.is_ascii_whitespace() && !quoted {
            let token = &cl[start..index];
            if token != "/TC" && token != "\"/TC\"" {
                result.push_str(token);
            }
            result.push(character);
            start = index + character.len_utf8();
        }
        backslashes = if character == '\\' { backslashes + 1 } else { 0 };
    }
    let token = &cl[start..];
    if token != "/TC" && token != "\"/TC\"" {
        result.push_str(token);
    }
    result
}

pub(super) fn configure_msvc_link_cl(command: &mut std::process::Command, cl: &str) {
    let options = link_cl_options(cl);
    if options != cl {
        command.env("CL", options);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn link_child_removes_only_global_force_c() {
        let mut link = std::process::Command::new("clang-cl");
        link.args(["main.obj", "hosted.rlib", "/Fe:probe.exe"]);
        configure_msvc_link_cl(&mut link, "/nologo /TC /DKEEP=1");
        let (key, value) = link.get_envs().next().unwrap();
        assert_eq!(key, "CL");
        assert_eq!(value.unwrap(), "/nologo  /DKEEP=1");
        assert_eq!(link.get_args().collect::<Vec<_>>(), ["main.obj", "hosted.rlib", "/Fe:probe.exe"]);

        // The compile command never calls the link-only helper.
        let mut compile = std::process::Command::new("clang-cl");
        compile.args(["/c", "source.c"]).env("CL", "/nologo /TC /DKEEP=1");
        assert_eq!(compile.get_envs().next().unwrap().1.unwrap(), "/nologo /TC /DKEEP=1");
    }

    #[test]
    fn quoted_values_and_per_file_flags_are_unchanged() {
        assert_eq!(link_cl_options("/TC"), "");
        assert_eq!(link_cl_options("\"/TC\"\t/TC"), "\t");
        for unchanged in [
            r#"/DNOTE="keep /TC text" /Tcsource.c /TP"#,
            r#"/I"C:\two  spaces\include" /DNOTE="say \"/TC\" now""#,
            "/DUNICODE=한글 /nologo",
        ] {
            assert_eq!(link_cl_options(unchanged), unchanged);
        }
    }
}
