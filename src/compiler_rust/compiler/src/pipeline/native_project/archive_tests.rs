use super::*;

fn args(command: &Command) -> Vec<&str> {
    command.get_args().map(|arg| arg.to_str().unwrap()).collect()
}

#[test]
fn archive_command_forms_are_preserved() {
    let objects = vec![PathBuf::from("one.obj"), PathBuf::from("two.obj")];
    let create = archive_create_command("llvm-lib.exe", Path::new("out.lib"), &objects, false, true);
    assert_eq!(args(&create), ["/NOLOGO", "/OUT:out.lib", "one.obj", "two.obj"]);
    let append = archive_create_command("lib.exe", Path::new("out.lib"), &objects, true, false);
    assert_eq!(args(&append), ["/NOLOGO", "/OUT:out.lib", "out.lib", "one.obj", "two.obj"]);
    let list = archive_list_command("llvm-lib.exe", Path::new("out.lib"));
    assert_eq!(args(&list), ["/NOLOGO", "/LIST", "out.lib"]);
    let create = archive_create_command("llvm-ar", Path::new("out.a"), &objects, false, true);
    assert_eq!(args(&create), ["rcsD", "out.a", "one.obj", "two.obj"]);
    let append = archive_create_command("llvm-ar", Path::new("out.a"), &objects, true, false);
    assert_eq!(args(&append), ["rs", "out.a", "one.obj", "two.obj"]);
    assert_eq!(args(&archive_list_command("llvm-ar", Path::new("out.a"))), ["t", "out.a"]);
}

#[test]
fn response_quoting_preserves_spaces_unicode_backslashes_and_quotes() {
    let path = Path::new("C:\\objects é 한글\\a \"quoted\".obj");
    assert_eq!(quote_posix_response_path(path), "\"C:\\\\objects é 한글\\\\a \\\"quoted\\\".obj\"");
    assert_eq!(quote_windows_response_path(path), "\"C:\\objects é 한글\\a \\\"quoted\\\".obj\"");
    assert_eq!(quote_windows_response_path(Path::new("C:\\end\\")), "\"C:\\end\\\\\"");
}

#[test]
fn response_writer_rejects_line_injection_before_writing() {
    for path in ["one.obj\ntwo.obj", "one.obj\rtwo.obj"] {
        let error = write_object_response_file(Path::new("unused.rsp"), &[path.into()], false).unwrap_err();
        assert!(error.contains("unsupported newline"), "{error}");
    }
}

/// Run explicitly with ARCHIVE_TEST_LLVM_AR, ARCHIVE_TEST_LLVM_LIB,
/// ARCHIVE_TEST_COFF and ARCHIVE_TEST_ROOT. No tool absence is a passing skip.
/// The same module is compiled into the Rust bootstrap compiler and into a
/// std-only rustc --test harness; this exercises create_archive itself.
#[test]
#[cfg(windows)]
#[ignore = "requires real LLVM tools and a compiled x86_64 COFF fixture"]
fn real_llvm_archive_large_object_list_round_trip() {
    use std::os::windows::ffi::OsStrExt;
    let tool = std::env::var("ARCHIVE_TEST_LLVM_AR").expect("ARCHIVE_TEST_LLVM_AR");
    let lib = std::env::var("ARCHIVE_TEST_LLVM_LIB").expect("ARCHIVE_TEST_LLVM_LIB");
    let fixture = std::env::var_os("ARCHIVE_TEST_COFF").expect("ARCHIVE_TEST_COFF");
    let root = PathBuf::from(std::env::var_os("ARCHIVE_TEST_ROOT").expect("ARCHIVE_TEST_ROOT"));
    std::fs::create_dir(&root).expect("fresh private archive fixture directory");
    let object_dir = root.join("objects with spaces é 한글");
    std::fs::create_dir(&object_dir).unwrap();
    let original = std::fs::read(fixture).unwrap();
    assert!(original.len() > 20 && original[..2] == [0x64, 0x86], "real x86_64 COFF object required");
    let mut objects = Vec::new();
    for index in 0u32..1000 {
        let path = object_dir.join(format!("object_{index:04}.obj"));
        let mut bytes = original.clone();
        // A valid COFF timestamp distinguishes every member's bytes, detecting
        // substitution or duplication as well as truncation of the object list.
        bytes[4..8].copy_from_slice(&index.to_le_bytes());
        std::fs::write(&path, bytes).unwrap();
        objects.push(path);
    }
    let direct_chars: usize = objects.iter().map(|p| p.as_os_str().encode_wide().count() + 3).sum();
    assert!(direct_chars > 32767, "fixture must exceed the CreateProcess limit: {direct_chars}");
    let before = archive_create_command(&tool, &root.join("before.a"), &objects, false, false)
        .output().expect_err("direct invocation must reproduce the Windows command-line failure");
    assert_eq!(before.raw_os_error(), Some(206), "{before}");
    for (name, archive_tool) in [("ar", tool.as_str()), ("lib", lib.as_str())] {
        let response_dir = root.join(format!("response {name} é"));
        std::fs::create_dir(&response_dir).unwrap();
        let archive = root.join(format!("archive {name} 한글.lib"));
        let output = create_archive(archive_tool, &archive, &objects, &response_dir).unwrap();
        assert!(output.status.success(), "{name}: {}", String::from_utf8_lossy(&output.stderr));
        let response = std::fs::read_to_string(response_dir.join("archive_objects.rsp")).unwrap();
        assert_eq!(response.lines().count(), objects.len());
        let listing = archive_list_command(&tool, &archive).output().unwrap();
        assert!(listing.status.success(), "{}", String::from_utf8_lossy(&listing.stderr));
        let listing = String::from_utf8(listing.stdout).unwrap();
        let names: Vec<_> = listing.lines().collect();
        assert_eq!(names.len(), objects.len(), "{name} archive member count");
        // LLVM-lib uses full member paths and may reorder them. Compare exact
        // basename inventories, then validate every extracted member's bytes.
        let actual: std::collections::BTreeSet<_> = names.iter()
            .map(|member| Path::new(member).file_name().unwrap().to_os_string()).collect();
        let expected: std::collections::BTreeSet<_> = objects.iter()
            .map(|object| object.file_name().unwrap().to_os_string()).collect();
        assert_eq!(actual, expected, "{name} member inventory");
        let extract = root.join(format!("extract {name}"));
        std::fs::create_dir(&extract).unwrap();
        let output = Command::new(&tool).arg("x").arg(&archive).current_dir(&extract).output().unwrap();
        assert!(output.status.success(), "{}", String::from_utf8_lossy(&output.stderr));
        for object in &objects {
            assert_eq!(std::fs::read(extract.join(object.file_name().unwrap())).unwrap(),
                std::fs::read(object).unwrap(), "member bytes: {}", object.display());
        }
        println!("PASS {name}: {} members, {} direct argv UTF-16 units, all COFF member bytes verified", objects.len(), direct_chars);
    }
}
