#!/usr/bin/env python3
"""Compile and exercise the production runtime flag owners without rebuilding a seed."""
import argparse
import pathlib
import subprocess
import tempfile


def function(source, name):
    start = source.index(f"fn {name}(")
    opening = source.index("{", start)
    depth = 1
    end = opening + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cc", required=True, help="Pinned clang-cl executable")
    parser.add_argument("--linker", required=True, help="Pinned lld-link executable")
    args = parser.parse_args()
    root = pathlib.Path(__file__).resolve().parents[2]
    source = (root / "src/compiler_rust/compiler/src/pipeline/native_project/tools.rs").read_text()
    # Both core-C compile paths must consume the helpers exercised below.
    assert source.count("command.args(core_c_codegen_flags(&cc));") == 2
    assert source.count("let msvc = msvc_style_c_driver(&cc);") == 2
    runtime_command = source[source.index("command.args(core_c_codegen_flags(&cc));"):]
    runtime_command = runtime_command[:runtime_command.index(".args(msvc_c11_atomics_flags(&cc))")]
    assert "if let Some(define) = piped_observer.c_define()" in runtime_command
    assert "command.arg(define);" in runtime_command
    assert 'if no_rust_array_packing' in runtime_command
    assert 'command.arg("-DSIMPLE_RUNTIME_NO_RUST_ARRAY_PACKING=1");' in runtime_command
    owners = "\n".join(function(source, name) for name in (
        "msvc_style_c_driver", "core_c_codegen_flags", "msvc_c11_atomics_flags"))
    program = owners + r'''
fn main() {
    for cc in ["cl", "CL.EXE", "clang-cl", "CLANG-CL.EXE", "C:\\SDK tools\\clang-cl.exe", "/sdk/clang-cl"] {
        assert!(msvc_style_c_driver(cc), "{cc}");
        assert_eq!(core_c_codegen_flags(cc), ["-c", "-O1", "-Gy", "-Gw", "-GS-"]);
    }
    for cc in ["clang", "clang.exe", "clang++", "gcc", "/sdk/clang"] {
        assert!(!msvc_style_c_driver(cc), "{cc}");
        assert_eq!(msvc_c11_atomics_flags(cc), [] as [&str; 0]);
        assert!(core_c_codegen_flags(cc).contains(&"-std=gnu11"));
        assert!(core_c_codegen_flags(cc).contains(&"-fPIC"));
    }
    assert_eq!(msvc_c11_atomics_flags("cl.exe"), ["-std:c11", "-experimental:c11atomics"]);
    assert_eq!(msvc_c11_atomics_flags("CLANG-CL.EXE"), ["-std:c11"]);
    let a: Vec<String> = std::env::args().collect();
    let output = std::process::Command::new(&a[1])
        .args(core_c_codegen_flags(&a[1])).args(msvc_c11_atomics_flags(&a[1]))
        .arg("/WX").arg(format!("/Fo{}", a[3])).arg(&a[2]).output().unwrap();
    assert!(output.status.success(), "{}{}", String::from_utf8_lossy(&output.stdout), String::from_utf8_lossy(&output.stderr));
    assert!(std::fs::metadata(&a[3]).unwrap().len() > 0);
    println!("PASS: driver selection, C11 atomics and real clang-cl /WX object compilation");
}
'''
    with tempfile.TemporaryDirectory(prefix="msvc-driver-flags-") as temporary:
        work = pathlib.Path(temporary)
        rust = work / "probe.rs"
        rust.write_text(program)
        binary = work / "probe.exe"
        subprocess.run(["rustc", "--edition=2021", "-Dwarnings", str(rust), "-C", f"linker={args.linker}", "-o", str(binary)], check=True)
        c = work / "probe.c"
        c.write_text("#include <stdatomic.h>\n#include <stdio.h>\n_Atomic(int) count;\nint probe(void) { return atomic_fetch_add(&count, 1); }\n")
        subprocess.run([str(binary), args.cc, str(c), str(work / "probe.obj")], check=True)


if __name__ == "__main__":
    main()
