#!/usr/bin/env python3
"""Execute the production compiler selector without building the compiler crate."""
import os
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[2]
source = Path(sys.argv[1]) if len(sys.argv) > 1 else root / "src/compiler_rust/compiler/src/pipeline/native_project/tools.rs"
text = source.read_text(encoding="utf-8")
start = text.index("pub(crate) fn target_c_compiler(")
end = text.index("\npub(crate) fn target_cxx_compiler(", start)
selector = text[start:end]
path_module = root / "src/compiler_rust/common/src/platform/path.rs"
path_literal = 'r#"' + path_module.as_posix() + '"#'
harness = '''
#![allow(dead_code)]
mod simple_common {
    pub mod target {
        #[derive(PartialEq, Clone, Copy)] pub enum TargetOS { Windows, Linux }
        #[derive(PartialEq, Clone, Copy)] pub enum LinkerFlavor { Gnu, Msvc }
        #[derive(Clone, Copy)] pub struct Target { pub os: TargetOS, pub flavor: LinkerFlavor }
        impl Target { pub fn linker_flavor(&self) -> LinkerFlavor { self.flavor } }
    }
    pub mod platform {
        #[path = PATH_MODULE] pub mod path;
        pub mod cc_detect {
            pub fn detect_c_compiler_for_target(_: &crate::simple_common::target::Target) -> String {
                "general-detector".into()
            }
        }
    }
}
fn hosted_linux_cross_compiler(_: simple_common::target::Target, _: bool) -> Option<&'static str> { None }
SELECTOR
fn main() {
    use simple_common::target::*;
    let gnu = std::env::args().nth(1).as_deref() == Some("gnu");
    println!("{}", target_c_compiler(Target { os: TargetOS::Windows,
        flavor: if gnu { LinkerFlavor::Gnu } else { LinkerFlavor::Msvc } }));
}
'''.replace("PATH_MODULE", path_literal).replace("SELECTOR", selector)
# TemporaryDirectory owns this newly created directory and removes only its contents.
with tempfile.TemporaryDirectory(prefix="simple-gnu-cc-authority-") as scratch:
    scratch = Path(scratch).resolve()
    rust_source = scratch / "selector.rs"
    executable = scratch / ("selector.exe" if os.name == "nt" else "selector")
    rust_source.write_text(harness, encoding="utf-8")
    subprocess.run(["rustc", "--edition=2021", str(rust_source), "-o", str(executable)], check=True)
    cases = [
        ("gnu", "C:/Toolchain With Spaces/bin/clang.exe", "C:\\Toolchain With Spaces\\bin\\clang.exe" if os.name == "nt" else "C:/Toolchain With Spaces/bin/clang.exe"),
        ("gnu", "/c/toolchain/bin/clang.exe", "c:\\toolchain\\bin\\clang.exe" if os.name == "nt" else "/c/toolchain/bin/clang.exe"),
        ("gnu", "", "clang"),
        ("gnu", "  ", "clang"),
        ("gnu", None, "clang"),
        ("msvc", "C:/toolchain/bin/clang-cl.exe", "general-detector"),
    ]
    for lane, cc, expected in cases:
        env = os.environ.copy()
        if cc is None:
            env.pop("CC", None)
        else:
            env["CC"] = cc
        result = subprocess.check_output([str(executable), lane], env=env, text=True).strip()
        assert result == expected, f"{lane} CC={cc!r}: got {result!r}, expected {expected!r}"
    print(f"PASS: {len(cases)} production compiler-authority cases")
