//! Compile the unchanged Windows runtime PTY owner without unrelated runtime
//! heap/collection exports. Both slices fail closed when owner boundaries move.
fn main() {
    let owner = "../../../../src/compiler_rust/runtime/src/value/pty.rs";
    println!("cargo:rerun-if-changed={owner}");
    let source = std::fs::read_to_string(owner).unwrap();
    let start = source.find("#[cfg(windows)]\nmod pty_process {").unwrap();
    let stop = source[start..].find("\n#[no_mangle]\npub extern \"C\" fn rt_pty_open").unwrap() + start;
    let wrappers_start = source.find("#[cfg(windows)]\npub fn host_pty_open").unwrap();
    let wrappers_stop = source[wrappers_start..].find("\n#[no_mangle]").unwrap() + wrappers_start;
    let output = std::path::PathBuf::from(std::env::var_os("OUT_DIR").unwrap()).join("runtime_pty_owner.rs");
    std::fs::write(output, format!("{}\n{}", &source[start..stop], &source[wrappers_start..wrappers_stop])).unwrap();
}
