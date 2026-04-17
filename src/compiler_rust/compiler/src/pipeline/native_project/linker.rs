//! Linker selection, linking, system symbols, stub generation.

use std::collections::HashMap;
use std::path::{Path, PathBuf};

use super::{effective_target, safe_canonicalize, ModuleImports, NativeProjectBuilder};
use super::stubs::{generate_stub_object, generate_stub_object_freestanding};
use super::tools::{
    find_archive_tool, find_c_compiler, find_cxx_compiler, find_native_all_library, find_runtime_library,
    strip_llvm_constructors, is_system_symbol,
};

impl NativeProjectBuilder {
    fn read_global_symbols(obj: &Path) -> Result<Vec<String>, String> {
        let output = std::process::Command::new("nm")
            .arg("-g")
            .arg(obj)
            .output()
            .map_err(|e| format!("nm: {e}"))?;
        if !output.status.success() {
            return Ok(Vec::new());
        }
        Ok(String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| line.split_whitespace().last())
            .map(|raw_name| {
                if cfg!(target_os = "macos") {
                    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
                } else {
                    raw_name.to_string()
                }
            })
            .collect())
    }

    fn cached_global_symbols<'a>(
        cache: &'a mut HashMap<PathBuf, Vec<String>>,
        obj: &Path,
    ) -> Result<&'a Vec<String>, String> {
        let key = safe_canonicalize(obj);
        if !cache.contains_key(&key) {
            let symbols = Self::read_global_symbols(obj)?;
            cache.insert(key.clone(), symbols);
        }
        cache
            .get(&key)
            .ok_or_else(|| format!("missing symbol cache entry for {}", obj.display()))
    }

    /// Compile the C++ main stub to an object file.
    pub(crate) fn compile_main_stub(&self, temp_dir: &Path) -> Result<PathBuf, String> {
        let main_cpp = temp_dir.join("_main_stub.cpp");
        let cxx = find_cxx_compiler();
        let is_msvc = cxx.contains("clang-cl") || simple_common::platform::cc_detect::is_msvc_target(&cxx);

        let stub_code = if is_msvc {
            r#"
extern "C" {
    int spl_main(void);
    void rt_set_args(int argc, char** argv);
    void __simple_runtime_init(void);
    void __simple_runtime_shutdown(void);
}
#pragma comment(linker, "/ALTERNATENAME:spl_main=_spl_main_stub")
#pragma comment(linker, "/ALTERNATENAME:rt_set_args=_rt_set_args_stub")
#pragma comment(linker, "/ALTERNATENAME:__simple_runtime_init=___simple_runtime_init_stub")
#pragma comment(linker, "/ALTERNATENAME:__simple_runtime_shutdown=___simple_runtime_shutdown_stub")
extern "C" int _spl_main_stub(void) { return 0; }
extern "C" void _rt_set_args_stub(int, char**) {}
extern "C" void ___simple_runtime_init_stub(void) {}
extern "C" void ___simple_runtime_shutdown_stub(void) {}
int main(int argc, char** argv) {
    __simple_runtime_init();
    rt_set_args(argc, argv);
    int r = spl_main();
    __simple_runtime_shutdown();
    return r;
}
"#
        } else {
            r#"
extern "C" {
    int __attribute__((weak)) spl_main(void);
    void __attribute__((weak)) rt_set_args(int argc, char** argv);
    void __attribute__((weak)) __simple_runtime_init(void);
    void __attribute__((weak)) __simple_runtime_shutdown(void);
    void __attribute__((weak)) __simple_call_module_inits(void);
}
int main(int argc, char** argv) {
    if (__simple_runtime_init) __simple_runtime_init();
    if (__simple_call_module_inits) __simple_call_module_inits();
    if (rt_set_args) rt_set_args(argc, argv);
    int r = spl_main ? spl_main() : 0;
    if (__simple_runtime_shutdown) __simple_runtime_shutdown();
    return r;
}
"#
        };

        std::fs::write(&main_cpp, stub_code).map_err(|e| format!("write main stub: {e}"))?;

        let main_o = temp_dir.join("_main_stub.o");
        let output = if cxx.contains("clang-cl") {
            std::process::Command::new(&cxx)
                .arg("/c")
                .arg(format!("/Fo{}", main_o.display()))
                .arg("/Gy")
                .arg(&main_cpp)
                .output()
                .map_err(|e| format!("compile main stub: {e}"))?
        } else {
            std::process::Command::new(&cxx)
                .args(["-c", "-ffunction-sections", "-fdata-sections", "-o"])
                .arg(&main_o)
                .arg(&main_cpp)
                .output()
                .map_err(|e| format!("compile main stub: {e}"))?
        };
        if !output.status.success() {
            let stderr = String::from_utf8_lossy(&output.stderr);
            return Err(format!("Failed to compile main stub ({}): {}", cxx, stderr));
        }
        Ok(main_o)
    }

    /// Generate a constructor function that calls all __module_init_* functions.
    pub(crate) fn generate_init_caller(
        &self,
        temp_dir: &Path,
        object_paths: &[PathBuf],
        symbol_cache: Option<&mut HashMap<PathBuf, Vec<String>>>,
    ) -> Result<Option<PathBuf>, String> {
        let mut init_names = Vec::new();
        let mut local_cache = HashMap::new();
        let cache = match symbol_cache {
            Some(cache) => cache,
            None => &mut local_cache,
        };
        for obj in object_paths {
            for normalized in Self::cached_global_symbols(cache, obj)? {
                if normalized.starts_with("__module_init_") {
                    let sanitized = normalized.replace('.', "_dot_");
                    init_names.push(sanitized);
                }
            }
        }
        if init_names.is_empty() {
            return Ok(None);
        }
        init_names.sort();
        init_names.dedup();

        let cxx = find_cxx_compiler();
        let is_clang_cl = cxx.contains("clang-cl");

        let mut code = String::from("// Auto-generated: calls all __module_init_* functions\n");
        if is_clang_cl {
            code.push_str("extern \"C\" {\n");
            for name in &init_names {
                code.push_str(&format!("    void {}(void);\n", name));
            }
            code.push_str("}\n");
            for name in &init_names {
                let stub = format!("_{}_stub", name);
                code.push_str(&format!(
                    "#pragma comment(linker, \"/ALTERNATENAME:{}={}\")\n\
                     extern \"C\" void {}(void) {{}}\n",
                    name, stub, stub
                ));
            }
            code.push_str("extern \"C\" void __simple_call_module_inits(void) {\n");
            for name in &init_names {
                code.push_str(&format!("    {}();\n", name));
            }
            code.push_str("}\n");
        } else {
            code.push_str("extern \"C\" {\n");
            for name in &init_names {
                code.push_str(&format!("    void __attribute__((weak)) {}(void);\n", name));
            }
            code.push_str("}\n");
            code.push_str("extern \"C\" void __simple_call_module_inits(void) {\n");
            for name in &init_names {
                code.push_str(&format!("    if ({}) {}();\n", name, name));
            }
            code.push_str("}\n");
        }

        let init_cpp = temp_dir.join("_init_all.cpp");
        std::fs::write(&init_cpp, &code).map_err(|e| format!("write init_all: {e}"))?;

        let init_o = temp_dir.join("_init_all.o");
        let status = if is_clang_cl {
            std::process::Command::new(&cxx)
                .arg("/c")
                .arg("/O2")
                .arg("/Gy")
                .arg(format!("/Fo{}", init_o.display()))
                .arg(&init_cpp)
                .status()
                .map_err(|e| format!("compile init_all: {e}"))?
        } else {
            std::process::Command::new(&cxx)
                .arg("-c")
                .arg("-O2")
                .arg("-ffunction-sections")
                .arg("-fdata-sections")
                .arg(&init_cpp)
                .arg("-o")
                .arg(&init_o)
                .status()
                .map_err(|e| format!("compile init_all: {e}"))?
        };
        if !status.success() {
            return Err(format!("compile init_all.cpp failed ({})", cxx));
        }
        Ok(Some(init_o))
    }

    /// Compile C runtime sources to object files (currently disabled).
    pub(crate) fn compile_c_runtime(&self, _temp_dir: &Path) -> Result<Vec<PathBuf>, String> {
        Ok(Vec::new())
    }

    /// Link object files into a native binary using LinkerBuilder.
    pub(crate) fn link_objects(&self, object_paths: &[PathBuf], imports: &ModuleImports) -> Result<(), String> {
        let temp_dir = object_paths[0].parent().ok_or("no parent for object path")?;

        let cross_target = effective_target();
        let is_freestanding = self.config.target.is_some()
            || cross_target.os == simple_common::target::TargetOS::None
            || cross_target.os == simple_common::target::TargetOS::SimpleOS;
        if is_freestanding {
            return self.link_objects_freestanding(object_paths, temp_dir, imports);
        }

        let main_o = self.compile_main_stub(temp_dir)?;
        let init_o = self.generate_init_caller(temp_dir, object_paths, None)?;

        let selected_runtime = self.selected_runtime_library(temp_dir);
        self.reject_unexpected_native_all(selected_runtime.as_ref())?;
        let has_native_all = selected_runtime
            .as_ref()
            .map_or(false, |(_, is_native_all)| *is_native_all);
        let cc = if has_native_all {
            find_cxx_compiler()
        } else {
            find_c_compiler()
        };
        let is_clang_cl = cc.contains("clang-cl");
        let is_msvc = simple_common::platform::cc_detect::is_msvc_target(&cc);
        let mut cmd = std::process::Command::new(&cc);
        if !is_msvc {
            cmd.arg("-fPIC");
        }

        #[cfg(target_os = "macos")]
        cmd.arg("-Wl,-ld_classic");

        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        cmd.arg("-no-pie");

        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        cmd.arg("-Wl,-z,muldefs");

        let cross_target = effective_target();
        if !cross_target.is_host() {
            let triple = match (cross_target.arch, cross_target.os) {
                (simple_common::target::TargetArch::Riscv32, simple_common::target::TargetOS::None) => {
                    "riscv32-unknown-elf"
                }
                (simple_common::target::TargetArch::Riscv64, simple_common::target::TargetOS::None) => {
                    "riscv64-unknown-elf"
                }
                (simple_common::target::TargetArch::Aarch64, simple_common::target::TargetOS::None) => {
                    "aarch64-none-elf"
                }
                (simple_common::target::TargetArch::Arm, simple_common::target::TargetOS::None) => "armv7-none-eabihf",
                (simple_common::target::TargetArch::X86, simple_common::target::TargetOS::None) => "i686-unknown-elf",
                (simple_common::target::TargetArch::X86_64, simple_common::target::TargetOS::None) => {
                    "x86_64-unknown-elf"
                }
                (simple_common::target::TargetArch::X86_64, simple_common::target::TargetOS::SimpleOS) => {
                    "x86_64-unknown-elf"
                }
                (simple_common::target::TargetArch::Aarch64, simple_common::target::TargetOS::SimpleOS) => {
                    "aarch64-none-elf"
                }
                (simple_common::target::TargetArch::Riscv64, simple_common::target::TargetOS::SimpleOS) => {
                    "riscv64-unknown-elf"
                }
                (simple_common::target::TargetArch::Riscv32, simple_common::target::TargetOS::SimpleOS) => {
                    "riscv32-unknown-elf"
                }
                (simple_common::target::TargetArch::X86, simple_common::target::TargetOS::SimpleOS) => {
                    "i686-unknown-elf"
                }
                (simple_common::target::TargetArch::Arm, simple_common::target::TargetOS::SimpleOS) => {
                    "armv7-none-eabihf"
                }
                _ => "",
            };
            if !triple.is_empty() {
                cmd.arg(format!("--target={}", triple));
                cmd.arg("-nostdlib");
                cmd.arg("-ffreestanding");
            }
        }

        if let Some(ref ls) = self.config.linker_script {
            cmd.arg(format!("-T{}", ls.display()));
        }

        if is_clang_cl {
            cmd.arg(&main_o);
            if let Some(ref init) = init_o {
                cmd.arg(init);
            }
            cmd.arg(format!("/Fe:{}", self.output.display()));
        } else {
            cmd.arg("-o").arg(&self.output).arg(&main_o);
            if let Some(ref init) = init_o {
                cmd.arg(init);
            }
        }

        if object_paths.len() > 100 {
            let archive_path = temp_dir.join("libspl_objects.a");
            let ar_tool = find_archive_tool();
            let is_msvc_lib = ar_tool == "lib";

            const BATCH_SIZE: usize = 200;
            let mut ar_ok = true;
            for (i, chunk) in object_paths.chunks(BATCH_SIZE).enumerate() {
                let status = if is_msvc_lib {
                    let mut lib_cmd = std::process::Command::new(&ar_tool);
                    lib_cmd.arg(format!("/OUT:{}", archive_path.display()));
                    if i > 0 {
                        lib_cmd.arg(&archive_path);
                    }
                    lib_cmd
                        .args(chunk)
                        .status()
                        .map_err(|e| format!("lib batch {i}: {e}"))?
                } else {
                    let flag = if i == 0 { "rcs" } else { "rs" };
                    std::process::Command::new(&ar_tool)
                        .arg(flag)
                        .arg(&archive_path)
                        .args(chunk)
                        .status()
                        .map_err(|e| format!("ar batch {i}: {e}"))?
                };
                if !status.success() {
                    ar_ok = false;
                    break;
                }
            }
            if !ar_ok {
                #[cfg(target_os = "macos")]
                {
                    let mut sub_archives = Vec::new();
                    for (i, chunk) in object_paths.chunks(BATCH_SIZE).enumerate() {
                        let sub = temp_dir.join(format!("_batch_{}.a", i));
                        let s = std::process::Command::new("libtool")
                            .arg("-static")
                            .arg("-o")
                            .arg(&sub)
                            .args(chunk)
                            .status()
                            .map_err(|e| format!("libtool batch {i}: {e}"))?;
                        if !s.success() {
                            return Err(format!("libtool failed on batch {i}"));
                        }
                        sub_archives.push(sub);
                    }
                    let s = std::process::Command::new("libtool")
                        .arg("-static")
                        .arg("-o")
                        .arg(&archive_path)
                        .args(&sub_archives)
                        .status()
                        .map_err(|e| format!("libtool merge: {e}"))?;
                    if !s.success() {
                        return Err("libtool merge failed".to_string());
                    }
                }
                #[cfg(not(target_os = "macos"))]
                return Err("ar failed to create archive".to_string());
            }
            #[cfg(target_os = "macos")]
            {
                cmd.arg("-Wl,-force_load").arg(&archive_path);
                cmd.arg("-Wl,-no_deduplicate");
            }
            #[cfg(any(target_os = "linux", target_os = "freebsd"))]
            {
                cmd.arg("-Wl,--whole-archive")
                    .arg(&archive_path)
                    .arg("-Wl,--no-whole-archive");
            }
            #[cfg(target_os = "windows")]
            {
                if is_clang_cl {
                    cmd.arg(&archive_path);
                } else if is_msvc {
                    cmd.arg(format!("-Wl,/WHOLEARCHIVE:{}", archive_path.display()));
                } else {
                    cmd.arg("-Wl,--whole-archive")
                        .arg(&archive_path)
                        .arg("-Wl,--no-whole-archive");
                }
            }
        } else {
            for obj in object_paths {
                cmd.arg(obj);
            }
        }

        if let Some((runtime_lib, is_native_all)) = selected_runtime.as_ref() {
            if *is_native_all {
                #[cfg(target_os = "macos")]
                {
                    cmd.arg("-Wl,-force_load").arg(runtime_lib);
                }
                #[cfg(target_os = "windows")]
                {
                    if is_clang_cl {
                        cmd.arg(runtime_lib);
                    } else if is_msvc {
                        cmd.arg(format!("-Wl,/WHOLEARCHIVE:{}", runtime_lib.display()));
                    } else {
                        cmd.arg("-Wl,--whole-archive");
                        cmd.arg(runtime_lib);
                        cmd.arg("-Wl,--no-whole-archive");
                    }
                }
                #[cfg(any(target_os = "linux", target_os = "freebsd"))]
                {
                    cmd.arg("-Wl,--whole-archive");
                    cmd.arg(runtime_lib);
                    cmd.arg("-Wl,--no-whole-archive");
                }
            } else {
                cmd.arg(runtime_lib);
            }
        }

        #[cfg(target_os = "windows")]
        if is_clang_cl || is_msvc {
            std::env::set_var("SIMPLE_LINKER_FLAVOR", "msvc");
        }
        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        if !is_clang_cl && !is_msvc {
            cmd.arg("-Wl,--gc-sections");
        }
        let link_config = simple_common::platform::link_config::PlatformLinkConfig::for_host();
        for path in &link_config.library_search_paths {
            cmd.arg(format!("-L{}", path));
        }
        if is_clang_cl {
            for lib in &link_config.libraries {
                cmd.arg(format!("{}.lib", lib));
            }
        } else {
            for lib in &link_config.libraries {
                cmd.arg(format!("-l{}", lib));
            }
        }
        if cfg!(target_os = "macos") && find_native_all_library().is_some() {
            if let Some(llvm_lib) = simple_common::platform::cc_detect::find_homebrew_llvm_lib() {
                cmd.arg(format!("-L{}", llvm_lib));
                cmd.arg(format!("-Wl,-rpath,{}", llvm_lib));
            }
            cmd.arg("-lc++");
            for fw in simple_common::platform::link_config::PlatformLinkConfig::macos_frameworks() {
                cmd.arg("-framework").arg(fw);
            }
        }

        #[cfg(not(target_os = "windows"))]
        {
            let stubs_o = generate_stub_object(
                temp_dir,
                object_paths,
                &main_o,
                selected_runtime.as_ref().map(|(p, _)| p.as_path()),
                &imports,
            )?;
            cmd.arg(&stubs_o);
        }
        #[cfg(target_os = "windows")]
        if !is_msvc && !is_clang_cl {
            let stubs_o = generate_stub_object(
                temp_dir,
                object_paths,
                &main_o,
                selected_runtime.as_ref().map(|(p, _)| p.as_path()),
                &imports,
            )?;
            cmd.arg(&stubs_o);
        }
        for flag in &link_config.unresolved_symbol_flags {
            cmd.arg(flag);
        }
        #[cfg(target_os = "windows")]
        if is_clang_cl {
            cmd.arg("/link").arg("/WHOLEARCHIVE").arg("/FORCE:MULTIPLE,UNRESOLVED");
        } else if is_msvc {
            cmd.arg("-Xlinker").arg("/FORCE:MULTIPLE,UNRESOLVED");
        }

        if self.config.strip {
            #[cfg(target_os = "macos")]
            cmd.arg("-Wl,-S");
            #[cfg(any(target_os = "linux", target_os = "freebsd"))]
            cmd.arg("-Wl,-s");
            #[cfg(target_os = "windows")]
            if is_clang_cl {
                cmd.arg("/link").arg("/DEBUG:NONE").arg("/OPT:REF,ICF");
            } else if is_msvc {
                cmd.arg("-Wl,/DEBUG:NONE").arg("-Wl,/OPT:REF,ICF");
            } else {
                cmd.arg("-Wl,--gc-sections").arg("-Wl,-s");
            }
        }

        if self.config.verbose {
            eprintln!("Link command: {:?}", cmd);
        }

        let output_result = cmd.output().map_err(|e| format!("link ({cc}): {e}"))?;

        if output_result.status.success() {
            if let Ok(meta) = std::fs::metadata(&self.output) {
                eprintln!("Linked: {} ({} KB) via {cc}", self.output.display(), meta.len() / 1024);
            }
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr);
            Err(format!("link failed: {}", stderr))
        }
    }

    /// Link object files for a freestanding target (no OS, no libc).
    pub(crate) fn link_objects_freestanding(
        &self,
        object_paths: &[PathBuf],
        temp_dir: &Path,
        _imports: &ModuleImports,
    ) -> Result<(), String> {
        let cross_target = effective_target();
        let triple = match cross_target.arch {
            simple_common::target::TargetArch::Riscv32 => "riscv32-unknown-elf",
            simple_common::target::TargetArch::Riscv64 => "riscv64-unknown-elf",
            simple_common::target::TargetArch::Aarch64 => "aarch64-none-elf",
            simple_common::target::TargetArch::Arm => "armv7-none-eabihf",
            simple_common::target::TargetArch::X86 => "i686-unknown-elf",
            simple_common::target::TargetArch::X86_64 => "x86_64-unknown-elf",
            _ => return Err("unsupported freestanding target architecture".to_string()),
        };

        let cc = find_c_compiler();
        let mut symbol_cache = HashMap::new();
        let init_o = self.generate_init_caller(temp_dir, object_paths, Some(&mut symbol_cache))?;

        let use_llvm = std::env::var("SIMPLE_BACKEND").as_deref() == Ok("llvm");
        let (march, mabi) = match cross_target.arch {
            simple_common::target::TargetArch::Riscv64 if use_llvm => ("-march=rv64imac", "-mabi=lp64"),
            simple_common::target::TargetArch::Riscv64 => ("-march=rv64gc", "-mabi=lp64d"),
            simple_common::target::TargetArch::Riscv32 => ("-march=rv32imac", "-mabi=ilp32"),
            _ => ("", ""),
        };

        let mut boot_objects: Vec<PathBuf> = Vec::new();
        let mut boot_compile_failures: usize = 0;
        if let Some(ref entry) = self.entry_file {
            let boot_dir = entry.parent().unwrap_or(std::path::Path::new(".")).join("boot");
            if boot_dir.is_dir() {
                if self.config.verbose {
                    eprintln!("  Boot directory: {}", boot_dir.display());
                }
                let asm_compilers: Vec<String> = {
                    let mut v = vec![cc.clone()];
                    #[cfg(target_os = "macos")]
                    for p in [
                        "/opt/homebrew/opt/llvm@18/bin/clang",
                        "/opt/homebrew/opt/llvm/bin/clang",
                        "/usr/local/opt/llvm/bin/clang",
                    ] {
                        if std::path::Path::new(p).exists() && !v.contains(&p.to_string()) {
                            v.push(p.to_string());
                        }
                    }
                    v
                };
                for ext in &["S", "s"] {
                    if let Ok(entries) = std::fs::read_dir(&boot_dir) {
                        for de in entries.flatten() {
                            let path = de.path();
                            if path.extension().and_then(|e| e.to_str()) == Some(ext) {
                                let stem = path.file_stem().unwrap_or_default().to_string_lossy();
                                let out = temp_dir.join(format!("_boot_{}.o", stem));
                                let mut assembled = false;
                                let mut last_stderr = String::new();
                                let mut last_code: Option<i32> = None;
                                for asm_cc in &asm_compilers {
                                    let mut asm_cmd = std::process::Command::new(asm_cc);
                                    asm_cmd
                                        .args(["-c", "-o"])
                                        .arg(&out)
                                        .arg(&path)
                                        .arg(format!("--target={}", triple));
                                    if !march.is_empty() {
                                        asm_cmd.arg(march);
                                    }
                                    if !mabi.is_empty() {
                                        asm_cmd.arg(mabi);
                                    }
                                    match asm_cmd.output() {
                                        Ok(r) => {
                                            if r.status.success() {
                                                boot_objects.push(out.clone());
                                                assembled = true;
                                                break;
                                            } else {
                                                last_code = r.status.code();
                                                last_stderr =
                                                    String::from_utf8_lossy(&r.stderr).into_owned();
                                            }
                                        }
                                        Err(e) => {
                                            last_stderr = format!("spawn error: {}", e);
                                        }
                                    }
                                }
                                if !assembled {
                                    boot_compile_failures += 1;
                                    let tail: String = last_stderr
                                        .lines()
                                        .rev()
                                        .take(20)
                                        .collect::<Vec<_>>()
                                        .into_iter()
                                        .rev()
                                        .collect::<Vec<_>>()
                                        .join("\n");
                                    eprintln!(
                                        "  ERROR: failed to assemble {} (exit={:?})\n--- stderr tail ---\n{}\n--- end stderr ---",
                                        path.display(),
                                        last_code,
                                        tail
                                    );
                                }
                            }
                        }
                    }
                }
                if let Ok(entries) = std::fs::read_dir(&boot_dir) {
                    for de in entries.flatten() {
                        let path = de.path();
                        if path.extension().and_then(|e| e.to_str()) == Some("c") {
                            let stem = path.file_stem().unwrap_or_default().to_string_lossy();
                            let out = temp_dir.join(format!("_boot_{}.o", stem));
                            let mut c_cmd = std::process::Command::new(&cc);
                            c_cmd
                                .args(["-c", "-ffreestanding", "-nostdlib", "-fno-pie", "-o"])
                                .arg(&out)
                                .arg(&path)
                                .arg(format!("--target={}", triple));
                            if triple.contains("x86_64") {
                                c_cmd.arg("-mno-red-zone");
                            }
                            if !march.is_empty() {
                                c_cmd.args([march, mabi, "-mcmodel=medany"]);
                            }
                            match c_cmd.output() {
                                Ok(r) => {
                                    if r.status.success() {
                                        boot_objects.push(out);
                                    } else {
                                        boot_compile_failures += 1;
                                        let stderr_str =
                                            String::from_utf8_lossy(&r.stderr).into_owned();
                                        let tail: String = stderr_str
                                            .lines()
                                            .rev()
                                            .take(20)
                                            .collect::<Vec<_>>()
                                            .into_iter()
                                            .rev()
                                            .collect::<Vec<_>>()
                                            .join("\n");
                                        eprintln!(
                                            "  ERROR: failed to compile {} (exit={:?})\n--- stderr tail ---\n{}\n--- end stderr ---",
                                            path.display(),
                                            r.status.code(),
                                            tail
                                        );
                                    }
                                }
                                Err(e) => {
                                    boot_compile_failures += 1;
                                    eprintln!(
                                        "  ERROR: failed to spawn clang for {}: {}",
                                        path.display(),
                                        e
                                    );
                                }
                            }
                        }
                    }
                }
                if boot_compile_failures > 0 {
                    eprintln!(
                        "  WARNING: {} boot source file(s) failed to compile; resulting ELF may have undefined refs",
                        boot_compile_failures
                    );
                }
                if self.config.verbose {
                    eprintln!(
                        "  Boot objects: {} files ({} compile failures)",
                        boot_objects.len(),
                        boot_compile_failures
                    );
                }
            }
        }

        let arch_filters: &[&str] = match cross_target.arch {
            simple_common::target::TargetArch::Riscv64 => &["__riscv__", "__riscv64__"],
            simple_common::target::TargetArch::Riscv32 => &["__riscv32__"],
            simple_common::target::TargetArch::Aarch64 => &["__arm64__", "__aarch64__", "__arm__"],
            simple_common::target::TargetArch::Arm => &["__arm__", "__arm32__"],
            simple_common::target::TargetArch::X86_64 => &["__x86_64__", "__x86__"],
            simple_common::target::TargetArch::X86 => &["__x86__", "__x86_32__"],
            _ => &[],
        };
        let arch_neg_filters: &[&str] = match cross_target.arch {
            simple_common::target::TargetArch::Riscv64 => &["__riscv32__"],
            simple_common::target::TargetArch::X86_64 => &["__x86_32__"],
            _ => &[],
        };

        #[cfg(any(target_os = "macos", target_os = "linux", target_os = "freebsd"))]
        let use_direct_lld = {
            ["ld.lld", "/opt/homebrew/bin/ld.lld", "/usr/local/bin/ld.lld"]
                .iter()
                .find(|p| {
                    std::process::Command::new(p)
                        .arg("--version")
                        .output()
                        .map_or(false, |o| o.status.success())
                })
                .map(|s| s.to_string())
        };
        #[cfg(not(any(target_os = "macos", target_os = "linux", target_os = "freebsd")))]
        let use_direct_lld: Option<String> = None;

        let ordered_objects = {
            let mut start_obj_idx: Option<usize> = None;
            for (i, obj) in object_paths.iter().enumerate() {
                if Self::cached_global_symbols(&mut symbol_cache, obj)?.iter().any(|sym| {
                    (sym.ends_with("___start") || sym.ends_with("__spl_start"))
                        && sym != "_start"
                        && sym != "spl_start"
                        && !sym.contains("_starts_with")
                        && arch_filters.iter().any(|f| sym.contains(f))
                        && !arch_neg_filters.iter().any(|f| sym.contains(f))
                }) {
                        start_obj_idx = Some(i);
                        break;
                }
            }
            let mut ordered: Vec<&PathBuf> = Vec::with_capacity(object_paths.len());
            if let Some(idx) = start_obj_idx {
                ordered.push(&object_paths[idx]);
                for (i, obj) in object_paths.iter().enumerate() {
                    if i != idx {
                        ordered.push(obj);
                    }
                }
            } else {
                ordered.extend(object_paths.iter());
            }
            ordered
        };

        // Blocker A fix: mirror the hosted-path `generate_stub_object` injection for
        // freestanding links. Without this, 174+ undefined Simple class-method symbols
        // (apps__installer_gui__..., common__render_scene__executor__..., etc.) were
        // being accepted by `--unresolved-symbols=ignore-all` and resolved to address 0
        // — calling them at runtime produced the `FAULT @ 0x950a` cascade through the
        // legacy VGA MMIO region. The freestanding stub generator emits weak `return 0`
        // definitions compiled with the cross `--target=<triple>` so every unresolved
        // ref lands on a harmless no-op instead of null. We KEEP --unresolved-symbols=
        // ignore-all as a belt-and-suspenders safety net for this commit; removing it
        // can be a follow-up slice once stub coverage is proven across arches.
        let freestanding_stub_obj = match generate_stub_object_freestanding(
            temp_dir,
            object_paths,
            &boot_objects,
            triple,
            march,
            mabi,
        ) {
            Ok(p) => Some(p),
            Err(e) => {
                eprintln!(
                    "  WARNING: freestanding stub generation failed: {} (link will proceed with ignore-all fallback)",
                    e
                );
                None
            }
        };

        let mut cmd = if let Some(ref lld_path) = use_direct_lld {
            let mut c = std::process::Command::new(lld_path);
            if let Some(ref ls) = self.config.linker_script {
                c.arg(format!("-T{}", ls.display()));
            }
            c.arg("-o").arg(&self.output);
            for boot_obj in &boot_objects {
                c.arg(boot_obj);
            }
            for obj in &ordered_objects {
                c.arg(obj.as_os_str());
            }
            if let Some(ref init) = init_o {
                c.arg(init);
            }
            if let Some(ref stub_o) = freestanding_stub_obj {
                c.arg(stub_o);
            }
            c
        } else {
            let mut c = std::process::Command::new(&cc);
            c.arg(format!("--target={}", triple));
            c.arg("-nostdlib");
            c.arg("-ffreestanding");
            c.arg("-static");
            c.arg("-fno-pic");
            c.arg("-fno-pie");
            c.arg("-fuse-ld=lld");
            if let Some(ref ls) = self.config.linker_script {
                c.arg(format!("-T{}", ls.display()));
            }
            c.arg("-o").arg(&self.output);
            for boot_obj in &boot_objects {
                c.arg(boot_obj);
            }
            for obj in &ordered_objects {
                c.arg(obj.as_os_str());
            }
            if let Some(ref init) = init_o {
                c.arg(init);
            }
            if let Some(ref stub_o) = freestanding_stub_obj {
                c.arg(stub_o);
            }
            c
        };

        if !boot_objects.is_empty() {
            let has_entry32 = boot_objects.iter().any(|obj| {
                Self::cached_global_symbols(&mut symbol_cache, obj)
                    .map(|symbols| symbols.iter().any(|sym| sym == "_entry32"))
                    .unwrap_or(false)
            });
            if has_entry32 {
                let entry_flag = if use_direct_lld.is_some() {
                    "--entry=_entry32"
                } else {
                    "-Wl,--entry=_entry32"
                };
                cmd.arg(entry_flag);
            }
        }

        // Scan for mangled _start -> create defsym alias.
        {
            let has_boot = !boot_objects.is_empty();
            let mut best_start: Option<String> = None;
            let mut fallback_start: Option<String> = None;

            if let Some(ref entry) = self.entry_file {
                let entry_str = entry.to_string_lossy();
                let stem = entry_str.trim_start_matches('/').trim_end_matches(".spl");
                let mangled_stem = stem.replace('/', "__");
                let candidates = [
                    format!("{}___start", mangled_stem),
                    format!("{}__spl_start", mangled_stem),
                ];
                'entry_search: for obj in object_paths {
                    for sym in Self::cached_global_symbols(&mut symbol_cache, obj)? {
                        if candidates.iter().any(|candidate| candidate == sym) {
                            best_start = Some(sym.to_string());
                            break 'entry_search;
                        }
                    }
                }
            }

            if best_start.is_none() {
                for obj in object_paths {
                    for sym in Self::cached_global_symbols(&mut symbol_cache, obj)? {
                        if (sym.ends_with("___start") || sym.ends_with("__spl_start"))
                            && sym != "_start"
                            && sym != "spl_start"
                        {
                            let neg_match = arch_neg_filters.iter().any(|f| sym.contains(f));
                            if neg_match {
                                continue;
                            }
                            let pos_match = arch_filters.iter().any(|f| sym.contains(f));
                            if pos_match {
                                best_start = Some(sym.to_string());
                            } else if fallback_start.is_none() {
                                fallback_start = Some(sym.to_string());
                            }
                        }
                    }
                }
            }
            if let Some(sym) = best_start.or(fallback_start) {
                let alias = if has_boot { "spl_start" } else { "_start" };
                if use_direct_lld.is_some() {
                    cmd.arg(format!("--defsym={}={}", alias, sym));
                } else {
                    cmd.arg(format!("-Wl,--defsym={}={}", alias, sym));
                }
            }
        }

        if use_direct_lld.is_some() {
            cmd.arg("-z").arg("muldefs");
            cmd.arg("--unresolved-symbols=ignore-all");
            if self.config.strip {
                cmd.arg("-s");
            }
        } else {
            cmd.arg("-Wl,-z,muldefs");
            cmd.arg("-Wl,--unresolved-symbols=ignore-all");
            if self.config.strip {
                cmd.arg("-Wl,-s");
            }
        }

        if self.config.verbose {
            eprintln!("Freestanding link command: {:?}", cmd);
        }

        let output_result = cmd.output().map_err(|e| format!("link ({cc}): {e}"))?;

        if output_result.status.success() {
            if (triple.contains("x86_64") || triple.contains("i686")) && !boot_objects.is_empty() {
                let elf64 = self.output.with_extension("elf64");
                let _ = std::fs::rename(&self.output, &elf64);
                let objcopy_bin = ["llvm-objcopy", "gobjcopy", "objcopy"]
                    .iter()
                    .find(|bin| {
                        std::process::Command::new(bin)
                            .arg("--version")
                            .output()
                            .map_or(false, |o| o.status.success())
                    })
                    .unwrap_or(&"objcopy");
                let objcopy = std::process::Command::new(objcopy_bin)
                    .args(["-O", "elf32-i386"])
                    .arg(&elf64)
                    .arg(&self.output)
                    .output();
                match objcopy {
                    Ok(r) if r.status.success() => {
                        let _ = std::fs::remove_file(&elf64);
                    }
                    _ => {
                        let _ = std::fs::rename(&elf64, &self.output);
                        eprintln!("WARNING: objcopy elf32 failed, keeping 64-bit ELF");
                    }
                }
            }
            if let Ok(meta) = std::fs::metadata(&self.output) {
                eprintln!(
                    "Linked (freestanding): {} ({} KB) via {cc} --target={}",
                    self.output.display(),
                    meta.len() / 1024,
                    triple
                );
            }
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr);
            Err(format!("link failed: {}", stderr))
        }
    }
}
