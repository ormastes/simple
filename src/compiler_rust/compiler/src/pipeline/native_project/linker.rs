//! Linker selection, linking, system symbols, stub generation.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::path::{Path, PathBuf};

use super::{effective_target, inline_asm_emit, safe_canonicalize, ModuleImports, NativeProjectBuilder};
use super::stubs::{generate_stub_object, generate_stub_object_freestanding};
use super::tools::{
    archive_create_command, build_compiler_backfill_archive, build_stage4_c_runtime_library,
    build_stage4_cli_c_provider_archives, build_stage4_runtime_capsule_archive,
    build_stage4_rust_runtime_projection_archive, find_archive_tool, find_c_compiler, find_compiler_rt_builtins,
    find_cxx_compiler, find_objcopy_tool, is_system_symbol, nm_command, strip_llvm_constructors, target_c_compiler,
    target_cxx_compiler, terminfo_link_args, validate_stage4_cli_c_provider_archive_disjointness,
};

#[cfg(target_os = "macos")]
fn add_macos_base_link_args(cmd: &mut std::process::Command) {
    cmd.arg("-Wl,-ld_classic").arg("-Wl,-dead_strip");
}

#[cfg(target_os = "macos")]
fn add_macos_native_all_host_support(cmd: &mut std::process::Command) {
    if let Some(llvm_lib) = simple_common::platform::cc_detect::find_homebrew_llvm_lib() {
        cmd.arg(format!("-L{}", llvm_lib));
        cmd.arg(format!("-Wl,-rpath,{}", llvm_lib));
    }
    cmd.arg("-lc++");
    for framework in simple_common::platform::link_config::PlatformLinkConfig::macos_frameworks() {
        cmd.arg("-framework").arg(framework);
    }
}

impl NativeProjectBuilder {
    pub(crate) fn stage4_rust_runtime_staticlib(runtime_path: &Path) -> Result<PathBuf, String> {
        let archive = runtime_path.join("deps/libsimple_runtime.a");
        if !archive.is_file() {
            return Err(format!(
                "Stage4 Rust runtime staticlib is missing: {}",
                archive.display()
            ));
        }
        Ok(archive)
    }

    pub(crate) fn prepare_stage4_compiler_backfill_archive(
        &self,
        selected_runtime: Option<&(PathBuf, bool)>,
        additional_providers: &[PathBuf],
        temp_dir: &Path,
    ) -> Result<Option<PathBuf>, String> {
        let Some(source) = self.selected_stage4_compiler_backfill_archive()? else {
            return Ok(None);
        };
        let mut providers = selected_runtime.map(|(path, _)| vec![path.clone()]).unwrap_or_default();
        providers.extend_from_slice(additional_providers);
        build_compiler_backfill_archive(&source, &providers, temp_dir).map(Some)
    }

    pub(super) fn resolve_freestanding_linker_script(
        explicit: Option<&Path>,
        target: simple_common::target::Target,
        simpleos_sysroot: &Path,
    ) -> Option<PathBuf> {
        explicit.map(Path::to_path_buf).or_else(|| {
            (target.os == simple_common::target::TargetOS::SimpleOS
                && matches!(
                    target.arch,
                    simple_common::target::TargetArch::X86_64 | simple_common::target::TargetArch::Aarch64
                ))
            .then(|| simpleos_sysroot.join("share/simpleos/simpleos.ld"))
        })
    }

    fn freestanding_target_triple(target: simple_common::target::Target) -> Option<&'static str> {
        match (target.arch, target.os) {
            (simple_common::target::TargetArch::Riscv32, simple_common::target::TargetOS::None) => {
                Some("riscv32-unknown-elf")
            }
            (simple_common::target::TargetArch::Riscv64, simple_common::target::TargetOS::None) => {
                Some("riscv64-unknown-elf")
            }
            (simple_common::target::TargetArch::Aarch64, simple_common::target::TargetOS::None) => {
                Some("aarch64-none-elf")
            }
            (simple_common::target::TargetArch::Arm, simple_common::target::TargetOS::None) => {
                Some("armv7-none-eabihf")
            }
            (simple_common::target::TargetArch::X86, simple_common::target::TargetOS::None) => Some("i686-unknown-elf"),
            (simple_common::target::TargetArch::X86_64, simple_common::target::TargetOS::None) => {
                Some("x86_64-unknown-elf")
            }
            (simple_common::target::TargetArch::X86_64, simple_common::target::TargetOS::SimpleOS) => {
                Some("x86_64-unknown-elf")
            }
            (simple_common::target::TargetArch::Aarch64, simple_common::target::TargetOS::SimpleOS) => {
                Some("aarch64-none-elf")
            }
            (simple_common::target::TargetArch::Riscv64, simple_common::target::TargetOS::SimpleOS) => {
                Some("riscv64-unknown-elf")
            }
            (simple_common::target::TargetArch::Riscv32, simple_common::target::TargetOS::SimpleOS) => {
                Some("riscv32-unknown-elf")
            }
            (simple_common::target::TargetArch::X86, simple_common::target::TargetOS::SimpleOS) => {
                Some("i686-unknown-elf")
            }
            (simple_common::target::TargetArch::Arm, simple_common::target::TargetOS::SimpleOS) => {
                Some("armv7-none-eabihf")
            }
            _ => None,
        }
    }

    fn simpleos_sysroot_dir(arch: simple_common::target::TargetArch) -> PathBuf {
        if let Ok(explicit) = std::env::var("SIMPLEOS_SYSROOT") {
            return PathBuf::from(explicit);
        }
        match arch {
            // Per-arch sysroots: x86_64 keeps the historical unsuffixed path.
            simple_common::target::TargetArch::Aarch64 => PathBuf::from("build/os/sysroot-aarch64"),
            _ => PathBuf::from("build/os/sysroot"),
        }
    }

    fn simpleos_user_runtime_paths(cross_target: simple_common::target::Target) -> Option<(PathBuf, PathBuf, PathBuf)> {
        if cross_target.os != simple_common::target::TargetOS::SimpleOS
            || !matches!(
                cross_target.arch,
                simple_common::target::TargetArch::X86_64 | simple_common::target::TargetArch::Aarch64
            )
        {
            return None;
        }
        let sysroot = Self::simpleos_sysroot_dir(cross_target.arch);
        let crt0 = sysroot.join("lib").join("crt0.o");
        let runtime = sysroot.join("lib").join("libsimple_runtime.a");
        let libc = sysroot.join("lib").join("libsimpleos_c.a");
        if crt0.exists() && runtime.exists() && libc.exists() {
            Some((crt0, runtime, libc))
        } else {
            None
        }
    }

    fn read_global_symbol_types(obj: &Path) -> Result<Vec<(String, String)>, String> {
        let output = nm_command()
            .arg("-g")
            .arg("-p")
            .arg(obj)
            .output()
            .map_err(|e| format!("nm: {e}"))?;
        if !output.status.success() {
            return Ok(Vec::new());
        }
        let mut symbols = Vec::new();
        for line in String::from_utf8_lossy(&output.stdout).lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            let parsed = match parts.as_slice() {
                [sym_type, name] => Some((*sym_type, *name)),
                [_addr, sym_type, name] => Some((*sym_type, *name)),
                _ => None,
            };
            if let Some((sym_type, raw_name)) = parsed {
                let name = if cfg!(target_os = "macos") {
                    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
                } else {
                    raw_name.to_string()
                };
                symbols.push((sym_type.to_string(), name));
            }
        }
        Ok(symbols)
    }

    pub(crate) fn freestanding_weak_boot_defsyms(
        object_paths: &[PathBuf],
        boot_objects: &[PathBuf],
        imports: &ModuleImports,
    ) -> Result<Vec<(String, String)>, String> {
        let mut boot_weak = HashSet::new();
        for obj in boot_objects {
            for (kind, name) in Self::read_global_symbol_types(obj)? {
                if matches!(kind.as_str(), "W" | "w" | "V" | "v") {
                    boot_weak.insert(name);
                }
            }
        }
        if boot_weak.is_empty() {
            return Ok(Vec::new());
        }

        let mut simple_defined = HashSet::new();
        let mut simple_strong_defined = HashSet::new();
        for obj in object_paths {
            for (kind, name) in Self::read_global_symbol_types(obj)? {
                // Undefined references (`U`, and weak-undefined `w`/`v`) are NOT
                // definitions: aliasing a boot-weak symbol onto an undefined name
                // produces a `--defsym: symbol not found` link error. Only count
                // genuinely defined symbols here.
                if matches!(kind.as_str(), "U" | "w" | "v") {
                    continue;
                }
                if !matches!(kind.as_str(), "W" | "V") {
                    simple_strong_defined.insert(name.clone());
                }
                simple_defined.insert(name);
            }
        }

        let mut aliases = BTreeMap::new();
        for (raw, variants) in imports.all_mangled.iter() {
            if !boot_weak.contains(raw) {
                continue;
            }
            if let Some(target) = variants
                .iter()
                .find(|candidate| *candidate != raw && simple_defined.contains(*candidate))
            {
                aliases.insert(raw.clone(), target.clone());
            }
        }

        for raw in &boot_weak {
            if aliases.contains_key(raw) {
                continue;
            }
            let suffix = format!("__{}", raw);
            if let Some(target) = simple_strong_defined
                .iter()
                .filter(|candidate| *candidate != raw)
                .filter(|candidate| candidate.ends_with(&suffix))
                .min()
            {
                aliases.insert(raw.clone(), target.clone());
            }
        }
        Ok(aliases.into_iter().collect())
    }

    /// Bridge fully module-qualified cross-module references to the bare symbol
    /// names that `@export("C")` and ambiguous-name functions actually emit.
    ///
    /// A caller that imports e.g. `use os.kernel.boot.tcp_baremetal_min` resolves
    /// the call `rt_io_tcp_bind(...)` through the import map to the prefixed symbol
    /// `os__kernel__boot__tcp_baremetal_min__rt_io_tcp_bind`. The *defining* module,
    /// however, emits that function under its bare C-ABI / weak name
    /// (`rt_io_tcp_bind`) because it carries `@export` or because the name is
    /// defined in multiple modules. The result is an undefined-symbol link error.
    ///
    /// For every undefined `PREFIX__SUFFIX` reference for which no object defines
    /// `PREFIX__SUFFIX` but some object *does* define the bare `SUFFIX`, emit a
    /// `--defsym=PREFIX__SUFFIX=SUFFIX` alias. This canonicalizes the reference
    /// onto the definition without changing any definition mangling, so targets
    /// that already link cleanly (no such dangling references) are unaffected.
    pub(crate) fn freestanding_qualified_to_bare_defsyms(
        object_paths: &[PathBuf],
        boot_objects: &[PathBuf],
    ) -> Result<Vec<(String, String)>, String> {
        let mut defined = HashSet::new();
        let mut undefined = HashSet::new();
        for obj in object_paths.iter().chain(boot_objects.iter()) {
            for (kind, name) in Self::read_global_symbol_types(obj)? {
                if kind == "U" {
                    undefined.insert(name);
                } else {
                    defined.insert(name);
                }
            }
        }

        let mut aliases = BTreeMap::new();
        for reference in &undefined {
            // Only consider module-qualified references (contain the `__` joiner)
            // that are still undefined after collecting every object's symbols.
            if defined.contains(reference) {
                continue;
            }
            let Some((_, suffix)) = reference.rsplit_once("__") else {
                continue;
            };
            if suffix.is_empty() || suffix == reference.as_str() {
                continue;
            }
            // The bare definition must exist and differ from the reference.
            if suffix != reference.as_str() && defined.contains(suffix) {
                aliases.insert(reference.clone(), suffix.to_string());
            }
        }
        Ok(aliases.into_iter().collect())
    }

    /// Reverse of `freestanding_qualified_to_bare_defsyms`: bridge an undefined
    /// *bare* reference onto a defined *module-qualified* symbol when EXACTLY ONE
    /// qualified definition has that bare name as its `__`-joined suffix. This
    /// covers codegen that emits a bare call (e.g. `char_from_code`) while the
    /// only definition in the closure is the mangled
    /// `lib__common__string_core__char_from_code`. Ambiguous (multiple qualified
    /// definitions with the same suffix) is left alone — auto-aliasing could
    /// route the call to the wrong implementation.
    pub(crate) fn freestanding_bare_to_qualified_defsyms(
        object_paths: &[PathBuf],
        boot_objects: &[PathBuf],
    ) -> Result<Vec<(String, String)>, String> {
        let mut defined = HashSet::new();
        let mut undefined = HashSet::new();
        for obj in object_paths.iter().chain(boot_objects.iter()) {
            for (kind, name) in Self::read_global_symbol_types(obj)? {
                if kind == "U" {
                    undefined.insert(name);
                } else {
                    defined.insert(name);
                }
            }
        }

        // Map each bare suffix -> the set of qualified definitions sharing it.
        let mut suffix_to_qualified: BTreeMap<String, Vec<String>> = BTreeMap::new();
        for def in &defined {
            if let Some((prefix, suffix)) = def.rsplit_once("__") {
                if prefix.is_empty() || suffix.is_empty() || suffix == def.as_str() {
                    continue;
                }
                suffix_to_qualified
                    .entry(suffix.to_string())
                    .or_default()
                    .push(def.clone());
            }
        }

        let mut aliases = BTreeMap::new();
        for reference in &undefined {
            // Only bare references (no `__` joiner) that have no bare definition.
            if reference.contains("__") || defined.contains(reference) {
                continue;
            }
            if let Some(candidates) = suffix_to_qualified.get(reference) {
                // Only auto-alias when there is exactly one qualified definition;
                // ambiguity is investigated by hand, never silently routed.
                if candidates.len() == 1 {
                    aliases.insert(reference.clone(), candidates[0].clone());
                }
            }
        }
        Ok(aliases.into_iter().collect())
    }

    fn read_global_symbols(obj: &Path) -> Result<Vec<String>, String> {
        let output = nm_command()
            .arg("-g")
            .arg(obj)
            .output()
            .map_err(|e| format!("nm: {e}"))?;
        if !output.status.success() {
            return Ok(Vec::new());
        }
        // The leading-underscore prefix is a Mach-O convention. Only strip it
        // when the *output* objects are Mach-O — for cross-compiled ELF objects
        // (e.g. freestanding `x86_64-unknown-none` kernels) the symbols have no
        // prefix, and stripping would turn `__module_init_X` into
        // `_module_init_X`, breaking module-init discovery.
        let strip_macho_underscore =
            cfg!(target_os = "macos") && effective_target().os == simple_common::target::TargetOS::MacOS;
        Ok(String::from_utf8_lossy(&output.stdout)
            .lines()
            .filter_map(|line| line.split_whitespace().last())
            .map(|raw_name| {
                if strip_macho_underscore {
                    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
                } else {
                    raw_name.to_string()
                }
            })
            .collect())
    }

    fn read_defined_symbol_set(obj: &Path) -> Result<HashSet<String>, String> {
        Ok(Self::read_global_symbol_types(obj)?
            .into_iter()
            .filter(|(kind, _)| kind != "U")
            .map(|(_, name)| name)
            .collect())
    }

    fn read_undefined_symbol_set(obj: &Path) -> Result<HashSet<String>, String> {
        let output = nm_command()
            .arg("-g")
            .arg("-p")
            .arg(obj)
            .output()
            .map_err(|e| format!("nm undefined: {e}"))?;
        if !output.status.success() {
            return Ok(HashSet::new());
        }
        let mut symbols = HashSet::new();
        for line in String::from_utf8_lossy(&output.stdout).lines() {
            let parts: Vec<&str> = line.split_whitespace().collect();
            let raw_name = match parts.as_slice() {
                [sym_type, name] if matches!(*sym_type, "U" | "w" | "v") => Some(*name),
                [_addr, sym_type, name] if matches!(*sym_type, "U" | "w" | "v") => Some(*name),
                _ => None,
            };
            if let Some(raw_name) = raw_name {
                let name = if cfg!(target_os = "macos") {
                    raw_name.strip_prefix('_').unwrap_or(raw_name).to_string()
                } else {
                    raw_name.to_string()
                };
                symbols.insert(name);
            }
        }
        Ok(symbols)
    }

    fn is_libm_symbol(sym: &str) -> bool {
        matches!(
            sym,
            "acos"
                | "acosf"
                | "asin"
                | "asinf"
                | "atan"
                | "atan2"
                | "atan2f"
                | "atanf"
                | "ceil"
                | "ceilf"
                | "cos"
                | "cosf"
                | "exp"
                | "exp2"
                | "exp2f"
                | "expf"
                | "fabs"
                | "fabsf"
                | "floor"
                | "floorf"
                | "fmod"
                | "fmodf"
                | "log"
                | "log10"
                | "log10f"
                | "log2"
                | "log2f"
                | "logf"
                | "pow"
                | "powf"
                | "round"
                | "roundf"
                | "sin"
                | "sinf"
                | "sqrt"
                | "sqrtf"
                | "tan"
                | "tanf"
                | "trunc"
                | "truncf"
        )
    }

    fn is_runtime_math_symbol(sym: &str) -> bool {
        sym.starts_with("rt_math_") || matches!(sym, "rt_sin" | "rt_cos" | "rt_sqrt" | "rt_pow")
    }

    fn is_openssl_runtime_symbol(sym: &str) -> bool {
        matches!(sym, "rt_net_https_openssl_local_probe")
    }

    fn is_sqlite_runtime_symbol(sym: &str) -> bool {
        sym.starts_with("rt_sqlite_") || sym.starts_with("sqlite3_")
    }

    fn entry_objects_require_libm(object_paths: &[PathBuf]) -> Result<bool, String> {
        for input in object_paths {
            if Self::read_undefined_symbol_set(input)?
                .iter()
                .any(|sym| Self::is_libm_symbol(sym) || Self::is_runtime_math_symbol(sym))
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn entry_objects_require_openssl(object_paths: &[PathBuf]) -> Result<bool, String> {
        for input in object_paths {
            if Self::read_undefined_symbol_set(input)?
                .iter()
                .any(|sym| Self::is_openssl_runtime_symbol(sym))
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    fn entry_objects_require_sqlite(object_paths: &[PathBuf]) -> Result<bool, String> {
        for input in object_paths {
            if Self::read_undefined_symbol_set(input)?
                .iter()
                .any(|sym| Self::is_sqlite_runtime_symbol(sym))
            {
                return Ok(true);
            }
        }
        Ok(false)
    }

    pub(crate) fn runtime_retention_symbols(
        _object_paths: &[PathBuf],
        _main_o: &Path,
        init_o: Option<&PathBuf>,
        runtime_lib: &Path,
        _imports: &ModuleImports,
    ) -> Result<Vec<String>, String> {
        let runtime_defined = Self::read_defined_symbol_set(runtime_lib)?;
        let mut required = BTreeSet::new();

        // Strong runtime references in live function sections extract their own
        // archive members. Rooting every object relocation here defeats
        // --gc-sections by retaining optional backends referenced only by dead
        // functions. Keep only weak or indirect runtime entry points.
        for root in [
            "__simple_runtime_init",
            "__simple_runtime_shutdown",
            "rt_set_args",
            "rt_function_not_found",
            "rt_string_bytes",
        ] {
            if runtime_defined.contains(root) {
                required.insert(root.to_string());
            }
        }
        let security_loader = "rt_security_load_registry_sdn";
        if let Some(init) = init_o {
            if Self::read_undefined_symbol_set(init)?.contains(security_loader)
                && runtime_defined.contains(security_loader)
            {
                required.insert(security_loader.to_string());
            }
        }

        let roots: Vec<String> = required.into_iter().collect();
        if std::env::var("SIMPLE_TRACE_RUNTIME_ROOTS").is_ok() {
            eprintln!(
                "Runtime retention source: {} defined={}",
                runtime_lib.display(),
                runtime_defined.len()
            );
            eprintln!(
                "Runtime retention roots ({}): {}",
                roots.len(),
                roots.iter().take(120).cloned().collect::<Vec<_>>().join(", ")
            );
        }
        Ok(roots)
    }

    #[cfg(any(target_os = "linux", target_os = "freebsd"))]
    pub(crate) fn add_elf_undefined_roots(cmd: &mut std::process::Command, symbols: &[String]) {
        for sym in symbols {
            cmd.arg(format!("-Wl,-u,{sym}"));
        }
    }

    #[cfg(any(target_os = "linux", target_os = "freebsd"))]
    fn quote_linker_response_path(path: &Path) -> String {
        let raw = path.to_string_lossy();
        debug_assert!(
            !raw.contains(['\n', '\r']),
            "response file paths must not contain newlines: {}",
            path.display()
        );
        let escaped = raw.replace('\\', "\\\\").replace('"', "\\\"");
        format!("\"{escaped}\"")
    }

    #[cfg(any(target_os = "linux", target_os = "freebsd"))]
    fn write_linker_object_response_file(temp_dir: &Path, object_paths: &[PathBuf]) -> Result<PathBuf, String> {
        let rsp_path = temp_dir.join("spl_objects.rsp");
        let mut quoted_paths = Vec::with_capacity(object_paths.len());
        for obj in object_paths {
            let raw = obj.to_string_lossy();
            if raw.contains(['\n', '\r']) {
                return Err(format!("object path contains unsupported newline: {}", obj.display()));
            }
            quoted_paths.push(Self::quote_linker_response_path(obj));
        }
        let contents = quoted_paths.join("\n");
        std::fs::write(&rsp_path, format!("{contents}\n")).map_err(|e| format!("write object response file: {e}"))?;
        Ok(rsp_path)
    }

    #[cfg(target_os = "linux")]
    fn stage4_live_runtime_requests(
        temp_dir: &Path,
        object_paths: &[PathBuf],
        main_o: &Path,
        init_o: Option<&PathBuf>,
        alias_stub: &Path,
    ) -> Result<Vec<String>, String> {
        let mut inputs = Vec::with_capacity(object_paths.len() + 3);
        inputs.push(main_o.to_path_buf());
        if let Some(init) = init_o {
            inputs.push(init.clone());
        }
        inputs.extend_from_slice(object_paths);
        inputs.push(alias_stub.to_path_buf());
        let projection_dir = temp_dir.join("stage4_live");
        std::fs::create_dir_all(&projection_dir)
            .map_err(|err| format!("create Stage4 live projection directory: {err}"))?;
        let response = Self::write_linker_object_response_file(&projection_dir, &inputs)?;
        let live = temp_dir.join("stage4_live_entry.o");
        let cc = target_c_compiler(effective_target());
        let output = std::process::Command::new(&cc)
            .args([
                "-nostdlib",
                "-no-pie",
                "-Wl,-r",
                "-Wl,--gc-sections",
                "-Wl,-u,main",
                "-Wl,-u,spl_main",
            ])
            .arg(format!("@{}", response.display()))
            .arg("-o")
            .arg(&live)
            .output()
            .map_err(|err| format!("execute Stage4 live entry projection with {cc}: {err}"))?;
        if !output.status.success() {
            return Err(format!(
                "Stage4 live entry projection failed: {}",
                String::from_utf8_lossy(&output.stderr).trim()
            ));
        }
        let mut requested: Vec<String> = Self::read_undefined_symbol_set(&live)?
            .into_iter()
            .filter(|symbol| {
                symbol.starts_with("rt_")
                    || symbol.starts_with("spl_")
                    || matches!(
                        symbol.as_str(),
                        "panic"
                            | "stderr_write"
                            | "stderr_flush"
                            | "__simple_runtime_init"
                            | "__simple_runtime_shutdown"
                            | "__simple_call_module_inits"
                    )
            })
            .collect();
        requested.sort();
        if requested.is_empty() {
            return Err("Stage4 live entry projection produced no runtime requests".to_string());
        }
        Ok(requested)
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

    pub(crate) fn freestanding_simple_main_entry_symbol(
        object_paths: &[PathBuf],
        symbol_cache: &mut HashMap<PathBuf, Vec<String>>,
    ) -> Result<Option<String>, String> {
        let mut qualified_candidate: Option<String> = None;
        for obj in object_paths {
            for sym in Self::cached_global_symbols(symbol_cache, obj)? {
                if sym == "spl_main" {
                    return Ok(Some("spl_main".to_string()));
                }
                if sym.ends_with("__spl_main") && qualified_candidate.is_none() {
                    qualified_candidate = Some(sym.to_string());
                }
            }
        }
        Ok(qualified_candidate)
    }

    /// Compile the C++ main stub to an object file.
    pub(crate) fn compile_main_stub(&self, temp_dir: &Path) -> Result<PathBuf, String> {
        let main_cpp = temp_dir.join("_main_stub.cpp");
        let cxx = target_cxx_compiler(effective_target());
        let is_msvc = cxx.contains("clang-cl") || simple_common::platform::cc_detect::is_msvc_target(&cxx);

        let has_entry = self.entry_file.is_some();
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
#if defined(__APPLE__)
extern "C" {
    int __attribute__((weak)) spl_main(void) { return 0; }
    void __attribute__((weak)) rt_set_args(int, char**) {}
    void __attribute__((weak)) __simple_runtime_init(void) {}
    void __attribute__((weak)) __simple_runtime_shutdown(void) {}
    void __attribute__((weak)) __simple_call_module_inits(void) {}
}
#else
extern "C" {
    int __attribute__((weak)) spl_main(void);
    void __attribute__((weak)) rt_set_args(int argc, char** argv);
    void __attribute__((weak)) __simple_runtime_init(void);
    void __attribute__((weak)) __simple_runtime_shutdown(void);
    void __attribute__((weak)) __simple_call_module_inits(void);
}
#endif
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
                .args([
                    "-c",
                    "-Os",
                    "-ffunction-sections",
                    "-fdata-sections",
                    "-fno-asynchronous-unwind-tables",
                    "-fno-unwind-tables",
                    "-fno-stack-protector",
                    "-o",
                ])
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
        // Always emit the caller, even when this entry has no module init
        // functions. The generated main stub references
        // `__simple_call_module_inits`; ELF accepts that weak undefined symbol,
        // but Darwin's classic linker rejects it. An empty concrete owner keeps
        // the hosted link contract identical on every Unix platform.
        init_names.sort();
        init_names.dedup();

        let cross_target = effective_target();
        let cxx = target_cxx_compiler(cross_target);
        let is_clang_cl = cxx.contains("clang-cl");
        let use_llvm_backend = std::env::var("SIMPLE_BACKEND").as_deref() == Ok("llvm");
        let init_target_triple = if cross_target.is_host() {
            None
        } else {
            Self::freestanding_target_triple(cross_target)
        };

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
            let mut cmd = std::process::Command::new(&cxx);
            cmd.arg("/c")
                .arg("/O2")
                .arg("/Gy")
                .arg(format!("/Fo{}", init_o.display()));
            if let Some(triple) = init_target_triple {
                cmd.arg(format!("--target={}", triple));
            }
            match cross_target.arch {
                simple_common::target::TargetArch::Riscv64 if use_llvm_backend => {
                    cmd.arg("-march=rv64imac").arg("-mabi=lp64");
                }
                simple_common::target::TargetArch::Riscv64 => {
                    cmd.arg("-march=rv64gc").arg("-mabi=lp64d");
                }
                simple_common::target::TargetArch::Riscv32 => {
                    cmd.arg("-march=rv32imac").arg("-mabi=ilp32");
                }
                _ => {}
            }
            // Freestanding RISC-V kernels load high (e.g. 0x80200000); the init
            // caller takes the address of each __module_init_* via HI20/LO12, so
            // it must use the same medany code model as the kernel objects, or
            // those relocations overflow medlow's ±2GB-from-zero window.
            if matches!(
                cross_target.arch,
                simple_common::target::TargetArch::Riscv64 | simple_common::target::TargetArch::Riscv32
            ) {
                cmd.arg("-mcmodel=medany");
            }
            cmd.arg(&init_cpp)
                .status()
                .map_err(|e| format!("compile init_all: {e}"))?
        } else {
            let mut cmd = std::process::Command::new(&cxx);
            cmd.arg("-c")
                .arg("-Os")
                .arg("-ffunction-sections")
                .arg("-fdata-sections")
                .arg("-fno-asynchronous-unwind-tables")
                .arg("-fno-unwind-tables")
                .arg("-fno-stack-protector");
            if let Some(triple) = init_target_triple {
                cmd.arg(format!("--target={}", triple));
            }
            match cross_target.arch {
                simple_common::target::TargetArch::Riscv64 if use_llvm_backend => {
                    cmd.arg("-march=rv64imac").arg("-mabi=lp64");
                }
                simple_common::target::TargetArch::Riscv64 => {
                    cmd.arg("-march=rv64gc").arg("-mabi=lp64d");
                }
                simple_common::target::TargetArch::Riscv32 => {
                    cmd.arg("-march=rv32imac").arg("-mabi=ilp32");
                }
                _ => {}
            }
            // Match the kernel objects' medany code model (see HI20-overflow note
            // in the clang-cl arm above) so high-loaded freestanding RISC-V links.
            if matches!(
                cross_target.arch,
                simple_common::target::TargetArch::Riscv64 | simple_common::target::TargetArch::Riscv32
            ) {
                cmd.arg("-mcmodel=medany");
            }
            cmd.arg(&init_cpp)
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
        // Use the OS component of the resolved target to decide freestanding routing.
        // `self.config.target.is_some()` was previously used here but is incorrect:
        // it routes any --target (including hosted cross-compiles like
        // x86_64-unknown-linux-gnu) to the freestanding path, which emits
        // -nostdlib/-ffreestanding and skips the C runtime archive. Since
        // set_target_override() is always called alongside config.target, the
        // effective_target() OS already reflects the right value.
        let is_freestanding = cross_target.os == simple_common::target::TargetOS::None
            || cross_target.os == simple_common::target::TargetOS::SimpleOS;
        if is_freestanding {
            return self.link_objects_freestanding(object_paths, temp_dir, imports);
        }

        let inline_asm_o = inline_asm_emit::compile_inline_asm_c(temp_dir, None)?;
        let mut link_object_paths: Vec<PathBuf> = object_paths.to_vec();
        if let Some(obj) = inline_asm_o {
            link_object_paths.push(obj);
        }
        let object_paths = link_object_paths.as_slice();

        let main_o = self.compile_main_stub(temp_dir)?;
        let init_o = self.generate_init_caller(temp_dir, object_paths, None)?;
        let selected_runtime = self.selected_runtime_library(temp_dir)?;
        self.reject_unexpected_native_all(selected_runtime.as_ref())?;
        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        let selected_runtime = match selected_runtime {
            Some((runtime_lib, true)) => {
                let filtered = strip_llvm_constructors(&runtime_lib, temp_dir).map_err(|err| {
                    format!(
                        "failed to strip LLVM constructors from {}: {:?}",
                        runtime_lib.display(),
                        err
                    )
                })?;
                Some((filtered, true))
            }
            other => other,
        };
        #[cfg(target_os = "linux")]
        let stage4_c_providers = if self.is_authorized_stage4_compiler_entry() {
            build_stage4_cli_c_provider_archives(&temp_dir.join("stage4_c_providers"))?
        } else {
            Vec::new()
        };
        #[cfg(not(target_os = "linux"))]
        let stage4_c_providers: Vec<PathBuf> = Vec::new();
        let exact_stage4 = !stage4_c_providers.is_empty();
        if exact_stage4 && std::env::var("SIMPLE_NO_STUB_FALLBACK").as_deref() != Ok("1") {
            return Err("Stage4 exact provider profile requires SIMPLE_NO_STUB_FALLBACK=1".to_string());
        }
        let stage4_rust_runtime = if exact_stage4 {
            let runtime_path = self
                .config
                .runtime_path
                .as_ref()
                .ok_or_else(|| "Stage4 requires an explicit Rust runtime path".to_string())?;
            // Project from the staticlib, not the bare rlib. The staticlib
            // carries the Rust std/alloc and crate dependency closure needed
            // by retained runtime exports while the capsule localizes every
            // definition outside the requested ABI.
            Some(Self::stage4_rust_runtime_staticlib(runtime_path)?)
        } else {
            None
        };
        let mut backfill_providers = stage4_c_providers.clone();
        if let Some(rust_runtime) = stage4_rust_runtime.as_ref() {
            backfill_providers.push(rust_runtime.clone());
        }
        let compiler_backfill =
            self.prepare_stage4_compiler_backfill_archive(selected_runtime.as_ref(), &backfill_providers, temp_dir)?;
        #[cfg(target_os = "linux")]
        let stage4_profile = if exact_stage4 {
            let (core, is_native_all) = selected_runtime
                .as_ref()
                .ok_or_else(|| "Stage4 requires the fresh core-C runtime".to_string())?;
            if *is_native_all {
                return Err("Stage4 exact provider profile forbids native_all".to_string());
            }
            let compiler = compiler_backfill
                .as_ref()
                .ok_or_else(|| "Stage4 requires the dedicated compiler backfill".to_string())?;
            validate_stage4_cli_c_provider_archive_disjointness(core, compiler, &stage4_c_providers)?;

            let rust_runtime = stage4_rust_runtime.as_ref().expect("validated Stage4 Rust runtime");
            let mut provider_paths = vec![compiler.as_path(), core.as_path(), rust_runtime.as_path()];
            provider_paths.extend(stage4_c_providers.iter().map(PathBuf::as_path));
            let alias_stub = generate_stub_object(temp_dir, object_paths, &main_o, &provider_paths, imports)?;
            let requested =
                Self::stage4_live_runtime_requests(temp_dir, object_paths, &main_o, init_o.as_ref(), &alias_stub)?;

            let compiler_defined = Self::read_defined_symbol_set(compiler)?;
            let mut c_defined = Self::read_defined_symbol_set(core)?;
            for provider in &stage4_c_providers {
                c_defined.extend(Self::read_defined_symbol_set(provider)?);
            }
            let rust_defined = Self::read_defined_symbol_set(rust_runtime)?;
            let mut c_requested = Vec::new();
            let mut rust_requested = Vec::new();
            let mut missing = Vec::new();
            for symbol in requested {
                if compiler_defined.contains(&symbol) {
                    continue;
                }
                if c_defined.contains(&symbol) {
                    c_requested.push(symbol);
                } else if rust_defined.contains(&symbol) {
                    rust_requested.push(symbol);
                } else {
                    missing.push(symbol);
                }
            }
            if !missing.is_empty() {
                return Err(format!(
                    "Stage4 requested symbols have no archive owner: {}",
                    missing.join(", ")
                ));
            }
            let mut allowed_c_runtime: Vec<String> = c_defined
                .iter()
                .filter(|symbol| symbol.starts_with("rt_") || symbol.starts_with("spl_"))
                .cloned()
                .collect();
            allowed_c_runtime.sort();
            let rust_capsule = build_stage4_rust_runtime_projection_archive(
                rust_runtime,
                &rust_requested,
                &allowed_c_runtime,
                &temp_dir.join("stage4_rust_runtime"),
            )?;
            for dependency in Self::read_undefined_symbol_set(&rust_capsule)? {
                if c_defined.contains(&dependency) && !c_requested.contains(&dependency) {
                    c_requested.push(dependency);
                }
            }
            c_requested.sort();
            let c_capsule = build_stage4_runtime_capsule_archive(
                core,
                &stage4_c_providers,
                &c_requested,
                &temp_dir.join("stage4_runtime_capsule"),
            )?;
            Some((alias_stub, rust_capsule, c_capsule))
        } else {
            None
        };
        #[cfg(not(target_os = "linux"))]
        let stage4_profile: Option<(PathBuf, PathBuf, PathBuf)> = None;
        let has_native_all = selected_runtime
            .as_ref()
            .is_some_and(|(_, is_native_all)| *is_native_all);

        let cc = if has_native_all {
            target_cxx_compiler(cross_target)
        } else {
            target_c_compiler(cross_target)
        };
        let is_clang_cl = cc.contains("clang-cl");
        let is_msvc = simple_common::platform::cc_detect::is_msvc_target(&cc);
        let mut cmd = std::process::Command::new(&cc);
        if !is_msvc {
            cmd.arg("-fPIC");
        }

        #[cfg(target_os = "macos")]
        add_macos_base_link_args(&mut cmd);

        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        cmd.arg("-no-pie");

        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        if !exact_stage4 {
            cmd.arg("-Wl,-z,muldefs");
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
            #[cfg(any(target_os = "linux", target_os = "freebsd"))]
            {
                let rsp_path = Self::write_linker_object_response_file(temp_dir, object_paths)?;
                cmd.arg(format!("@{}", rsp_path.display()));
            }
            #[cfg(not(any(target_os = "linux", target_os = "freebsd")))]
            {
                let archive_path = temp_dir.join("libspl_objects.a");
                let ar_tool = find_archive_tool();

                const BATCH_SIZE: usize = 200;
                let mut ar_ok = true;
                for (i, chunk) in object_paths.chunks(BATCH_SIZE).enumerate() {
                    let status = archive_create_command(&ar_tool, &archive_path, chunk, i > 0, false)
                        .status()
                        .map_err(|e| format!("archive batch {i}: {e}"))?;
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
            }
        } else {
            for obj in object_paths {
                cmd.arg(obj);
            }
        }

        #[cfg(any(target_os = "linux", target_os = "freebsd"))]
        if exact_stage4 {
            let (stubs_o, rust_capsule, c_capsule) = stage4_profile.as_ref().expect("validated Stage4 profile");
            let backfill = compiler_backfill.as_ref().expect("validated Stage4 compiler backfill");
            let mut roots =
                Self::runtime_retention_symbols(object_paths, &main_o, init_o.as_ref(), rust_capsule, imports)?;
            roots.extend(Self::runtime_retention_symbols(
                object_paths,
                &main_o,
                init_o.as_ref(),
                c_capsule,
                imports,
            )?);
            roots.sort();
            roots.dedup();
            Self::add_elf_undefined_roots(&mut cmd, &roots);
            cmd.arg(stubs_o)
                .arg("-Wl,--start-group")
                .arg(backfill)
                .arg(rust_capsule)
                .arg(c_capsule)
                .arg("-Wl,--end-group");
        }

        if !exact_stage4 {
            if let Some(backfill) = compiler_backfill.as_ref() {
                cmd.arg(backfill);
            }
        }

        if !exact_stage4 {
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
                        if std::env::var("SIMPLE_NATIVE_FORCE_WHOLE_ARCHIVE").as_deref() == Ok("1") {
                            cmd.arg("-Wl,--whole-archive");
                            cmd.arg(runtime_lib);
                            cmd.arg("-Wl,--no-whole-archive");
                        } else {
                            let roots = Self::runtime_retention_symbols(
                                object_paths,
                                &main_o,
                                init_o.as_ref(),
                                runtime_lib,
                                imports,
                            )?;
                            Self::add_elf_undefined_roots(&mut cmd, &roots);
                            cmd.arg(runtime_lib);
                        }
                    }
                    if std::env::var("SIMPLE_BOOTSTRAP_STAGE4").as_deref() == Ok("1") {
                        let core_c_runtime = build_stage4_c_runtime_library(&temp_dir.join("stage4_core_c_runtime"))
                            .ok_or_else(|| "failed to build Stage 4 core-C runtime supplement".to_string())?;
                        cmd.arg(core_c_runtime);
                    }
                } else {
                    #[cfg(target_os = "macos")]
                    {
                        cmd.arg("-Wl,-force_load").arg(runtime_lib);
                    }
                    #[cfg(any(target_os = "linux", target_os = "freebsd"))]
                    {
                        let roots = Self::runtime_retention_symbols(
                            object_paths,
                            &main_o,
                            init_o.as_ref(),
                            runtime_lib,
                            imports,
                        )?;
                        Self::add_elf_undefined_roots(&mut cmd, &roots);
                        cmd.arg(runtime_lib);
                    }
                    #[cfg(all(not(target_os = "macos"), not(target_os = "linux"), not(target_os = "freebsd")))]
                    cmd.arg(runtime_lib);
                }
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
        let link_config = {
            #[cfg(target_os = "windows")]
            {
                if !is_clang_cl && !is_msvc {
                    simple_common::platform::link_config::PlatformLinkConfig::windows_mingw()
                } else {
                    simple_common::platform::link_config::PlatformLinkConfig::for_host()
                }
            }
            #[cfg(not(target_os = "windows"))]
            {
                simple_common::platform::link_config::PlatformLinkConfig::for_host()
            }
        };
        for path in &link_config.library_search_paths {
            cmd.arg(format!("-L{}", path));
        }
        let omit_unwind = cfg!(target_os = "linux")
            && selected_runtime
                .as_ref()
                .is_some_and(|(_, is_native_all)| !is_native_all)
            && self.runtime_bundle_prefers_core_lane();
        let omit_libm = cfg!(target_os = "linux")
            && selected_runtime
                .as_ref()
                .is_some_and(|(_, is_native_all)| !is_native_all)
            && self.runtime_bundle_prefers_core_lane()
            && !Self::entry_objects_require_libm(object_paths)?;
        let require_openssl = cfg!(target_os = "linux") && Self::entry_objects_require_openssl(object_paths)?;
        let omit_sqlite = cfg!(target_os = "linux")
            && selected_runtime
                .as_ref()
                .is_some_and(|(_, is_native_all)| !is_native_all)
            && !Self::entry_objects_require_sqlite(object_paths)?;
        if is_clang_cl {
            for lib in &link_config.libraries {
                if omit_unwind && *lib == "unwind" {
                    continue;
                }
                if omit_libm && *lib == "m" {
                    continue;
                }
                if omit_sqlite && *lib == "sqlite3" {
                    continue;
                }
                cmd.arg(format!("{}.lib", lib));
            }
        } else {
            #[cfg(target_os = "linux")]
            {
                cmd.arg("-Wl,--as-needed");
            }
            for lib in &link_config.libraries {
                if omit_unwind && *lib == "unwind" {
                    continue;
                }
                if omit_libm && *lib == "m" {
                    continue;
                }
                if omit_sqlite && *lib == "sqlite3" {
                    continue;
                }
                cmd.arg(format!("-l{}", lib));
            }
            if require_openssl {
                cmd.arg("-lssl").arg("-lcrypto");
            }
            if has_native_all {
                cmd.args(terminfo_link_args(cross_target));
            }
            #[cfg(target_os = "linux")]
            {
                cmd.arg("-Wl,--no-as-needed");
            }
        }
        #[cfg(target_os = "macos")]
        if has_native_all {
            add_macos_native_all_host_support(&mut cmd);
        }

        #[cfg(not(target_os = "windows"))]
        {
            if !exact_stage4 {
                let mut provider_paths = Vec::new();
                if let Some(backfill) = compiler_backfill.as_ref() {
                    provider_paths.push(backfill.as_path());
                }
                if let Some((runtime, _)) = selected_runtime.as_ref() {
                    provider_paths.push(runtime.as_path());
                }
                let stubs_o = generate_stub_object(temp_dir, object_paths, &main_o, &provider_paths, imports)?;
                cmd.arg(&stubs_o);
                #[cfg(any(target_os = "linux", target_os = "freebsd"))]
                if let Some((runtime_lib, _)) = selected_runtime.as_ref() {
                    // ponytail: ELF archives resolve left-to-right; stubs may reference runtime helpers.
                    cmd.arg(runtime_lib);
                }
            }
        }
        #[cfg(target_os = "windows")]
        if !is_msvc && !is_clang_cl {
            let mut provider_paths = Vec::new();
            if let Some(backfill) = compiler_backfill.as_ref() {
                provider_paths.push(backfill.as_path());
            }
            if let Some((runtime, _)) = selected_runtime.as_ref() {
                provider_paths.push(runtime.as_path());
            }
            let stubs_o = generate_stub_object(temp_dir, object_paths, &main_o, &provider_paths, &imports)?;
            cmd.arg(&stubs_o);
        }
        let strict_no_stub_fallback = std::env::var("SIMPLE_NO_STUB_FALLBACK").as_deref() == Ok("1");
        if !strict_no_stub_fallback {
            for flag in &link_config.unresolved_symbol_flags {
                cmd.arg(flag);
            }
        }
        #[cfg(target_os = "windows")]
        if is_clang_cl && !strict_no_stub_fallback {
            cmd.arg("/link").arg("/WHOLEARCHIVE").arg("/FORCE:MULTIPLE,UNRESOLVED");
        } else if is_msvc && !strict_no_stub_fallback {
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
            #[cfg(any(target_os = "linux", target_os = "freebsd"))]
            if self.config.strip {
                if let Some(objcopy) = find_objcopy_tool() {
                    let _ = std::process::Command::new(objcopy)
                        .arg("--remove-section=.comment")
                        .arg(&self.output)
                        .status();
                }
            }
            #[cfg(target_os = "windows")]
            if self.config.strip {
                normalize_windows_pe_metadata(&self.output)?;
            }
            if let Ok(meta) = std::fs::metadata(&self.output) {
                eprintln!("Linked: {} ({} KB) via {cc}", self.output.display(), meta.len() / 1024);
            }
            Ok(())
        } else {
            let stderr = String::from_utf8_lossy(&output_result.stderr);
            if selected_runtime
                .as_ref()
                .is_some_and(|(_, is_native_all)| !is_native_all)
                && self.runtime_bundle_prefers_core_lane()
            {
                Err(format!(
                    "link failed: {}\
\nnote: the selected core lane (`{}`) links `libsimple_runtime.a` only. \
If this entry depends on hosted-only runtime symbols, rebuild with `--runtime-bundle rust-hosted` \
(legacy aliases: `--runtime-bundle hosted` or `--runtime-bundle all`).",
                    stderr,
                    self.resolve_runtime_lane().display_name()
                ))
            } else {
                Err(format!("link failed: {}", stderr))
            }
        }
    }

    /// Link object files for a freestanding target (no OS, no libc).
    pub(crate) fn link_objects_freestanding(
        &self,
        object_paths: &[PathBuf],
        temp_dir: &Path,
        imports: &ModuleImports,
    ) -> Result<(), String> {
        let cross_target = effective_target();
        let triple = Self::freestanding_target_triple(cross_target)
            .ok_or_else(|| "unsupported freestanding target architecture".to_string())?;

        let use_llvm = std::env::var("SIMPLE_BACKEND").as_deref() == Ok("llvm");
        let riscv32_march_override = std::env::var("SIMPLE_RISCV32_MARCH").ok();
        let riscv32_mabi_override = std::env::var("SIMPLE_RISCV32_MABI").ok();
        let (march, mabi) = match cross_target.arch {
            simple_common::target::TargetArch::Riscv64 if use_llvm => ("-march=rv64imac", "-mabi=lp64"),
            simple_common::target::TargetArch::Riscv64 => ("-march=rv64gc", "-mabi=lp64d"),
            simple_common::target::TargetArch::Riscv32 => (
                riscv32_march_override.as_deref().unwrap_or("-march=rv32imac"),
                riscv32_mabi_override.as_deref().unwrap_or("-mabi=ilp32"),
            ),
            _ => ("", ""),
        };
        let inline_asm_o = inline_asm_emit::compile_inline_asm_c(temp_dir, Some((triple, march, mabi)))?;
        let mut link_object_paths: Vec<PathBuf> = object_paths.to_vec();
        if let Some(obj) = inline_asm_o {
            link_object_paths.push(obj);
        }
        let object_paths = link_object_paths.as_slice();
        let mut symbol_cache = HashMap::new();
        let init_o = self.generate_init_caller(temp_dir, object_paths, Some(&mut symbol_cache))?;
        let cc = find_c_compiler();

        let compiler_rt_builtins = find_compiler_rt_builtins(triple);
        let simpleos_user_runtime = Self::simpleos_user_runtime_paths(cross_target);
        let effective_linker_script = Self::resolve_freestanding_linker_script(
            self.config.linker_script.as_deref(),
            cross_target,
            &Self::simpleos_sysroot_dir(cross_target.arch),
        );
        if let Some(ref script) = effective_linker_script {
            if !script.is_file() {
                return Err(format!("missing linker script: {}", script.display()));
            }
        }

        let mut boot_objects: Vec<PathBuf> = Vec::new();
        let mut boot_compile_failures: usize = 0;
        if let Some(ref entry) = self.entry_file {
            let skip_boot_autodiscovery = cross_target.arch == simple_common::target::TargetArch::Riscv64
                && entry
                    .file_name()
                    .and_then(|name| name.to_str())
                    .map(|name| name.starts_with("ghdl_boot_info"))
                    .unwrap_or(false);
            let rv64_desktop_service_boot = cross_target.arch == simple_common::target::TargetArch::Riscv64
                && entry
                    .file_name()
                    .and_then(|name| name.to_str())
                    .map(|name| name == "desktop_service_entry.spl")
                    .unwrap_or(false);
            let boot_dir = entry.parent().unwrap_or(std::path::Path::new(".")).join("boot");
            let debug_boot_sources = self.config.verbose || std::env::var("SIMPLE_LINKER_DEBUG").is_ok();
            if skip_boot_autodiscovery && debug_boot_sources {
                eprintln!("  Boot autodiscovery skipped for {}", entry.display());
            }
            let proof_runtime_stem = "ghdl_boot_info_runtime";
            if boot_dir.is_dir() {
                if debug_boot_sources {
                    eprintln!("  Boot directory: {}", boot_dir.display());
                }
                let asm_compilers: Vec<String> = {
                    let mut v = vec![];
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
                    if !v.contains(&cc) {
                        v.push(cc.clone());
                    }
                    v
                };
                for ext in &["S", "s"] {
                    if let Ok(entries) = std::fs::read_dir(&boot_dir) {
                        for de in entries.flatten() {
                            let path = de.path();
                            if path.extension().and_then(|e| e.to_str()) == Some(ext) {
                                if skip_boot_autodiscovery {
                                    continue;
                                }
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
                                                if debug_boot_sources {
                                                    eprintln!("  Boot ASM source: {}", path.display());
                                                }
                                                assembled = true;
                                                break;
                                            } else {
                                                last_code = r.status.code();
                                                last_stderr = String::from_utf8_lossy(&r.stderr).into_owned();
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
                            if skip_boot_autodiscovery && stem != proof_runtime_stem {
                                continue;
                            }
                            let minimal_boot = std::env::var("SIMPLE_BOOT_MINIMAL").is_ok();
                            let ssh_live_boot = std::env::var("SIMPLE_SSH_LIVE_BUILD_MARKER").is_ok();
                            if rv64_desktop_service_boot
                                && stem != "full_networking_runtime"
                                && stem != "curve25519_ring_helper"
                                && stem != "ed25519_scalar_helper"
                                && stem != "ed25519_sha512_helper"
                                && stem != "tls13_aes256_gcm_helper"
                                && stem != "tls13_sha256_helper"
                                && stem != "ed25519_verify_helper"
                            {
                                continue;
                            }
                            if ssh_live_boot && stem == "baremetal_stubs" {
                                continue;
                            }
                            if minimal_boot
                                && !skip_boot_autodiscovery
                                && stem != "baremetal_stubs"
                                && stem != "freestanding_runtime"
                                && !(ssh_live_boot && stem == "full_networking_runtime")
                                && stem != "curve25519_ring_helper"
                                && stem != "ed25519_scalar_helper"
                                && stem != "ed25519_sha512_helper"
                                && stem != "tls13_aes256_gcm_helper"
                                && stem != "tls13_sha256_helper"
                                && stem != "ed25519_verify_helper"
                            {
                                continue;
                            }
                            let out = temp_dir.join(format!("_boot_{}.o", stem));
                            let mut compiled = false;
                            let mut last_stderr = String::new();
                            let mut last_code: Option<i32> = None;
                            for c_cc in &asm_compilers {
                                let mut c_cmd = std::process::Command::new(c_cc);
                                c_cmd
                                    .args([
                                        "-c",
                                        "-ffreestanding",
                                        "-nostdlib",
                                        "-fno-pie",
                                        "-ffunction-sections",
                                        "-fdata-sections",
                                        "-o",
                                    ])
                                    .arg(&out)
                                    .arg(&path)
                                    .arg(format!("--target={}", triple));
                                if stem == "curve25519_ring_helper"
                                    || stem == "ed25519_scalar_helper"
                                    || stem == "ed25519_verify_helper"
                                    || triple.contains("x86_64")
                                {
                                    let cwd = std::env::current_dir().unwrap_or_else(|_| std::path::PathBuf::from("."));
                                    let ring_include = cwd.join("src/compiler_rust/vendor/ring/include");
                                    let ring_root = cwd.join("src/compiler_rust/vendor/ring");
                                    let ring_pregenerated = cwd.join("src/compiler_rust/vendor/ring/pregenerated");
                                    c_cmd
                                        .arg("-DOPENSSL_NO_ASM")
                                        .arg("-DRING_CORE_NOSTDLIBINC")
                                        .arg("-I")
                                        .arg(ring_include)
                                        .arg("-I")
                                        .arg(ring_root)
                                        .arg("-I")
                                        .arg(ring_pregenerated);
                                    if triple.contains("x86_64") {
                                        c_cmd.arg("-mno-red-zone");
                                    }
                                }
                                if !march.is_empty() {
                                    c_cmd.args([march, mabi, "-mcmodel=medany"]);
                                }
                                match c_cmd.output() {
                                    Ok(r) => {
                                        if r.status.success() {
                                            boot_objects.push(out.clone());
                                            if debug_boot_sources {
                                                eprintln!("  Boot C source: {}", path.display());
                                            }
                                            compiled = true;
                                            break;
                                        }
                                        last_code = r.status.code();
                                        last_stderr = String::from_utf8_lossy(&r.stderr).into_owned();
                                    }
                                    Err(e) => {
                                        last_stderr = format!("spawn error: {}", e);
                                    }
                                }
                            }
                            if !compiled {
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
                                    "  ERROR: failed to compile {} (exit={:?})\n--- stderr tail ---\n{}\n--- end stderr ---",
                                    path.display(),
                                    last_code,
                                    tail
                                );
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
                if debug_boot_sources {
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
                        .is_ok_and(|o| o.status.success())
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

        let freestanding_stub_obj =
            generate_stub_object_freestanding(temp_dir, object_paths, &boot_objects, triple, march, mabi)?;
        let weak_boot_defsyms = Self::freestanding_weak_boot_defsyms(object_paths, &boot_objects, imports)?;
        if !weak_boot_defsyms.is_empty() {
            eprintln!(
                "Freestanding weak boot alias override: {} symbol(s)",
                weak_boot_defsyms.len()
            );
        }
        // Bridge module-qualified cross-module references onto the bare symbol
        // names that `@export`/ambiguous definitions actually emit.
        let qualified_bare_defsyms = Self::freestanding_qualified_to_bare_defsyms(object_paths, &boot_objects)?;
        if !qualified_bare_defsyms.is_empty() {
            eprintln!(
                "Freestanding qualified->bare alias bridge: {} symbol(s)",
                qualified_bare_defsyms.len()
            );
        }
        // Reverse bridge: an undefined bare reference onto a unique qualified
        // definition sharing its suffix (e.g. `char_from_code` ->
        // `lib__common__string_core__char_from_code`).
        let bare_qualified_defsyms = Self::freestanding_bare_to_qualified_defsyms(object_paths, &boot_objects)?;
        if !bare_qualified_defsyms.is_empty() {
            eprintln!(
                "Freestanding bare->qualified alias bridge: {} symbol(s)",
                bare_qualified_defsyms.len()
            );
        }

        let mut cmd = if let Some(ref lld_path) = use_direct_lld {
            let mut c = std::process::Command::new(lld_path);
            c.arg("--gc-sections");
            if let Some(ref ls) = effective_linker_script {
                c.arg(format!("-T{}", ls.display()));
            }
            for (raw, target) in &weak_boot_defsyms {
                c.arg(format!("--defsym={}={}", raw, target));
            }
            for (raw, target) in &qualified_bare_defsyms {
                c.arg(format!("--defsym={}={}", raw, target));
            }
            for (raw, target) in &bare_qualified_defsyms {
                c.arg(format!("--defsym={}={}", raw, target));
            }
            c.arg("-o").arg(&self.output);
            if let Some((ref crt0, _, _)) = simpleos_user_runtime {
                c.arg(crt0);
            }
            for boot_obj in &boot_objects {
                c.arg(boot_obj);
            }
            for obj in &ordered_objects {
                c.arg(obj.as_os_str());
            }
            if let Some(ref init) = init_o {
                c.arg(init);
            }
            if let Some(ref builtins) = compiler_rt_builtins {
                c.arg(builtins);
            }
            if let Some(ref stub_o) = freestanding_stub_obj {
                c.arg(stub_o);
            }
            if let Some((_, ref runtime, ref libc)) = simpleos_user_runtime {
                c.arg(runtime);
                c.arg(libc);
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
            c.arg("-Wl,--gc-sections");
            if let Some(ref ls) = effective_linker_script {
                c.arg(format!("-T{}", ls.display()));
            }
            for (raw, target) in &weak_boot_defsyms {
                c.arg(format!("-Wl,--defsym={}={}", raw, target));
            }
            for (raw, target) in &qualified_bare_defsyms {
                c.arg(format!("-Wl,--defsym={}={}", raw, target));
            }
            for (raw, target) in &bare_qualified_defsyms {
                c.arg(format!("-Wl,--defsym={}={}", raw, target));
            }
            c.arg("-o").arg(&self.output);
            if let Some((ref crt0, _, _)) = simpleos_user_runtime {
                c.arg(crt0);
            }
            for boot_obj in &boot_objects {
                c.arg(boot_obj);
            }
            for obj in &ordered_objects {
                c.arg(obj.as_os_str());
            }
            if let Some(ref init) = init_o {
                c.arg(init);
            }
            if let Some(ref builtins) = compiler_rt_builtins {
                c.arg(builtins);
            }
            if let Some(ref stub_o) = freestanding_stub_obj {
                c.arg(stub_o);
            }
            if let Some((_, ref runtime, ref libc)) = simpleos_user_runtime {
                c.arg(runtime);
                c.arg(libc);
            }
            c
        };

        let has_boot_entry32 = if !boot_objects.is_empty() {
            boot_objects.iter().any(|obj| {
                Self::cached_global_symbols(&mut symbol_cache, obj)
                    .map(|symbols| symbols.iter().any(|sym| sym == "_entry32"))
                    .unwrap_or(false)
            })
        } else {
            false
        };
        if has_boot_entry32 {
            let entry_flag = if use_direct_lld.is_some() {
                "--entry=_entry32"
            } else {
                "-Wl,--entry=_entry32"
            };
            cmd.arg(entry_flag);
        }

        let has_explicit_start = !has_boot_entry32
            && object_paths.iter().any(|obj| {
                Self::cached_global_symbols(&mut symbol_cache, obj)
                    .map(|symbols| symbols.iter().any(|sym| sym == "_start" || sym.ends_with("___start")))
                    .unwrap_or(false)
            });
        if has_explicit_start {
            let entry_flag = if use_direct_lld.is_some() {
                "--entry=_start"
            } else {
                "-Wl,--entry=_start"
            };
            cmd.arg(entry_flag);
        }

        // Scan for mangled entry symbols -> create defsym aliases.
        {
            let has_boot = !boot_objects.is_empty();
            let mut best_raw_start: Option<String> = None;
            let mut fallback_raw_start: Option<String> = None;
            let mut best_spl_start: Option<String> = None;
            let mut fallback_spl_start: Option<String> = None;

            if let Some(ref entry) = self.entry_file {
                let entry_str = entry.to_string_lossy();
                let stem = entry_str.trim_start_matches('/').trim_end_matches(".spl");
                let mangled_stem = stem.replace('/', "__");
                let raw_start_candidate = format!("{}___start", mangled_stem);
                let spl_start_candidate = format!("{}__spl_start", mangled_stem);
                'entry_search: for obj in object_paths {
                    for sym in Self::cached_global_symbols(&mut symbol_cache, obj)? {
                        if *sym == raw_start_candidate {
                            best_raw_start = Some(sym.to_string());
                        } else if *sym == spl_start_candidate {
                            best_spl_start = Some(sym.to_string());
                        }
                        if best_raw_start.is_some() && best_spl_start.is_some() {
                            break 'entry_search;
                        }
                    }
                }
            }

            if best_raw_start.is_none() || best_spl_start.is_none() {
                for obj in object_paths {
                    for sym in Self::cached_global_symbols(&mut symbol_cache, obj)? {
                        if sym.ends_with("___start") && sym != "_start" && sym != "spl_start" {
                            let neg_match = arch_neg_filters.iter().any(|f| sym.contains(f));
                            if neg_match {
                                continue;
                            }
                            let pos_match = arch_filters.iter().any(|f| sym.contains(f));
                            if pos_match {
                                if best_raw_start.is_none() {
                                    best_raw_start = Some(sym.to_string());
                                }
                            } else if fallback_raw_start.is_none() {
                                fallback_raw_start = Some(sym.to_string());
                            }
                        } else if sym.ends_with("__spl_start") && sym != "_start" && sym != "spl_start" {
                            let neg_match = arch_neg_filters.iter().any(|f| sym.contains(f));
                            if neg_match {
                                continue;
                            }
                            let pos_match = arch_filters.iter().any(|f| sym.contains(f));
                            if pos_match {
                                if best_spl_start.is_none() {
                                    best_spl_start = Some(sym.to_string());
                                }
                            } else if fallback_spl_start.is_none() {
                                fallback_spl_start = Some(sym.to_string());
                            }
                        }
                    }
                }
            }
            let raw_start_alias = best_raw_start.clone().or(fallback_raw_start.clone());
            let spl_start_alias = best_spl_start.clone().or(fallback_spl_start.clone());
            let simple_main_alias = if !has_boot_entry32 && raw_start_alias.is_none() && spl_start_alias.is_none() {
                Self::freestanding_simple_main_entry_symbol(object_paths, &mut symbol_cache)?
            } else {
                None
            };
            let primary_entry_alias = raw_start_alias.clone().or(simple_main_alias.clone());
            let has_simpleos_crt0 = simpleos_user_runtime.is_some();

            if !has_boot_entry32 {
                if let Some(sym) = primary_entry_alias.clone() {
                    if has_simpleos_crt0 {
                        if use_direct_lld.is_some() {
                            cmd.arg(format!("--defsym=main={}", sym));
                            cmd.arg("--entry=_start");
                        } else {
                            cmd.arg(format!("-Wl,--defsym=main={}", sym));
                            cmd.arg("-Wl,--entry=_start");
                        }
                    } else if use_direct_lld.is_some() {
                        cmd.arg(format!("--defsym=_start={}", sym));
                        cmd.arg("--entry=_start");
                    } else {
                        cmd.arg(format!("-Wl,--defsym=_start={}", sym));
                        cmd.arg("-Wl,--entry=_start");
                    }
                }
            }
            if let Some(sym) = primary_entry_alias.clone().or(spl_start_alias.clone()) {
                if use_direct_lld.is_some() {
                    cmd.arg(format!("--defsym=__simple_entry_start={}", sym));
                } else {
                    cmd.arg(format!("-Wl,--defsym=__simple_entry_start={}", sym));
                }
            }
            if let Some(sym) = spl_start_alias {
                if use_direct_lld.is_some() {
                    cmd.arg(format!("--defsym=spl_start={}", sym));
                } else {
                    cmd.arg(format!("-Wl,--defsym=spl_start={}", sym));
                }
            } else if !has_boot {
                // No boot support object depends on raw spl_start in this case.
                // Leave the alias unset when only _start is needed.
            } else if let Some(sym) = raw_start_alias {
                if use_direct_lld.is_some() {
                    cmd.arg(format!("--defsym=spl_start={}", sym));
                } else {
                    cmd.arg(format!("-Wl,--defsym=spl_start={}", sym));
                }
            }
        }

        if use_direct_lld.is_some() {
            cmd.arg("-z").arg("muldefs");
            if std::env::var("SIMPLE_ALLOW_FREESTANDING_STUBS").as_deref() == Ok("1") {
                cmd.arg("--unresolved-symbols=ignore-all");
            }
            if self.config.strip {
                cmd.arg("-s");
            }
        } else {
            cmd.arg("-Wl,-z,muldefs");
            if std::env::var("SIMPLE_ALLOW_FREESTANDING_STUBS").as_deref() == Ok("1") {
                cmd.arg("-Wl,--unresolved-symbols=ignore-all");
            }
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
                            .is_ok_and(|o| o.status.success())
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

#[cfg(target_os = "windows")]
pub(crate) fn normalize_windows_pe_metadata(path: &Path) -> Result<(), String> {
    use std::io::{Read, Seek, SeekFrom, Write};

    let mut file = std::fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(path)
        .map_err(|e| format!("open PE for metadata normalization {}: {e}", path.display()))?;

    let len = file
        .metadata()
        .map_err(|e| format!("metadata for PE {}: {e}", path.display()))?
        .len();
    if len < 0x100 {
        return Err(format!("PE too small for metadata normalization: {}", path.display()));
    }

    file.seek(SeekFrom::Start(0x3c))
        .map_err(|e| format!("seek PE header pointer: {e}"))?;
    let mut pe_offset_bytes = [0u8; 4];
    file.read_exact(&mut pe_offset_bytes)
        .map_err(|e| format!("read PE header pointer: {e}"))?;
    let pe_offset = u32::from_le_bytes(pe_offset_bytes) as u64;
    if pe_offset + 24 + 68 > len {
        return Err(format!("invalid PE header offset in {}", path.display()));
    }

    file.seek(SeekFrom::Start(pe_offset))
        .map_err(|e| format!("seek PE signature: {e}"))?;
    let mut sig = [0u8; 4];
    file.read_exact(&mut sig)
        .map_err(|e| format!("read PE signature: {e}"))?;
    if sig != *b"PE\0\0" {
        return Err(format!("missing PE signature in {}", path.display()));
    }

    // COFF TimeDateStamp and PE OptionalHeader.CheckSum are generated by the
    // linker and vary between otherwise identical stripped Windows binaries.
    file.seek(SeekFrom::Start(pe_offset + 8))
        .map_err(|e| format!("seek COFF timestamp: {e}"))?;
    file.write_all(&[0, 0, 0, 0])
        .map_err(|e| format!("zero COFF timestamp: {e}"))?;

    file.seek(SeekFrom::Start(pe_offset + 24 + 64))
        .map_err(|e| format!("seek PE checksum: {e}"))?;
    file.write_all(&[0, 0, 0, 0])
        .map_err(|e| format!("zero PE checksum: {e}"))?;

    Ok(())
}

#[cfg(test)]
mod linker_tests {
    use super::*;
    use crate::pipeline::native_project::tools::hosted_linux_cross_compiler;
    use simple_common::target::{Target, TargetArch, TargetOS};

    #[cfg(target_os = "macos")]
    #[test]
    fn macos_native_all_link_args_dead_strip_and_retain_metal_support() {
        let mut command = std::process::Command::new("clang++");
        add_macos_base_link_args(&mut command);
        add_macos_native_all_host_support(&mut command);
        let args = command
            .get_args()
            .map(|arg| arg.to_string_lossy().into_owned())
            .collect::<Vec<_>>();

        assert!(args.iter().any(|arg| arg == "-Wl,-dead_strip"));
        assert!(args.iter().any(|arg| arg == "-lc++"));
        assert!(args.windows(2).any(|pair| pair == ["-framework", "Metal"]));
    }

    #[test]
    fn hosted_linux_cross_compilers_select_gnu_toolchains() {
        assert_eq!(
            hosted_linux_cross_compiler(Target::new(TargetArch::Aarch64, TargetOS::Linux), false),
            Some("aarch64-linux-gnu-gcc")
        );
        assert_eq!(
            hosted_linux_cross_compiler(Target::new(TargetArch::Aarch64, TargetOS::Linux), true),
            Some("aarch64-linux-gnu-g++")
        );
        assert_eq!(
            hosted_linux_cross_compiler(Target::new(TargetArch::Riscv64, TargetOS::Linux), false),
            Some("riscv64-linux-gnu-gcc")
        );
        assert_eq!(
            hosted_linux_cross_compiler(Target::new(TargetArch::Riscv64, TargetOS::Linux), true),
            Some("riscv64-linux-gnu-g++")
        );
        assert_eq!(
            hosted_linux_cross_compiler(Target::new(TargetArch::Arm, TargetOS::Linux), false),
            Some("arm-linux-gnueabihf-gcc")
        );
    }

    #[test]
    fn hosted_linux_cross_compilers_leave_host_and_freestanding_alone() {
        assert_eq!(hosted_linux_cross_compiler(Target::host(), false), None);
        assert_eq!(
            hosted_linux_cross_compiler(Target::new(TargetArch::Aarch64, TargetOS::None), false),
            None
        );
    }

    #[test]
    fn freestanding_target_triple_keeps_none_and_simpleos_mappings() {
        assert_eq!(
            NativeProjectBuilder::freestanding_target_triple(Target::new(TargetArch::Riscv64, TargetOS::None)),
            Some("riscv64-unknown-elf")
        );
        assert_eq!(
            NativeProjectBuilder::freestanding_target_triple(Target::new(TargetArch::Aarch64, TargetOS::SimpleOS)),
            Some("aarch64-none-elf")
        );
        assert_eq!(
            NativeProjectBuilder::freestanding_target_triple(Target::new(TargetArch::Aarch64, TargetOS::Linux)),
            None
        );
    }

    #[cfg(target_os = "windows")]
    #[test]
    fn normalize_windows_pe_metadata_zeroes_timestamp_and_checksum() {
        let temp = tempfile::tempdir().unwrap();
        let path = temp.path().join("test.exe");
        let mut bytes = vec![0u8; 512];
        bytes[0x3c..0x40].copy_from_slice(&0x80u32.to_le_bytes());
        bytes[0x80..0x84].copy_from_slice(b"PE\0\0");
        bytes[0x88..0x8c].copy_from_slice(&0x12345678u32.to_le_bytes());
        bytes[0x80 + 24 + 64..0x80 + 24 + 68].copy_from_slice(&0x87654321u32.to_le_bytes());
        std::fs::write(&path, bytes).unwrap();

        normalize_windows_pe_metadata(&path).unwrap();

        let normalized = std::fs::read(&path).unwrap();
        assert_eq!(&normalized[0x88..0x8c], &[0, 0, 0, 0]);
        assert_eq!(&normalized[0x80 + 24 + 64..0x80 + 24 + 68], &[0, 0, 0, 0]);
    }

    #[cfg(any(target_os = "linux", target_os = "freebsd"))]
    #[test]
    fn write_linker_object_response_file_quotes_each_object_path() {
        let temp = tempfile::tempdir().unwrap();
        let object_paths = vec![
            temp.path().join("plain.o"),
            temp.path().join("with space.o"),
            temp.path().join("quote\"slash\\name.o"),
        ];

        let rsp_path = NativeProjectBuilder::write_linker_object_response_file(temp.path(), &object_paths).unwrap();
        let contents = std::fs::read_to_string(rsp_path).unwrap();

        assert_eq!(contents.lines().count(), object_paths.len());
        assert!(contents
            .lines()
            .all(|line| line.starts_with('"') && line.ends_with('"')));
        assert!(contents.contains(&NativeProjectBuilder::quote_linker_response_path(&object_paths[1])));
        assert!(contents.contains(&NativeProjectBuilder::quote_linker_response_path(&object_paths[2])));
    }

    #[cfg(any(target_os = "linux", target_os = "freebsd"))]
    #[test]
    fn write_linker_object_response_file_rejects_newlines() {
        let temp = tempfile::tempdir().unwrap();
        let object_paths = vec![PathBuf::from("bad\nname.o")];

        let err = NativeProjectBuilder::write_linker_object_response_file(temp.path(), &object_paths).unwrap_err();

        assert!(err.contains("unsupported newline"));
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn link_inputs_require_libm_detects_math_symbols_only_when_referenced() {
        let temp = tempfile::tempdir().unwrap();
        let plain_c = temp.path().join("plain.c");
        let math_c = temp.path().join("math.c");
        let plain_o = temp.path().join("plain.o");
        let math_o = temp.path().join("math.o");

        std::fs::write(&plain_c, "int plain(void) { return 1; }\n").unwrap();
        std::fs::write(
            &math_c,
            "extern double sqrt(double); double mathy(double x) { return sqrt(x); }\n",
        )
        .unwrap();

        let plain_status = std::process::Command::new("cc")
            .args(["-c", "-O0"])
            .arg(&plain_c)
            .arg("-o")
            .arg(&plain_o)
            .status()
            .unwrap();
        assert!(plain_status.success());

        let math_status = std::process::Command::new("cc")
            .args(["-c", "-O0", "-fno-builtin-sqrt"])
            .arg(&math_c)
            .arg("-o")
            .arg(&math_o)
            .status()
            .unwrap();
        assert!(math_status.success());

        assert!(!NativeProjectBuilder::entry_objects_require_libm(&[plain_o]).unwrap());
        assert!(NativeProjectBuilder::entry_objects_require_libm(&[math_o]).unwrap());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn link_inputs_require_openssl_detects_https_probe_only_when_referenced() {
        let temp = tempfile::tempdir().unwrap();
        let plain_c = temp.path().join("plain.c");
        let https_c = temp.path().join("https.c");
        let plain_o = temp.path().join("plain.o");
        let https_o = temp.path().join("https.o");

        std::fs::write(&plain_c, "int plain(void) { return 1; }\n").unwrap();
        std::fs::write(
            &https_c,
            "extern long long rt_net_https_openssl_local_probe(void); long long httpsy(void) { return rt_net_https_openssl_local_probe(); }\n",
        )
        .unwrap();

        let plain_status = std::process::Command::new("cc")
            .args(["-c", "-O0"])
            .arg(&plain_c)
            .arg("-o")
            .arg(&plain_o)
            .status()
            .unwrap();
        assert!(plain_status.success());

        let https_status = std::process::Command::new("cc")
            .args(["-c", "-O0"])
            .arg(&https_c)
            .arg("-o")
            .arg(&https_o)
            .status()
            .unwrap();
        assert!(https_status.success());

        assert!(!NativeProjectBuilder::entry_objects_require_openssl(&[plain_o]).unwrap());
        assert!(NativeProjectBuilder::entry_objects_require_openssl(&[https_o]).unwrap());
    }

    #[cfg(target_os = "linux")]
    #[test]
    fn link_inputs_require_sqlite_detects_sqlite_runtime_symbols_only_when_referenced() {
        let temp = tempfile::tempdir().unwrap();
        let plain_c = temp.path().join("plain.c");
        let sqlite_c = temp.path().join("sqlite.c");
        let plain_o = temp.path().join("plain.o");
        let sqlite_o = temp.path().join("sqlite.o");

        std::fs::write(&plain_c, "int plain(void) { return 1; }\n").unwrap();
        std::fs::write(
            &sqlite_c,
            "extern long long rt_sqlite_open(void); long long db(void) { return rt_sqlite_open(); }\n",
        )
        .unwrap();

        let plain_status = std::process::Command::new("cc")
            .args(["-c", "-O0"])
            .arg(&plain_c)
            .arg("-o")
            .arg(&plain_o)
            .status()
            .unwrap();
        assert!(plain_status.success());

        let sqlite_status = std::process::Command::new("cc")
            .args(["-c", "-O0"])
            .arg(&sqlite_c)
            .arg("-o")
            .arg(&sqlite_o)
            .status()
            .unwrap();
        assert!(sqlite_status.success());

        assert!(!NativeProjectBuilder::entry_objects_require_sqlite(&[plain_o]).unwrap());
        assert!(NativeProjectBuilder::entry_objects_require_sqlite(&[sqlite_o]).unwrap());
    }
}
