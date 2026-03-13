//! Platform-specific linking configuration.
//!
//! Single source of truth for per-OS library lists, search paths,
//! stub generation strategies, and linker flags. Extracted from
//! scattered `#[cfg(target_os)]` blocks in `native_project.rs`
//! and `native_binary.rs` following MDSOC L0 Common principles.

use crate::target::{Target, TargetArch, TargetOS};

/// Strategy for generating stubs for unresolved symbols at link time.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StubStrategy {
    /// Linux ELF: `.weak <sym>` — real definitions take precedence.
    Weak,
    /// macOS Mach-O: `.weak_definition <sym>`.
    WeakDefinition,
    /// FreeBSD ELF: `.globl <sym>` strong stub + `--allow-multiple-definition`.
    StrongWithAllowMultiple,
    /// Windows: no assembly stubs — use linker `/FORCE:UNRESOLVED` or
    /// `__attribute__((weak))` via MinGW.
    None,
}

/// How the main stub declares weak externals.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MainStubVariant {
    /// GCC/Clang `__attribute__((weak))` — Linux, macOS, FreeBSD, MinGW.
    WeakAttribute,
    /// MSVC `#pragma comment(linker, "/ALTERNATENAME:...")`.
    MsvcAlternateName,
}

/// Whole-archive strategy for forcing all symbols into the binary.
#[derive(Debug, Clone)]
pub enum WholeArchiveStyle {
    /// macOS: `-Wl,-force_load,<path>`.
    ForceLoad,
    /// ELF (Linux, FreeBSD, MinGW): `-Wl,--whole-archive <path> -Wl,--no-whole-archive`.
    GnuWholeArchive,
    /// MSVC-compatible linker: `/WHOLEARCHIVE:<path>` (via `-Wl,` or `-Xlinker`).
    MsvcWholeArchive,
}

/// Archive tool fallback strategy when `ar` fails.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ArFallback {
    /// macOS: fall back to `libtool -static`.
    Libtool,
    /// No fallback — fail immediately.
    None,
}

/// Per-OS linking configuration for native project builds.
#[derive(Debug, Clone)]
pub struct PlatformLinkConfig {
    /// Libraries to link (e.g., `["pthread", "dl", "m"]`).
    pub libraries: Vec<&'static str>,
    /// Additional library search paths (e.g., `["/usr/local/lib"]`).
    pub library_search_paths: Vec<&'static str>,
    /// System shared libraries to scan for defined symbols
    /// (to avoid generating stubs for them).
    pub system_scan_libs: Vec<&'static str>,
    /// `nm` flags for scanning system libraries.
    pub nm_flags: Vec<&'static str>,
    /// Strategy for generating stub functions.
    pub stub_strategy: StubStrategy,
    /// Extra characters valid in assembly labels (beyond alphanumerics and `_`).
    pub asm_label_extra_chars: Vec<char>,
    /// Linker flags for handling unresolved symbols after stubs.
    pub unresolved_symbol_flags: Vec<&'static str>,
    /// Whether to disable PIE (position-independent executable).
    pub disable_pie: bool,
    /// Extra linker flags passed early (e.g., macOS `-Wl,-ld_classic`).
    pub extra_link_flags: Vec<&'static str>,
    /// How to include all symbols from an archive (whole-archive).
    pub whole_archive_style: WholeArchiveStyle,
    /// Extra flags after whole-archive (e.g., macOS `-Wl,-no_deduplicate`).
    pub post_archive_flags: Vec<&'static str>,
    /// Fallback when `ar` fails.
    pub ar_fallback: ArFallback,
    /// Strip flag for the linker (via `-Wl,`).
    pub strip_flag: &'static str,
    /// Whether assembly stub generation is supported.
    pub supports_asm_stubs: bool,
    /// How the C++ main stub declares weak externals.
    pub main_stub_variant: MainStubVariant,
    /// Whether `___builtin_*` trampolines should be generated.
    pub generate_builtin_trampolines: bool,
    /// Whether `-fPIC` should be passed to the linker driver.
    pub use_fpic: bool,
    /// Whether the linker supports `-Bstatic`/`-Bdynamic` for static linking control.
    pub supports_bstatic: bool,
}

impl PlatformLinkConfig {
    /// Get the link configuration for the host platform.
    pub fn for_host() -> Self {
        Self::for_target(&Target::host())
    }

    /// Get the link configuration for a specific target.
    ///
    /// For Windows, defaults to MSVC ABI. Use `for_windows_abi()` or
    /// `for_host_with_compiler()` to select MinGW.
    pub fn for_target(target: &Target) -> Self {
        match target.os {
            TargetOS::Linux => Self::linux(),
            TargetOS::MacOS => Self::macos(),
            TargetOS::FreeBSD => Self::freebsd(),
            TargetOS::Windows => Self::windows(),
            _ => Self::linux(), // fallback
        }
    }

    /// Get the link configuration for the host, auto-detecting Windows ABI
    /// from the C compiler.
    pub fn for_host_with_compiler(cc: &str) -> Self {
        let target = Target::host();
        match target.os {
            TargetOS::Windows => {
                let is_msvc = crate::platform::cc_detect::is_msvc_target(cc);
                Self::for_windows_abi(is_msvc)
            }
            _ => Self::for_target(&target),
        }
    }

    fn linux() -> Self {
        Self {
            libraries: vec!["pthread", "dl", "m", "unwind"],
            library_search_paths: vec![],
            system_scan_libs: vec![
                "/lib/x86_64-linux-gnu/libc.so.6",
                "/lib/x86_64-linux-gnu/libm.so.6",
                "/lib/x86_64-linux-gnu/libpthread.so.0",
                "/lib/x86_64-linux-gnu/libdl.so.2",
            ],
            nm_flags: vec!["-D", "-g", "-p"],
            stub_strategy: StubStrategy::Weak,
            asm_label_extra_chars: vec!['.', '$'],
            unresolved_symbol_flags: vec!["-Wl,--allow-multiple-definition", "-Wl,--unresolved-symbols=ignore-all"],
            disable_pie: true,
            extra_link_flags: vec![],
            whole_archive_style: WholeArchiveStyle::GnuWholeArchive,
            post_archive_flags: vec![],
            ar_fallback: ArFallback::None,
            strip_flag: "-Wl,-s",
            supports_asm_stubs: true,
            main_stub_variant: MainStubVariant::WeakAttribute,
            generate_builtin_trampolines: false,
            use_fpic: true,
            supports_bstatic: true,
        }
    }

    fn macos() -> Self {
        Self {
            libraries: vec!["m", "System"],
            library_search_paths: vec![],
            system_scan_libs: vec!["/usr/lib/libSystem.B.dylib"],
            nm_flags: vec!["-g", "-p"],
            stub_strategy: StubStrategy::WeakDefinition,
            asm_label_extra_chars: vec!['$'],
            unresolved_symbol_flags: vec!["-Wl,-undefined,dynamic_lookup"],
            disable_pie: false,
            extra_link_flags: vec!["-Wl,-ld_classic"],
            whole_archive_style: WholeArchiveStyle::ForceLoad,
            post_archive_flags: vec!["-Wl,-no_deduplicate"],
            ar_fallback: ArFallback::Libtool,
            strip_flag: "-Wl,-S",
            supports_asm_stubs: true,
            main_stub_variant: MainStubVariant::WeakAttribute,
            generate_builtin_trampolines: true,
            use_fpic: true,
            supports_bstatic: false,
        }
    }

    fn freebsd() -> Self {
        Self {
            libraries: vec!["pthread", "m", "execinfo", "z", "zstd", "util", "rt"],
            library_search_paths: vec!["/usr/local/lib"],
            system_scan_libs: vec![
                "/lib/libc.so.7",
                "/lib/libm.so.5",
                "/lib/libthr.so.3",
                "/usr/lib/libexecinfo.so.1",
            ],
            nm_flags: vec!["-D", "-g", "-p"],
            stub_strategy: StubStrategy::StrongWithAllowMultiple,
            asm_label_extra_chars: vec!['.', '$'],
            unresolved_symbol_flags: vec!["-Wl,--allow-multiple-definition"],
            disable_pie: true,
            extra_link_flags: vec![],
            whole_archive_style: WholeArchiveStyle::GnuWholeArchive,
            post_archive_flags: vec![],
            ar_fallback: ArFallback::None,
            strip_flag: "-Wl,-s",
            supports_asm_stubs: true,
            main_stub_variant: MainStubVariant::WeakAttribute,
            generate_builtin_trampolines: false,
            use_fpic: true,
            supports_bstatic: true,
        }
    }

    fn windows() -> Self {
        Self {
            libraries: vec!["kernel32", "ws2_32", "bcrypt", "userenv"],
            library_search_paths: vec![],
            system_scan_libs: vec![],
            nm_flags: vec![],
            stub_strategy: StubStrategy::None,
            asm_label_extra_chars: vec![],
            unresolved_symbol_flags: vec![],
            disable_pie: false,
            extra_link_flags: vec![],
            whole_archive_style: WholeArchiveStyle::MsvcWholeArchive,
            post_archive_flags: vec![],
            ar_fallback: ArFallback::None,
            strip_flag: "",
            supports_asm_stubs: false,
            main_stub_variant: MainStubVariant::MsvcAlternateName,
            generate_builtin_trampolines: false,
            use_fpic: false,
            supports_bstatic: false,
        }
    }

    /// Adjust Windows config for MinGW toolchain (GNU ABI instead of MSVC).
    pub fn windows_mingw() -> Self {
        Self {
            // ntdll: NtReadFile, NtOpenFile, NtWriteFile, NtCreateNamedPipeFile (Rust std)
            // ole32: CoTaskMemFree (dirs_sys_next crate)
            // synchronization: WakeByAddressSingle, WaitOnAddress (Rust std parking_lot)
            libraries: vec![
                "kernel32", "ws2_32", "bcrypt", "userenv",
                "ntdll", "ole32", "synchronization",
            ],
            library_search_paths: vec![],
            system_scan_libs: vec![],
            nm_flags: vec![],
            stub_strategy: StubStrategy::Weak,
            asm_label_extra_chars: vec![],
            unresolved_symbol_flags: vec![
                "-Wl,--allow-multiple-definition",
                "-Wl,--warn-unresolved-symbols",
            ],
            disable_pie: false,
            extra_link_flags: vec![],
            whole_archive_style: WholeArchiveStyle::GnuWholeArchive,
            post_archive_flags: vec![],
            ar_fallback: ArFallback::None,
            strip_flag: "-Wl,-s",
            supports_asm_stubs: true,
            main_stub_variant: MainStubVariant::WeakAttribute,
            generate_builtin_trampolines: false,
            use_fpic: false,
            supports_bstatic: true,
        }
    }

    /// Get Windows config based on whether the compiler targets MSVC ABI.
    pub fn for_windows_abi(is_msvc: bool) -> Self {
        if is_msvc {
            Self::windows()
        } else {
            Self::windows_mingw()
        }
    }

    /// Add whole-archive flags to a command for linking an archive.
    ///
    /// `is_clang_cl`: whether the compiler driver is clang-cl (MSVC syntax).
    pub fn add_whole_archive_args(
        &self,
        cmd: &mut std::process::Command,
        archive_path: &std::path::Path,
        is_clang_cl: bool,
    ) {
        match &self.whole_archive_style {
            WholeArchiveStyle::ForceLoad => {
                cmd.arg("-Wl,-force_load").arg(archive_path);
            }
            WholeArchiveStyle::GnuWholeArchive => {
                cmd.arg("-Wl,--whole-archive")
                    .arg(archive_path)
                    .arg("-Wl,--no-whole-archive");
            }
            WholeArchiveStyle::MsvcWholeArchive => {
                if is_clang_cl {
                    cmd.arg("-Xlinker").arg("/WHOLEARCHIVE").arg(archive_path);
                } else {
                    cmd.arg(format!("-Wl,/WHOLEARCHIVE:{}", archive_path.display()));
                }
            }
        }
        for flag in &self.post_archive_flags {
            cmd.arg(flag);
        }
    }

    /// Add strip flags to a linker command.
    ///
    /// `is_clang_cl`: whether the compiler driver is clang-cl (MSVC syntax).
    pub fn add_strip_args(&self, cmd: &mut std::process::Command, is_clang_cl: bool) {
        if self.strip_flag.is_empty() {
            // Windows MSVC: use /DEBUG:NONE
            if matches!(self.main_stub_variant, MainStubVariant::MsvcAlternateName) {
                if is_clang_cl {
                    cmd.arg("-Xlinker").arg("/DEBUG:NONE");
                } else {
                    cmd.arg("-Wl,/DEBUG:NONE");
                }
            }
        } else {
            cmd.arg(self.strip_flag);
        }
    }

    /// Add force-unresolved flags for MSVC linker (no assembly stubs).
    ///
    /// `is_clang_cl`: whether the compiler driver is clang-cl (MSVC syntax).
    pub fn add_force_unresolved_args(&self, cmd: &mut std::process::Command, is_clang_cl: bool) {
        if !self.supports_asm_stubs
            && matches!(self.main_stub_variant, MainStubVariant::MsvcAlternateName)
        {
            if is_clang_cl {
                cmd.arg("-Xlinker").arg("/FORCE:UNRESOLVED");
            } else {
                cmd.arg("-Wl,/FORCE:UNRESOLVED");
            }
        }
    }

    /// Run libtool fallback for creating an archive on macOS.
    ///
    /// Returns `Ok(())` if libtool succeeded, `Err` otherwise.
    /// Only meaningful when `ar_fallback == ArFallback::Libtool`.
    pub fn run_ar_fallback(
        &self,
        temp_dir: &std::path::Path,
        archive_path: &std::path::Path,
        object_paths: &[std::path::PathBuf],
        batch_size: usize,
    ) -> Result<(), String> {
        match self.ar_fallback {
            ArFallback::Libtool => {
                let mut sub_archives = Vec::new();
                for (i, chunk) in object_paths.chunks(batch_size).enumerate() {
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
                    .arg(archive_path)
                    .args(&sub_archives)
                    .status()
                    .map_err(|e| format!("libtool merge: {e}"))?;
                if !s.success() {
                    return Err("libtool merge failed".to_string());
                }
                Ok(())
            }
            ArFallback::None => Err("ar failed to create archive".to_string()),
        }
    }

    /// Generate the C++ main stub source code.
    pub fn main_stub_code(&self) -> &'static str {
        match self.main_stub_variant {
            MainStubVariant::MsvcAlternateName => {
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
            }
            MainStubVariant::WeakAttribute => {
                r#"
extern "C" {
    int __attribute__((weak)) spl_main(void);
    void __attribute__((weak)) rt_set_args(int argc, char** argv);
    void __attribute__((weak)) __simple_runtime_init(void);
    void __attribute__((weak)) __simple_runtime_shutdown(void);
}
int main(int argc, char** argv) {
    if (__simple_runtime_init) __simple_runtime_init();
    if (rt_set_args) rt_set_args(argc, argv);
    int r = spl_main ? spl_main() : 0;
    if (__simple_runtime_shutdown) __simple_runtime_shutdown();
    return r;
}
"#
            }
        }
    }

    /// Static library filename for a given name on this platform.
    ///
    /// MSVC produces `name.lib`, Unix produces `libname.a`.
    pub fn static_lib_name(&self, name: &str) -> (String, String) {
        if matches!(self.main_stub_variant, MainStubVariant::MsvcAlternateName) {
            (format!("{}.lib", name), format!("lib{}.a", name))
        } else {
            (format!("lib{}.a", name), format!("{}.lib", name))
        }
    }

    /// Whether this platform's object format forbids dots in symbol names.
    ///
    /// Mach-O (macOS) does not support dots — Apple ld crashes. COFF (Windows) and
    /// ELF (Linux, FreeBSD) allow dots in symbol names.
    pub fn dots_forbidden_in_symbols(&self) -> bool {
        matches!(self.stub_strategy, StubStrategy::WeakDefinition)
    }

    /// Check if a symbol name is valid as an assembly label on this platform.
    pub fn is_valid_asm_label(&self, sym: &str) -> bool {
        !sym.is_empty()
            && sym
                .chars()
                .all(|c| c.is_alphanumeric() || c == '_' || self.asm_label_extra_chars.contains(&c))
    }

    /// Generate assembly stub for a symbol.
    pub fn generate_stub_asm(&self, sym: &str, ret_nil: &str) -> String {
        match self.stub_strategy {
            StubStrategy::WeakDefinition => {
                format!(".weak_definition {0}\n.globl {0}\n{0}:\n  {1}\n\n", sym, ret_nil)
            }
            StubStrategy::StrongWithAllowMultiple => {
                format!(".globl {0}\n{0}:\n  {1}\n\n", sym, ret_nil)
            }
            StubStrategy::Weak => {
                format!(".weak {0}\n{0}:\n  {1}\n\n", sym, ret_nil)
            }
            StubStrategy::None => String::new(),
        }
    }

    /// Generate assembly for a builtin trampoline (e.g., `___builtin_X` → `_X`).
    pub fn generate_builtin_trampoline_asm(&self, sym: &str, jmp_prefix: &str, real_fn: &str) -> String {
        match self.stub_strategy {
            StubStrategy::WeakDefinition => {
                format!(
                    ".weak_definition {0}\n.globl {0}\n{0}:\n  {1} {2}\n\n",
                    sym, jmp_prefix, real_fn
                )
            }
            StubStrategy::StrongWithAllowMultiple | StubStrategy::Weak => {
                // Use weak for trampolines on ELF regardless
                format!(".weak {0}\n.globl {0}\n{0}:\n  {1} {2}\n\n", sym, jmp_prefix, real_fn)
            }
            StubStrategy::None => String::new(),
        }
    }
}

// ────────────────────────────────────────────────────────────────────────────
// Object-format / codegen platform helpers
// ────────────────────────────────────────────────────────────────────────────

/// Object format of the target (drives section naming, symbol prefixes, etc.).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ObjectFormat {
    ELF,
    MachO,
    COFF,
}

impl ObjectFormat {
    pub fn for_target(target: &Target) -> Self {
        match target.os {
            TargetOS::MacOS => ObjectFormat::MachO,
            TargetOS::Windows => ObjectFormat::COFF,
            _ => ObjectFormat::ELF,
        }
    }

    pub fn for_host() -> Self {
        Self::for_target(&Target::host())
    }
}

/// Platform-specific codegen configuration.
/// Centralises decisions that were previously scattered as `cfg!(target_os)` checks.
#[derive(Debug, Clone)]
pub struct PlatformCodegenConfig {
    pub object_format: ObjectFormat,
    /// Section for auto-init function pointers (e.g., `.init_array` / `__DATA,__mod_init_func`).
    pub init_section_segment: &'static str,
    pub init_section_name: &'static str,
    /// Whether symbol names must not contain `.` (Mach-O requirement).
    pub sanitize_dots_in_symbols: bool,
    /// Whether the C ABI prepends `_` to symbols.
    pub c_symbol_underscore_prefix: bool,
    /// Extra linker flags for the native project pipeline.
    pub extra_linker_flags: Vec<&'static str>,
    /// Whether to use `-filelist` for large object counts (macOS).
    pub use_filelist: bool,
    /// Max objects before using archive or filelist (0 = unlimited).
    pub archive_threshold: usize,
    /// Strip flag for the linker.
    pub strip_flag: &'static str,
    /// Whether this platform uses Windows calling convention (WindowsFastcall).
    pub windows_calling_convention: bool,
}

impl PlatformCodegenConfig {
    pub fn for_host() -> Self {
        Self::for_target(&Target::host())
    }

    pub fn for_target(target: &Target) -> Self {
        match target.os {
            TargetOS::MacOS => Self::macos(),
            TargetOS::Windows => Self::windows(),
            TargetOS::FreeBSD => Self::freebsd(),
            _ => Self::linux(),
        }
    }

    fn linux() -> Self {
        Self {
            object_format: ObjectFormat::ELF,
            init_section_segment: "",
            init_section_name: ".init_array",
            sanitize_dots_in_symbols: false,
            c_symbol_underscore_prefix: false,
            extra_linker_flags: vec!["-no-pie"],
            use_filelist: false,
            archive_threshold: 100,
            strip_flag: "-Wl,-s",
            windows_calling_convention: false,
        }
    }

    fn macos() -> Self {
        Self {
            object_format: ObjectFormat::MachO,
            init_section_segment: "__DATA",
            init_section_name: "__mod_init_func",
            sanitize_dots_in_symbols: true,
            c_symbol_underscore_prefix: true,
            extra_linker_flags: vec![],
            use_filelist: true,
            archive_threshold: usize::MAX, // skip archiving — ranlib issues with cranelift objects
            strip_flag: "-Wl,-dead_strip",
            windows_calling_convention: false,
        }
    }

    fn freebsd() -> Self {
        Self {
            object_format: ObjectFormat::ELF,
            init_section_segment: "",
            init_section_name: ".init_array",
            sanitize_dots_in_symbols: false,
            c_symbol_underscore_prefix: false,
            extra_linker_flags: vec!["-no-pie"],
            use_filelist: false,
            archive_threshold: 100,
            strip_flag: "-Wl,-s",
            windows_calling_convention: false,
        }
    }

    fn windows() -> Self {
        Self {
            object_format: ObjectFormat::COFF,
            init_section_segment: "",
            init_section_name: ".CRT$XCU",
            sanitize_dots_in_symbols: false,
            c_symbol_underscore_prefix: true,
            extra_linker_flags: vec![],
            use_filelist: false,
            archive_threshold: 100,
            strip_flag: "/DEBUG:NONE",
            windows_calling_convention: true,
        }
    }

    /// Sanitize a symbol name if required by the object format.
    pub fn sanitize_symbol(&self, name: &str) -> String {
        if self.sanitize_dots_in_symbols && name.contains('.') {
            name.replace('.', "_dot_")
        } else {
            name.to_string()
        }
    }
}

/// Default libraries for standalone native binary linking.
/// Used by `NativeBinaryOptions` in `native_binary.rs`.
pub fn default_libraries_for_target(target: &Target) -> Vec<String> {
    match target.os {
        TargetOS::Linux => vec![
            "c".into(),
            "pthread".into(),
            "dl".into(),
            "m".into(),
            "gcc_s".into(),
            "lzma".into(),
            "simple_runtime".into(),
        ],
        TargetOS::MacOS => vec!["System".into(), "simple_runtime".into()],
        TargetOS::Windows => vec![
            "c".into(),
            "msvcrt".into(),
            "kernel32".into(),
            "ws2_32".into(),
            "advapi32".into(),
            "simple_runtime".into(),
        ],
        TargetOS::FreeBSD => vec![
            "c".into(),
            "pthread".into(),
            "m".into(),
            "execinfo".into(),
            "simple_runtime".into(),
        ],
        _ => vec!["c".into()],
    }
}
