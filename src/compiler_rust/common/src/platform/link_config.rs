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
}

impl PlatformLinkConfig {
    /// Get the link configuration for the host platform.
    pub fn for_host() -> Self {
        Self::for_target(&Target::host())
    }

    /// Get the link configuration for a specific target.
    pub fn for_target(target: &Target) -> Self {
        match target.os {
            TargetOS::Linux => Self::linux(),
            TargetOS::MacOS => Self::macos(),
            TargetOS::FreeBSD => Self::freebsd(),
            TargetOS::Windows => {
                if target.linker_flavor() == crate::target::LinkerFlavor::Gnu {
                    Self::windows_mingw()
                } else {
                    Self::windows()
                }
            }
            _ => Self::linux(), // fallback
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
        }
    }

    /// Apple frameworks required by the Rust standard library and its transitive
    /// dependencies (CommonCrypto, I/O, networking, UI for some optional paths).
    /// Linked via `-framework` flags on macOS.
    pub fn macos_frameworks() -> Vec<&'static str> {
        vec![
            "CoreFoundation",
            "Security",
            "SystemConfiguration",
            "IOKit",
            "CoreServices",
            "Foundation",
            "AppKit",
        ]
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
            unresolved_symbol_flags: vec!["-Wl,--allow-multiple-definition", "-Wl,--unresolved-symbols=ignore-all"],
            disable_pie: true,
        }
    }

    fn windows() -> Self {
        Self {
            libraries: vec![
                "kernel32", "ws2_32", "bcrypt", "userenv", "ntdll",
                "advapi32", "dbghelp", "ole32", "oleaut32", "shell32",
                "crypt32", "secur32", "ncrypt", "iphlpapi",
                "ucrt", "msvcrt", "vcruntime",
            ],
            library_search_paths: vec![],
            system_scan_libs: vec![],
            nm_flags: vec![],
            stub_strategy: StubStrategy::Weak, // not used on Windows
            asm_label_extra_chars: vec![],
            unresolved_symbol_flags: vec![],
            disable_pie: false,
        }
    }

    /// Adjust Windows config for MinGW toolchain (GNU ABI instead of MSVC).
    pub fn windows_mingw() -> Self {
        Self {
            // Rust std + crate dependencies on MinGW require these system libs.
            // Matches what rustc normally passes for x86_64-pc-windows-gnu.
            libraries: vec![
                "kernel32",
                "ntdll",
                "userenv",
                "ws2_32",
                "dbghelp",
                "advapi32",
                "bcrypt",
                "ole32",
                "oleaut32",
                "shell32",
                "propsys",
                "runtimeobject",
                "synchronization",
                "crypt32",
                "secur32",
                "ncrypt",
                "iphlpapi",
                "user32",
                "gdi32",
                "dwmapi",
                "imm32",
                "uxtheme",
                "winmm",
                "shlwapi",
                "gcc_eh",
                "msvcrt",
                "mingwex",
                "mingw32",
                "gcc",
            ],
            library_search_paths: vec![],
            system_scan_libs: vec![],
            nm_flags: vec![],
            stub_strategy: StubStrategy::Weak,
            asm_label_extra_chars: vec!['.', '$'],
            unresolved_symbol_flags: vec!["-Wl,--allow-multiple-definition", "-Wl,--warn-unresolved-symbols", "-Wl,--no-fatal-warnings"],
            disable_pie: false,
        }
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
