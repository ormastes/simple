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
            // Static LLVM objects retained from `libsimple_native_all.a` depend on
            // compression and terminal-info libraries. Cargo supplies these when it
            // links the seed; native-build must carry the same transitive contract.
            // `--as-needed` keeps them out of binaries that do not retain LLVM code.
            libraries: vec!["pthread", "dl", "m", "unwind", "sqlite3", "z", "zstd", "tinfo"],
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
            // `m`/`System` are the libc/libm base. The combined `libsimple_native_all.a`
            // additionally references the C libraries that several runtime/vendor crates
            // bind (libffi for dynamic FFI, libedit for the REPL, zlib/zstd for
            // compression, libxml2 for the XML helpers, libncurses for terminfo, libobjc
            // for the Objective-C runtime, libiconv for text transcoding). These are not
            // emitted as load commands by this native-build link path the way `cargo`/
            // rustc auto-adds them, so they must be listed explicitly or their symbols go
            // unresolved (and, with `SIMPLE_NO_STUB_FALLBACK=1`, fail the build).
            libraries: vec![
                "m", "System", "z", "ffi", "edit", "zstd", "xml2", "ncurses", "objc", "iconv",
            ],
            // Homebrew prefix so `-lzstd` resolves (no `libzstd.tbd` ships in the SDK).
            library_search_paths: vec!["/opt/homebrew/lib"],
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
            // Metal/CoreGraphics are referenced by the graphics runtime baked into
            // the selected Rust runtime archive (including `libsimple_runtime.a`,
            // e.g. `_MTLCreateSystemDefaultDevice`); without these frameworks those
            // symbols stay unresolved at final link time.
            "Metal",
            "CoreGraphics",
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
                "kernel32",
                "ws2_32",
                "bcrypt",
                "userenv",
                "ntdll",
                "advapi32",
                "dbghelp",
                "ole32",
                "oleaut32",
                "shell32",
                "crypt32",
                "secur32",
                "ncrypt",
                "iphlpapi",
                "d3d11",
                "dxgi",
                "ucrt",
                "msvcrt",
                "vcruntime",
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
                "d3d11",
                "dxgi",
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
            unresolved_symbol_flags: vec![
                "-Wl,--allow-multiple-definition",
                "-Wl,--warn-unresolved-symbols",
                "-Wl,--no-fatal-warnings",
            ],
            disable_pie: false,
        }
    }

    /// Check if a symbol name is valid as an assembly label on this platform.
    pub fn is_valid_asm_label(&self, sym: &str) -> bool {
        !sym.is_empty()
            && sym
                .chars()
                .all(|c| c.is_ascii_alphanumeric() || c == '_' || self.asm_label_extra_chars.contains(&c))
    }

    fn needs_asm_quoting(&self, sym: &str) -> bool {
        sym.chars().next().is_some_and(|c| c.is_ascii_digit())
            || sym
                .chars()
                .any(|c| !(c.is_ascii_alphanumeric() || c == '_' || self.asm_label_extra_chars.contains(&c)))
    }

    fn asm_symbol(&self, sym: &str) -> String {
        if !self.needs_asm_quoting(sym) {
            return sym.to_string();
        }

        let escaped = sym.replace('\\', "\\\\").replace('"', "\\\"");
        format!("\"{}\"", escaped)
    }

    /// Generate assembly stub for a symbol.
    pub fn generate_stub_asm(&self, sym: &str, ret_nil: &str) -> String {
        let sym = self.asm_symbol(sym);
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
        let sym = self.asm_symbol(sym);
        let real_fn = self.asm_symbol(real_fn);
        match self.stub_strategy {
            StubStrategy::WeakDefinition => {
                format!(
                    ".weak_definition {0}\n.globl {0}\n{0}:\n  {1} {2}\n\n",
                    sym, jmp_prefix, real_fn
                )
            }
            StubStrategy::StrongWithAllowMultiple => {
                format!(".globl {0}\n{0}:\n  {1} {2}\n\n", sym, jmp_prefix, real_fn)
            }
            StubStrategy::Weak => {
                format!(".weak {0}\n{0}:\n  {1} {2}\n\n", sym, jmp_prefix, real_fn)
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
            "simple_runtime".into(),
        ],
        TargetOS::MacOS => vec!["System".into(), "simple_runtime".into()],
        TargetOS::Windows => vec![
            "c".into(),
            "msvcrt".into(),
            "kernel32".into(),
            "ws2_32".into(),
            "advapi32".into(),
            "d3d11".into(),
            "dxgi".into(),
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trampoline_quotes_digit_start_target() {
        let config = PlatformLinkConfig::linux();
        let asm = config.generate_builtin_trampoline_asm(
            "rt_hashmap_new",
            "jmp",
            "01_unit__lib__nogc_async_mut__spec__rt_hashmap_new",
        );

        assert!(asm.contains("rt_hashmap_new:\n  jmp \"01_unit__lib__nogc_async_mut__spec__rt_hashmap_new\""));
    }

    #[test]
    fn stub_quotes_digit_start_symbol() {
        let config = PlatformLinkConfig::linux();
        let asm = config.generate_stub_asm("01_unit__entry", "retq");

        assert!(asm.contains(".weak \"01_unit__entry\""));
        assert!(asm.contains("\"01_unit__entry\":\n  retq"));
    }

    #[test]
    fn asm_label_validation_is_ascii_only() {
        let config = PlatformLinkConfig::linux();

        assert!(config.is_valid_asm_label("rt_hashmap_new"));
        assert!(!config.is_valid_asm_label("rt_hashmap_ñ"));
    }

    #[test]
    fn linux_links_static_llvm_transitive_libraries() {
        let config = PlatformLinkConfig::linux();

        for library in ["z", "zstd", "tinfo"] {
            assert!(config.libraries.contains(&library));
        }
    }
}
