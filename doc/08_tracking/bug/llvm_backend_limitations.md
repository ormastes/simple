# LLVM Backend Known Limitations

**Date:** 2026-04-04
**Modules:** `llvm_capability.spl`, `llvm_version.spl`, `llvm_cross_target.spl`, `llvm_support_matrix.spl`
**Modified:** `tools.spl`, `backend_helpers.spl`

---

## Detection Limitations

### LIM-DET-001: libLLVM Detection Uses Shell Probing, Not Native dlopen

`detect_libllvm_available()` in `llvm_capability.spl` checks for libLLVM by running
`llvm-config --libdir` and then testing file existence with `test -f`. It does not
actually attempt to `dlopen` the library. A file may exist but be an incompatible
ABI, a broken symlink, or a stub package. The capability report will claim
`llvm_lib_backend_available: true` even if the library cannot actually be loaded at
codegen time.

**Severity:** Medium
**Workaround:** If llvm-lib backend fails at codegen, pass `--backend=llvm` to force
CLI-based llc/opt pipeline.

### LIM-DET-002: Windows libLLVM Detection Checks Only LLVM-C.dll

On Windows, `detect_libllvm_available()` checks for `LLVM-C.dll` via `dir /b`. The
actual DLL may be named differently depending on the LLVM distribution (e.g.,
`libLLVM.dll`, `LLVM-18.dll`, or version-specific names from Chocolatey/Scoop
installs). Only one filename pattern is checked.

**Severity:** Low
**Workaround:** Ensure `LLVM-C.dll` is present in the llvm-config `--libdir` path, or
use the CLI backend (`--backend=llvm`).

### LIM-DET-003: Linux Hardcoded Probe Paths Are Debian/Ubuntu-Specific

The fallback probe paths in `detect_libllvm_available()` (lines 256-262) are
Debian/Ubuntu layout (`/usr/lib/llvm-18/lib/`, `/usr/lib/x86_64-linux-gnu/`). Distros
with different layouts (NixOS, Gentoo, Alpine, openSUSE) will not be detected by the
fallback path probe. Detection still works if `llvm-config` is on PATH.

**Severity:** Low
**Workaround:** Ensure `llvm-config` is installed and on PATH. The first detection
method (llvm-config) is distribution-agnostic.

### LIM-DET-004: macOS Homebrew Detection Assumes `brew` on PATH

The macOS fallback in `detect_libllvm_available()` runs
`$(brew --prefix llvm 2>/dev/null)` inside a shell command. If Homebrew is installed
but not on PATH (e.g., Apple Silicon `/opt/homebrew/bin` not in PATH), detection fails.

**Severity:** Low
**Workaround:** Add Homebrew to PATH: `export PATH="$(brew --prefix)/bin:$PATH"`.

### LIM-DET-005: FreeBSD Has No Fallback Probe Paths

`detect_libllvm_available()` has fallback probes for Linux and macOS but none for
FreeBSD. If `llvm-config` is not on PATH, FreeBSD libLLVM detection will always fail.

**Severity:** Low
**Workaround:** Install `llvm-config` via `pkg install llvm18`.

### LIM-DET-006: Tool Discovery Order Prefers Older Versions

`find_llc_portable()` and sibling functions search `llc-18` before `llc-17` before
`llc-16`, then `llc-19`, then unversioned `llc`. LLVM 19 is searched after 16, meaning
a system with both 16 and 19 installed will select 16 even though 19 is newer. The
order prioritizes the primary version (18) but treats 19 as a fallback.

**Severity:** Low (by design -- 18 is the primary supported version)
**Workaround:** Use unversioned symlinks or ensure only the desired version is
installed.

### LIM-DET-007: wasm-ld and nm Version Not Detected

`LlvmToolStatus` for `wasm_ld` and `nm` is created with `LlvmVersionInfo.unknown()`.
No version detection is performed for these tools, so version mismatch warnings cannot
be generated for them.

**Severity:** Low

---

## Version Handling Limitations

### LIM-VER-001: Version Parsing Uses Manual Character Comparison

`parse_llvm_version()` in `llvm_version.spl` implements integer parsing by
character-by-character comparison (`ch == "0"`, `ch == "1"`, etc.) rather than using a
standard `parseInt` function. While correct for ASCII digits, this is fragile if the
Simple runtime ever changes string iteration semantics.

**Severity:** Very Low (works correctly today)

### LIM-VER-002: Only Major Version Checked for Compatibility

`check_version_compatibility()` only compares `version.major` against `LLVM_VERSION_MIN`
(16) and `LLVM_VERSION_MAX` (19). Minor and patch versions are parsed but not used for
compatibility decisions. A hypothetical breaking change in a minor release would not be
caught.

**Severity:** Very Low (LLVM does not break ABI within major versions)

### LIM-VER-003: Version Mismatch Only Compares llc vs libLLVM

`check_version_mismatch()` only compares `llc_ver` against `lib_ver`. It does not check
for mismatches between `opt`, `clang`, and `llc`. A system with `opt-17` and `llc-18`
would not generate a warning.

**Severity:** Low
**Workaround:** Ensure all LLVM tools come from the same installation.

### LIM-VER-004: Version String with Leading Text Before Digits May Mismatch

`parse_llvm_version()` splits on spaces and checks if each part starts with a digit and
contains a dot. Output like `"v18.1.3"` (with a leading `v`) would not match because
the first character is `v`, not a digit. Standard LLVM tools do not produce this format,
but third-party wrappers might.

**Severity:** Very Low
**Workaround:** None needed for standard LLVM installations.

---

## Cross-Target Limitations

### LIM-CROSS-001: is_available() Combines Unix and Windows Shell in One Command

`TargetToolchain.is_available()` in `llvm_cross_target.spl` runs
`command -v {linker} 2>/dev/null || where {linker} 2>NUL` as a single shell command.
On Unix, the `where` portion will produce stderr noise (suppressed by `2>NUL` which is
a Windows-only redirect). On Windows, `command -v` is a bash built-in that may not
exist in `cmd.exe`. This works when the shell is bash/zsh but may fail in pure cmd.exe
environments.

**Severity:** Medium (Windows-only)
**Workaround:** Ensure a bash-compatible shell is available on Windows, or use WSL.

### LIM-CROSS-002: Environment Variable Detection Uses echo in Shell

`resolve_toolchain()` reads `SIMPLE_LINKER` and `SIMPLE_SYSROOT` via
`shell("echo $SIMPLE_LINKER 2>/dev/null")`. On Windows cmd.exe, `$SIMPLE_LINKER` is
not expanded (Windows uses `%SIMPLE_LINKER%`). Environment variable overrides will not
work on native Windows cmd.exe.

**Severity:** Medium (Windows-only)
**Workaround:** Use CLI flags `--linker=` and `--sysroot=` instead of environment
variables on Windows.

### LIM-CROSS-003: No Windows Cross-Compilation Targets

`toolchain_for_target()` does not provide cross-compilation descriptors for Windows
targets from a Linux/macOS host (e.g., `x86_64-pc-windows-msvc` or
`x86_64-pc-windows-gnu`). Cross-compiling to Windows is not supported.

**Severity:** Medium
**Workaround:** Build on native Windows, or use MinGW toolchain manually with
`--linker=` and `--sysroot=` overrides.

### LIM-CROSS-004: i686 Toolchain Only Defined for Linux

`toolchain_i686()` has a specific descriptor for Linux but falls back to a generic
empty descriptor for all other OSes (macOS, Windows, FreeBSD). 32-bit x86 compilation
on non-Linux hosts lacks proper defaults.

**Severity:** Low
**Workaround:** Provide linker and sysroot manually via CLI flags or environment
variables.

### LIM-CROSS-005: RISCV-32 Uses riscv64-linux-gnu-ld as Linker

`toolchain_riscv32()` specifies `riscv64-linux-gnu-ld` as the linker for RV32 targets,
relying on the `-melf32lriscv` flag to select 32-bit mode. This works with GNU ld but
may not work with all linker implementations (e.g., lld may need different flags).

**Severity:** Low
**Workaround:** Use `--linker=` override if using a non-GNU linker for RV32.

### LIM-CROSS-006: WASM Targets Lack WASI Sysroot Configuration

Both `toolchain_wasm32()` and `toolchain_wasm64()` leave `sysroot` and `crt_dir` empty.
WASI programs that need libc (via wasi-sdk) require a sysroot, but there is no
automatic detection of wasi-sdk installation.

**Severity:** Medium
**Workaround:** Pass `--sysroot=/path/to/wasi-sdk/share/wasi-sysroot` manually.

### LIM-CROSS-007: Default Linker is mold on Linux, Not Universally Installed

Linux x86_64 and native aarch64 toolchains default to `mold` as the linker. While mold
is fast, it is not installed by default on most distributions. If mold is missing,
linking will fail with "linker not found" rather than falling back to `ld` or `lld`.

**Severity:** Medium
**Workaround:** Install mold (`apt install mold`) or override with
`--linker=ld` / `--linker=lld`.

---

## Support Matrix Limitations

### LIM-MAT-001: llvm-lib Backend Does Not Support WASM

The support matrix marks `LlvmLib + Wasm32` and `LlvmLib + Wasm64` as `Unsupported`.
WASM emission through the libLLVM C API is not implemented. Users must use the CLI
backend (`--backend=llvm`) for WASM targets.

**Severity:** Medium
**Workaround:** Use `--backend=llvm` for WASM targets.

### LIM-MAT-002: wasm64 Support is Experimental

The matrix marks `Llvm + Wasm64` as `Partial` with no proof file. The wasm64 proposal
is still evolving in the WebAssembly ecosystem and toolchain support is incomplete.

**Severity:** Low
**Workaround:** Use wasm32 for production WASM targets.

### LIM-MAT-003: Matrix is Static, Not Validated at Runtime

`get_support_matrix()` returns hardcoded entries. The matrix is not cross-checked
against actual tool availability from `LlvmCapabilityReport`. A system missing the
required tools will still show "Stable" in the matrix output even if the tools are
absent.

**Severity:** Low
**Workaround:** Use `detect_llvm_capabilities()` for actual runtime availability;
use the support matrix only as a reference for what *can* work.

### LIM-MAT-004: Matrix Lookup is Linear Scan

`lookup_support()` iterates the entire matrix array for each query. With 16 entries
this is negligible, but the design does not scale to larger matrices without indexing.

**Severity:** Very Low (16 entries)

---

## General Workarounds

| Problem | Workaround |
|---------|-----------|
| libLLVM detected but fails at codegen | `--backend=llvm` to use CLI pipeline |
| LLVM tools not found on PATH | Install LLVM and ensure versioned binaries or `llvm-config` are on PATH |
| Version mismatch warnings | Install all LLVM tools from the same package version |
| Windows environment variables ignored | Use `--linker=` and `--sysroot=` CLI flags |
| mold linker not installed (Linux) | `apt install mold` or `--linker=ld` |
| WASM needs sysroot | `--sysroot=/path/to/wasi-sdk/share/wasi-sysroot` |
| Cross-compile to Windows | Build natively on Windows or use MinGW with manual overrides |
| NixOS/Alpine/Gentoo libLLVM not found | Ensure `llvm-config` is on PATH |
| WASM with llvm-lib backend | Use `--backend=llvm` (CLI backend) |
| 32-bit x86 linking fails | `apt install gcc-multilib libc6-dev-i386` |

---

## Related Files

- `src/compiler/70.backend/backend/llvm_capability.spl` -- Capability detection
- `src/compiler/70.backend/backend/llvm_version.spl` -- Version parsing and compatibility
- `src/compiler/70.backend/backend/llvm_cross_target.spl` -- Cross-target toolchain descriptors
- `src/compiler/70.backend/backend/llvm_support_matrix.spl` -- Support matrix
- `src/compiler/70.backend/backend/backend_helpers.spl` -- Consumes capability report
- `src/compiler/70.backend/backend/tools.spl` -- Tool discovery
