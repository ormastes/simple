# LLVM Backend Policy

**Date:** 2026-04-04
**Status:** Active

## Backend Selection Precedence

The Simple compiler supports three LLVM execution paths. Selection follows this precedence:

### 1. `llvm-lib` (Preferred Hosted Path)

Use when `libLLVM` is available on the host system.

- In-process compilation via LLVM C API
- No external tool dependencies (`llc`, `opt` not needed)
- Lower overhead, deterministic builds
- Primary path for release builds on hosts with LLVM dev libraries

### 2. `llvm` (CLI Fallback Path)

Use when `libLLVM` is unavailable but LLVM CLI tools exist.

- Uses `llc`, `opt`, `clang` as subprocesses
- Requires LLVM 16-19 (see version policy below)
- Portable across package manager installations
- Fallback for systems where only the LLVM toolchain is installed

### 3. `rust-llvm` (Bootstrap / Advanced Path)

Use for:
- Bootstrap compilation (Rust seed -> Simple compiler)
- Advanced LLVM integration via inkwell
- Future GPU-oriented expansion

This is a bootstrap-specialized path, not a primary production path.

## Auto-Selection Logic

```
if llvm_available()   -> llvm-lib  (best: in-process, no tools)
elif llc_available()  -> llvm      (good: CLI tools present)
else                  -> cranelift (fallback: no LLVM at all)
```

For 32-bit targets, only LLVM backends are supported (Cranelift lacks 32-bit).

## Supported LLVM Version Range

| Version | Status |
|---------|--------|
| LLVM 19 | Supported |
| LLVM 18 | Supported (primary) |
| LLVM 17 | Supported |
| LLVM 16 | Supported (minimum) |
| LLVM 15 | Unsupported (too old) |
| LLVM 20+ | Best-effort (too new, warn) |

Version checks are centralized in `llvm_version.spl`.

## Authoritative Backend Per Build Type

| Build Type | Authoritative Backend | Rationale |
|------------|----------------------|-----------|
| Hosted native (release) | `llvm-lib` | In-process, best optimization |
| Hosted native (debug) | `cranelift` | Fastest compile time |
| Cross-target Linux | `llvm` or `llvm-lib` | Needs target triple support |
| Bare-metal | `llvm` or `llvm-lib` | Needs `-none` triple |
| WASM | `llvm` | Needs `wasm-ld` for linking |
| Bootstrap | `rust-llvm` | Minimal dependency path |

## Target Support Classes

Each target is classified by proof level:

- **stable**: Compiled authoritative proof exists, CI-tested
- **supported**: Works with external sysroot/toolchain, documented requirements
- **partial**: Code generation works, linking may need manual setup
- **unsupported**: Not available for this backend

See `llvm_support_matrix.spl` for the machine-readable matrix.

## GPU Scope

GPU codegen (CUDA/PTX, Vulkan/SPIR-V) is **out of scope** for the core LLVM completion milestone. GPU support is classified separately as advanced/experimental and uses dedicated `Cuda` and `Vulkan` backend kinds.

## Diagnostics Policy

When a backend is unavailable, the compiler must emit actionable diagnostics:

- Name the missing tool or library
- Suggest platform-specific install commands
- Report the detected LLVM version if tools are found
- List which targets are available given the current toolchain

See `llvm_capability.spl` for the capability report implementation.
