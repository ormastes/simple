# LLVM Backend Policy

**Date:** 2026-04-04
**Status:** Active

## Backend Selection Precedence

The Simple compiler publicly supports two LLVM execution paths. Selection follows this precedence:

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

### `rust-llvm` (Bootstrap / Advanced Path)

This path is intentionally **not** part of the public support matrix.

Use only for bootstrap experiments or seed-tooling work where the Rust-hosted LLVM stack is already available.
Do not count it toward public backend closure, release support, or README matrix claims.

## Auto-Selection Logic

```
if llvm_available()   -> llvm-lib  (best: in-process, no tools)
elif llc_available()  -> llvm      (good: CLI tools present)
else                  -> cranelift (fallback: no LLVM at all)
```

For 32-bit targets, only LLVM backends are supported (Cranelift lacks 32-bit).
`rust-llvm` is not part of auto-selection.

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
| Compiler (`build`, `native-build`) | `llvm-lib` | In-process, best optimization |
| Interpreter / Loader | `cranelift` | Fast JIT for running code |
| Cross-target Linux | `llvm` or `llvm-lib` | Needs target triple support |
| Bare-metal | `llvm` or `llvm-lib` | Needs `-none` triple |
| WASM | `llvm` | Needs `wasm-ld` for linking |
| Bootstrap seed tooling | `rust-llvm` | Out-of-band bootstrap path, not counted in public matrix |

## Target Support Classes

Each target is classified by proof level:

- **stable**: Compiled authoritative proof exists, CI-tested
- **supported**: Works with external sysroot/toolchain, documented requirements
- **partial**: Code generation works, linking may need manual setup
- **unsupported**: Not available for this backend

The public matrix currently tracks only `llvm-lib` and `llvm` rows. If a workflow requires Rust-hosted LLVM bootstrap, that is documented separately and must not be treated as public backend closure.

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

## rust-llvm Exclusion

Per [ADR: rust-llvm Exclusion](../../04_architecture/adr_rust_llvm_exclusion.md), the Rust bootstrap LLVM path (`src/compiler_rust/`) is formally excluded from the public LLVM backend family. It is a development-only bootstrap tool, not a production backend. The public support matrix contains only `llvm-lib` and `llvm` (CLI) columns.
