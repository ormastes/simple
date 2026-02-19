# Target-Qualified Inline Assembly

**Status:** Design
**Date:** 2026-02-18

## Overview

Target-qualified asm extends `asm` blocks with compile-time target dispatch via `asm match`.
The qualifier `[arch, os, abi, backend version]` selects which asm block to compile based on
the current build target. **This feature only works with `asm match` or `compile_error`** —
standalone `asm[spec]{}` is not supported.

Relies on existing types:
- `TargetArch` — `src/std/common/target.spl`
- `TargetOS` — `src/std/common/target.spl`
- `TargetPreset.abi` — `src/compiler/target_presets.spl`
- `BackendKind` — `src/compiler_core/backend_types.spl`
- `CallingConvention` — `src/compiler_shared/calling_convention.spl`

---

## Qualifier Format

```
[arch, os, abi, backend version_constraint]
  │     │    │    │       │
  │     │    │    │       └─ version comparison (optional)
  │     │    │    └─ BackendKind: llvm, cranelift, native (optional, default: _)
  │     │    └─ ABI: gnu, eabihf, msvc, macho, ilp32, lp64d (optional, default: _)
  │     └─ TargetOS: linux, windows, macos, freebsd, baremetal (optional, default: _)
  └─ TargetArch: x86_64, aarch64, arm, riscv64, riscv32, avr, ... (required)
```

### Positional fields

| Position | Field | Source type | Required | Default | Examples |
|----------|-------|-------------|----------|---------|----------|
| 1 | arch | `TargetArch` | yes | — | `x86_64`, `aarch64`, `arm`, `riscv64`, `avr` |
| 2 | os | `TargetOS` | no | `_` (any) | `linux`, `windows`, `freebsd`, `baremetal` |
| 3 | abi | ABI string | no | `_` (any) | `gnu`, `msvc`, `eabihf`, `macho`, `ilp32` |
| 4 | backend | `BackendKind` | no | `_` (any) | `llvm`, `cranelift`, `native` |
| 4+ | version | comparison | no | none | `>= 15`, `== 17`, `~= 17`, `>= 14 < 18` |

### Wildcard `_`

Use `_` to skip a position:

```simple
[x86_64, _, _, llvm >= 15]    # any OS, any ABI, llvm 15+
[aarch64, linux]               # trailing fields default to _
```

### Arch grouping with `|`

```simple
[x86_64 | x86]         # matches either arch
[riscv32 | riscv64]    # matches either RISC-V variant
```

---

## Version Constraints

| Operator | Meaning | Example |
|----------|---------|---------|
| `>=` | Minimum version (hard error if lower) | `llvm >= 15` |
| `==` | Exact version (hard error if different) | `llvm == 17` |
| `<` | Maximum version (hard error if higher) | `llvm < 18` |
| `>= N < M` | Range (inclusive lower, exclusive upper) | `llvm >= 14 < 18` |
| `~=` | Proper/recommended version (compiles on any, emits **note** if different) | `llvm ~= 17` |

### `~=` (proper version) semantics

```simple
case [x86_64, _, _, llvm ~= 17]:
    # Compiles on any llvm version
    # If llvm != 17, emits:
    #   note: recommended backend version: llvm 17, found: llvm 15
    "vmovaps ymm0, [{0}]"
```

---

## Syntax

### `asm match` — Multi-target dispatch (required form)

```simple
fn disable_interrupts():
    asm match:
        case [x86_64]:
            "cli"
        case [aarch64]:
            "msr daifset, #0xf"
        case [riscv64]:
            "csrci mstatus, 0x8"
        case [arm]:
            "cpsid i"
        case _:
            compile_error("disable_interrupts: unsupported arch")
```

### `asm assert` — Compile-time target guard

```simple
fn kernel_main():
    asm assert [x86_64, linux, gnu, llvm >= 15]
    # compile_error if ANY qualifier doesn't match build target

    asm:
        "cli"
        "lgdt [rdi]"
```

### NOT supported — standalone `asm[spec]{}`

```simple
# WRONG — this is a compile error
asm[x86_64]:
    "cli"

# CORRECT — use asm match
asm match:
    case [x86_64]:
        "cli"
    case _:
        compile_error("unsupported")
```

---

## Exhaustiveness Rules

### Exhaustive (has `_` catch-all)

```simple
asm match:
    case [x86_64]:
        "mfence"
    case [aarch64]:
        "dmb ish"
    case _:
        compile_error("memory_fence: unsupported arch")
```

No warning. `_` must be the last case. The `_` body must be either `compile_error(...)` or
valid asm for a fallback implementation.

### Non-exhaustive (no `_`) — compiler warning

```simple
asm match:
    case [x86_64]:
        "mfence"
    case [aarch64]:
        "dmb ish"
    # WARNING: asm match is non-exhaustive
    #   missing: arm, riscv32, riscv64, avr, mcs51, msp430, wasm32, wasm64
    #   add 'case _: compile_error("...")' for exhaustive matching
```

The compiler emits a **warning** listing all unmatched `TargetArch` variants.
If the current build target matches no case, it is a **compile error**.

---

## Examples

### 1. Syscall — arch + os

```simple
fn fast_syscall(nr: i64) -> i64:
    asm match:
        case [x86_64, linux]:
            "mov rax, {0}"
            "syscall"
            in(reg) nr
            out(rax) result
        case [x86_64, freebsd]:
            "mov rax, {0}"
            "syscall"
            in(reg) nr
            out(rax) result
        case [aarch64, linux]:
            "mov x8, {0}"
            "svc #0"
            in(reg) nr
            out(x0) result
        case _:
            compile_error("fast_syscall: unsupported target")
```

### 2. ABI-sensitive calling — arch + os + abi

```simple
fn call_extern(ptr: Ptr):
    asm match:
        case [x86_64, windows, msvc]:
            "call {0}"
            in(rcx) ptr         # msvc: first arg in rcx
        case [x86_64, _, gnu]:
            "call {0}"
            in(rdi) ptr          # sysv: first arg in rdi
        case _:
            compile_error("call_extern: unsupported ABI")
```

### 3. Backend version — SIMD requiring llvm 15+

```simple
fn simd_add(a: Ptr, b: Ptr, out: Ptr):
    asm match:
        case [x86_64, _, _, llvm >= 15]:
            "vmovaps ymm0, [{0}]"
            "vaddps ymm0, ymm0, [{1}]"
            "vmovaps [{2}], ymm0"
            in(reg) a
            in(reg) b
            in(reg) out
        case [x86_64, _, _, cranelift]:
            compile_error("simd_add: cranelift does not support AVX")
        case _:
            compile_error("simd_add: unsupported target")
```

### 4. Proper/recommended version with `~=`

```simple
fn optimized_copy(dst: Ptr, src: Ptr, len: i64):
    asm match:
        case [x86_64, _, _, llvm ~= 17]:
            # Compiles on any llvm, note emitted if not llvm 17
            "rep movsb"
            in(rdi) dst
            in(rsi) src
            in(rcx) len
            options: [volatile]
        case [aarch64, _, _, llvm ~= 17]:
            "1: ldrb w3, [x1], #1"
            "strb w3, [x0], #1"
            "subs x2, x2, #1"
            "b.ne 1b"
            in(x0) dst
            in(x1) src
            in(x2) len
        case _:
            compile_error("optimized_copy: unsupported target")
```

### 5. Arch grouping

```simple
fn nop_any():
    asm match:
        case [x86_64 | x86]:
            "nop"
        case [aarch64 | arm]:
            "nop"
        case [riscv32 | riscv64]:
            "nop"
        case [wasm32]:
            compile_error("wasm has no nop instruction")
        case _:
            compile_error("unsupported arch")
```

### 6. Compile-time guard before plain asm

```simple
fn kernel_entry():
    asm assert [x86_64, linux, gnu, llvm >= 15]

    # After assert, plain asm is safe — target is known
    asm:
        "cli"
        "mov rsp, {0}"
        in(reg) stack_top
```

---

## Compiler Behavior

### Case selection

At compile time, the compiler evaluates each `case [spec]` against the current build target
(`TargetArch`, `TargetOS`, ABI, `BackendKind`, backend version). The **first matching case**
is compiled; all others are discarded (dead code elimination).

### Error conditions

| Condition | Result |
|-----------|--------|
| No case matches, has `case _: compile_error(...)` | Compile error with user message |
| No case matches, no `_` | Compile error: "no asm match case for target X" |
| No case matches, `_` has fallback asm | Fallback asm is compiled |
| `asm assert [spec]` and target doesn't match | Compile error |
| `~= version` and version differs | **Note** (not error), code still compiles |
| `>= version` and version too low | Compile error |

### Warning conditions

| Condition | Result |
|-----------|--------|
| `asm match` without `_` catch-all | Warning: non-exhaustive, lists missing arches |

---

## Relationship to Existing `asm` Syntax

Target-qualified asm **extends** the existing `asm` block; it does not replace it.

| Form | Target-aware | Use case |
|------|-------------|----------|
| `asm: "nop"` | No | Single-platform code, platform set by `@platform` or build target |
| `asm { "nop" }` | No | Same, braced form |
| `asm "nop"` | No | Same, single-line form |
| `asm match: case [spec]: ...` | **Yes** | Multi-platform dispatch |
| `asm assert [spec]` | **Yes** | Compile-time target guard |

The existing `@platform("x86_64")` file-level attribute (from the inline assembly design doc)
sets the default for plain `asm` blocks. `asm match` overrides this per-case.

---

## Implementation Notes

### Parser changes

- `asm match:` parsed as new expression kind `ExprAsmMatch`
- `case [...]` parsed as `AsmTargetSpec` with positional fields
- `compile_error("...")` is an existing compile-time intrinsic
- `asm assert [...]` parsed as `StmtAsmAssert`

### Semantic analysis

- Each `AsmTargetSpec` resolved against `TargetArch.parse()`, `TargetOS`, ABI strings, `BackendKind`
- Exhaustiveness check: enumerate all `TargetArch` variants, subtract matched ones, warn on remainder
- Version comparison: backend version queried from compiler context (e.g., LLVM version from `llc --version`)

### Codegen

- Only the matching case is lowered to MIR/LLVM IR
- Non-matching cases produce no code
- `compile_error` halts compilation with the given message

---

## References

- Inline assembly design: `doc/design/inline_assembly_design.md`
- Target types: `src/std/common/target.spl` (TargetArch, TargetOS, Target)
- Target presets: `src/compiler/target_presets.spl` (TargetPreset with abi field)
- Backend types: `src/compiler_core/backend_types.spl` (BackendKind, CodegenTarget)
- Calling conventions: `src/compiler_shared/calling_convention.spl`
- LLVM target config: `src/compiler/backend/llvm_target.spl`
- Existing asm backends: `src/compiler/backend/x86_asm.spl`, `arm_asm.spl`, `riscv_asm.spl`
- Inline asm AST: `src/compiler/inline_asm.spl`
