# SimpleOS Bootstrap Plan

Full bootstrap path for building the Simple compiler to run on SimpleOS.

## Overview

The Simple compiler bootstraps through 3 stages from a Rust seed:

1. **Rust seed** (Cargo/Cranelift) produces Stage 1 binary
2. **Stage 1** compiles itself to produce Stage 2
3. **Stage 2** compiles itself to produce Stage 3 (must equal Stage 2 = convergence)

This document describes how to execute that pipeline targeting SimpleOS,
both via cross-compilation from a host and natively on SimpleOS itself.

---

## Phase 0: Prerequisites

### On-Host (Cross-Compilation Path)

| Requirement | Purpose | How to get it |
|-------------|---------|---------------|
| Host Rust toolchain | Build the Rust seed binary | `rustup` (stable) |
| Clang (host) | Link native binaries | System package or LLVM release |
| SimpleOS sysroot | Headers + libsimpleos_c.a + crt0.o + linker script | `sh src/os/port/llvm/sysroot.shs` |
| Source tree | All `.spl` files under `src/` | Git checkout |

The sysroot layout (built by `src/os/port/llvm/sysroot.shs`):

```
build/os/sysroot/
  include/              -- C headers (simpleos_libc.h, stdio.h, etc.)
  include/c++/          -- Minimal C++ headers
  lib/                  -- libsimpleos_c.a, crt0.o, compiler-rt builtins
  share/simpleos/       -- simpleos.ld linker script
```

### On-SimpleOS (Native Build Path)

Everything above, plus these must already run **on** SimpleOS:

| Requirement | Purpose | Source |
|-------------|---------|--------|
| Clang/LLD running on SimpleOS | Compile C stubs, link final binary | Cross-built via `src/os/port/llvm/build.spl --cross` |
| Rust seed binary for SimpleOS | Stage 0 compiler | Cross-compiled from host (see Phase 1b) |
| SimpleOS filesystem | Read `.spl` source files | VFS or initramfs with source tree |
| `simple_make` (optional) | Make-like build tool written in Simple | `src/os/port/build_tools/simple_make.spl` |

---

## Phase 1: Rust Seed

### Phase 1a: Build Rust Seed on Host (Standard)

```bash
cd src/compiler_rust
SDKROOT=$(xcrun --show-sdk-path) \
  cargo build --profile bootstrap -p simple-driver -p simple-native-all
```

Output: `src/compiler_rust/target/bootstrap/simple`

This binary uses the Cranelift backend (deterministic with incremental cache)
and produces x86_64/aarch64 ELF or Mach-O for the host platform.

### Phase 1b: Cross-Compile Rust Seed for SimpleOS

The Rust seed must eventually run on SimpleOS. Two approaches:

**Approach A: Cross-compile from host** (recommended for initial bootstrap)

```bash
cd src/compiler_rust

# Build with SimpleOS target spec
SDKROOT=$(xcrun --show-sdk-path) \
  cargo build --profile bootstrap \
    -p simple-driver -p simple-native-all \
    --target ../os/toolchain/rust/x86_64-unknown-simpleos.json \
    -Z build-std=core,alloc
```

Requirements:
- Rust nightly (for `-Z build-std`)
- `rust-src` component (`rustup +nightly component add rust-src`)
- SimpleOS target spec JSON at `src/os/toolchain/rust/x86_64-unknown-simpleos.json`
- libsimpleos_c.a built and linked

Linking requires SimpleOS sysroot flags:
- `-nostdlib -ffreestanding -static`
- `-T build/os/sysroot/share/simpleos/simpleos.ld`
- `-L build/os/sysroot/lib -lsimpleos_c`
- `build/os/sysroot/lib/crt0.o`

**Approach B: Build Rust on SimpleOS** (long-term goal)

Requires a full Rust toolchain running on SimpleOS, built via
`src/os/port/rust/build.spl`. This is a larger effort that
depends on the LLVM cross-build (`src/os/port/llvm/build.spl --cross`)
completing first.

### Phase 1c: Build SimpleOS Sysroot

Before any cross-compilation, the sysroot must be populated:

```bash
sh src/os/port/llvm/sysroot.shs
```

This:
1. Copies headers from `src/os/libc/include/` to `build/os/sysroot/include/`
2. Builds `libsimpleos_c.a` from the libc sources (using the `Makefile` in `src/os/libc/`)
3. Copies `crt0.o` (startup code) and linker script `simpleos.ld`
4. Optionally installs compiler-rt builtins

The libc includes: string ops, memory ops, printf, mmap/munmap, file I/O
(via SimpleOS syscalls), process control, basic math, pthreads stubs,
dlmalloc allocator, setjmp/longjmp, signal stubs, and time stubs.

---

## Phase 2: Stage 1 on SimpleOS

Stage 1 uses the Rust seed to compile the Simple compiler from `.spl` source.

### Host cross-build for SimpleOS

```bash
SIMPLE_BOOTSTRAP=1 \
SIMPLE_LIB=$(pwd)/src \
SIMPLE_TARGET=x86_64-simpleos \
  src/compiler_rust/target/bootstrap/simple \
    native-build \
    --source src/compiler \
    --source src/lib \
    --source src/app \
    --entry src/app/cli/main.spl \
    -o build/bootstrap/stage1_full/simple_simpleos \
    --strip
```

Key considerations:
- `SIMPLE_BOOTSTRAP=1` activates the bootstrap text rewriter (strips `?`, rewrites `.?`, etc.)
- The Rust seed uses Cranelift backend (deterministic, no LLVM required)
- `native-build` is a Rust FFI call (`rt_native_build`) that compiles all discovered `.spl` files, generates object files, and links with clang/lld
- For SimpleOS target, the linker must use the SimpleOS flags from `simpleos_native_build_config.spl`:
  - `-nostdlib -ffreestanding -static`
  - Custom linker script (`simpleos.ld`, places `.text` at `0x10000000`)
  - Link against `libsimpleos_c.a`
  - Include `crt0.o` for startup

### On-SimpleOS native build

If the Rust seed binary is already on SimpleOS (from Phase 1b):

```bash
SIMPLE_BOOTSTRAP=1 \
SIMPLE_LIB=/src \
  /bootstrap/simple \
    native-build \
    --source /src/compiler \
    --source /src/lib \
    --source /src/app \
    --entry /src/app/cli/main.spl \
    -o /build/stage1/simple \
    --strip
```

Requires clang and lld to be available on SimpleOS
(from `src/os/port/llvm/build.spl --cross`).

---

## Phase 3: Stage 2 and 3 (Self-Hosting)

### Stage 2

The Stage 1 binary (built from Simple source) compiles itself:

```bash
SIMPLE_LIB=$(pwd)/src \
  build/bootstrap/stage1_full/simple_simpleos \
    native-build \
    --source src/compiler \
    --source src/lib \
    --source src/app \
    --entry src/app/cli/main.spl \
    -o build/bootstrap/stage2/simple_simpleos \
    --strip
```

Stage 2 no longer needs `SIMPLE_BOOTSTRAP=1` because the Stage 1 binary
is a full Simple compiler (not the Rust seed).

### Stage 3

Stage 2 compiles itself to produce Stage 3:

```bash
SIMPLE_LIB=$(pwd)/src \
  build/bootstrap/stage2/simple_simpleos \
    native-build \
    --source src/compiler \
    --source src/lib \
    --source src/app \
    --entry src/app/cli/main.spl \
    -o build/bootstrap/stage3/simple_simpleos \
    --strip
```

### Convergence

Stage 2 and Stage 3 must be identical (or stub-identical when auto-stubs
are involved). Verification:

```bash
# Exact binary match
diff build/bootstrap/stage2/simple_simpleos build/bootstrap/stage3/simple_simpleos

# If not byte-identical, compare stub counts
nm build/bootstrap/stage2/simple_simpleos | grep "auto_stub" | wc -l
nm build/bootstrap/stage3/simple_simpleos | grep "auto_stub" | wc -l
# Both should report the same count (currently ~2367 stubs)
```

---

## Phase 4: Verification

### Functional Verification

Run the test suite with the SimpleOS-built binary:

```bash
SIMPLE_LIB=$(pwd)/src \
  build/bootstrap/stage3/simple_simpleos test
```

### Cross-Platform Comparison

The SimpleOS binary will differ from the host binary in:
- ELF vs Mach-O format (if host is macOS)
- Platform-specific codegen (syscall conventions, linker flags)
- Linked libraries (libsimpleos_c.a vs system libc)

But should be **functionally identical**:
- Same number of compiled files (~2906)
- Same number of auto-stubs (~2367)
- Same test pass rate

### Smoke Test

Minimal verification that the binary starts:

```bash
# On SimpleOS (or in QEMU)
/build/stage3/simple --version
/build/stage3/simple --help
```

---

## Architecture Diagram

```
Host Machine                              SimpleOS (QEMU/hardware)
============                              ========================

Rust seed (cargo)                         Rust seed (cross-compiled)
    |                                         |
    v                                         v
Stage 1 (SIMPLE_BOOTSTRAP=1)             Stage 1 (SIMPLE_BOOTSTRAP=1)
    |                                         |
    v                                         v
Stage 2 (self-hosted)                     Stage 2 (self-hosted)
    |                                         |
    v                                         v
Stage 3 (verify == Stage 2)              Stage 3 (verify == Stage 2)
```

Cross-compilation shortcut (build on host, deploy to SimpleOS):

```
Host: Rust seed --> Stage 1 --> Stage 2 --> Stage 3
                                              |
                                    [deploy to SimpleOS]
                                              |
SimpleOS:                          Stage 3 ---> runs on SimpleOS
```

---

## Known Issues and Limitations

1. **LLVM backend not usable for bootstrap**: LLVM codegen has runtime crashes
   due to tagged-value ABI handling. Use Cranelift backend only.

2. **Auto-stubs**: ~2367 functions are auto-stubbed (GPU, database, network
   externs that have no SimpleOS implementation). These are expected.

3. **libc coverage**: SimpleOS libc is minimal. Some runtime functions may
   need additional libc support (e.g., locale, wide chars, advanced I/O).

4. **Filesystem**: SimpleOS VFS must support enough file operations for the
   compiler to read source files and write object files.

5. **Memory**: The compiler needs significant memory (~512MB+). SimpleOS
   must support large mmap allocations.

6. **Target triple**: SimpleOS uses `x86_64-unknown-simpleos` (primary),
   with `aarch64-simpleos`, `riscv64gc-simpleos`, `riscv32imac-simpleos`
   also supported.

---

## File References

| File | Purpose |
|------|---------|
| `src/os/port/simpleos_native_build_config.spl` | Linker flags, sysroot paths |
| `src/os/port/llvm/build.spl` | LLVM cross-build (host tools + cross clang) |
| `src/os/port/llvm/sysroot.shs` | Sysroot packaging script |
| `src/os/port/rust/build.spl` | Rust toolchain cross-build |
| `src/os/libc/simpleos_libc.c` | Minimal libc implementation |
| `src/os/libc/Makefile` | Libc build (produces libsimpleos_c.a) |
| `src/os/port/build_tools/simple_make.spl` | Make replacement for SimpleOS |
| `src/app/cli/main.spl` | Full CLI entry point |
| `src/app/cli/bootstrap_main.spl` | Minimal bootstrap entry point |
| `src/os/port/bootstrap_verify.spl` | Bootstrap verification script |
| `src/os/port/bootstrap_cross.spl` | Cross-compilation bootstrap script |
| `src/compiler_rust/Cargo.toml` | Rust seed workspace |
| `src/compiler_rust/driver/Cargo.toml` | Driver crate (produces `simple` binary) |
| `src/compiler_rust/native_all/Cargo.toml` | Static library crate |
