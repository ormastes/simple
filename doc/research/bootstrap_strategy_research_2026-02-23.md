# Bootstrap Strategy Research: C++ Backend + LLVM Cross-Platform

**Date:** 2026-02-23
**Status:** Research Complete
**Scope:** Bootstrap architecture decisions for Simple language compiler

---

## Executive Summary

This document researches how other languages handle bootstrapping and cross-platform compilation, then evaluates strategies for Simple's bootstrap pipeline. The core question: **should Simple use C++ backend for bootstrap and LLVM backend for cross-platform (Windows/macOS/FreeBSD)?**

**Recommendation:** Yes, with a three-tier architecture modeled after Zig's approach:
- **Tier 1 (Bootstrap):** C backend -> any platform with a C compiler (already partially working)
- **Tier 2 (Development):** Cranelift JIT for fast debug builds
- **Tier 3 (Release/Cross-platform):** LLVM for optimized multi-platform binaries

---

## 1. Current Simple Bootstrap State

### What Exists Today

| Component | Status | Location |
|-----------|--------|----------|
| C backend (MIR -> C++20) | Working | `src/compiler/backend/backend/c_backend.spl` |
| C runtime | Working | `src/runtime/runtime.c` (36 KB) + platform headers |
| CMake build | Working | `src/compiler_cpp/CMakeLists.txt` |
| Stage 1 binary (C-compiled) | 85.9 KB | `bin/bootstrap/cpp/simple` |
| Stage 2 binary (self-compiled) | 164.3 KB | `bin/bootstrap/native/simple` |
| Stage 3 binary (verification) | 164.2 KB | `bin/bootstrap/native/simple_v2` |
| LLVM backend | Working (needs `llc`) | `src/compiler/backend/backend/llvm_backend.spl` |
| Cranelift backend | Working (JIT) | `src/compiler/backend/backend/cranelift.spl` |
| Native backend | Working (x86_64/AArch64/RISC-V) | `src/compiler/backend/backend/native/` |
| Platform headers | Linux/macOS/Windows/FreeBSD/NetBSD/OpenBSD/RISC-V | `src/runtime/platform/` |

### Bootstrap Pipeline (8 stages)

```
check -> bootstrap -> build -> seed -> core1 -> core2 -> full1 -> full2
```

Located in `src/app/build/bootstrap_pipeline.spl`. Currently stages 2-3 still call Cargo (Rust), not the Simple self-compiler.

### Current Blockers

1. SMF compile produces stub bytecode (`ret`-only, no real codegen)
2. `rt_compile_to_llvm_ir` not implemented in bootstrap binary
3. `CompilerDriver` cannot load in interpreter (generics in MIR/HIR types)

---

## 2. How Other Languages Bootstrap

### 2.1 Languages That Bootstrap via C/C++

#### Go — Custom C Dialect -> Self-Hosted

- **History:** Written in Plan 9 C, mechanically translated to Go in 2015 (Go 1.5)
- **Bootstrap anchor:** Go 1.4 (last C version) is the permanent seed
- **Current policy:** Go 1.N requires Go 1.(N-2) to build
- **No LLVM:** Entirely self-hosted with custom backends (Plan 9 assembler heritage)
- **Reproducibility:** Achieved in Go 1.21; verified nightly via `gorebuild`
- **Binary size:** ~15-20 MB compiler, ~100-130 MB full toolchain

**Key insight:** Go proves a language can thrive without LLVM by owning the entire pipeline. Trade-off: code quality is good but not state-of-the-art vs LLVM.

#### Zig — WASM Seed + Multi-Backend (THE reference model)

- **History:** Originally C++ (~80K lines), self-hosted in Zig (~250K lines)
- **Bootstrap artifact:** `zig1.wasm` (~637 KB compressed, committed to repo)
- **Seed interpreter:** 4,000 lines of C99 (WASI interpreter converts WASM -> C)
- **3-stage pipeline:**
  1. WASM -> C -> native `zig1` (requires only C compiler)
  2. `zig1` compiles full Zig compiler -> `zig2`
  3. `zig2` builds production compiler with user-selected backend

**Multi-backend strategy (the key architecture):**

| Build Mode | Backend | Speed | Quality |
|------------|---------|-------|---------|
| Debug (x86_64) | Self-hosted x86_64 | 275ms hello world | Good |
| Release | LLVM | 22.8s hello world | Excellent |
| Exotic targets | C backend | Medium | Good |
| Bootstrap | WASM -> C -> native | One-time | Adequate |

**Result:** Debug compilation is **70% faster** than LLVM path. Memory usage dropped **3x** (9.6 GB -> 2.8 GB).

#### Nim — Committed C Sources (transpiler model)

- **Architecture:** Nim transpiles to C/C++/JS/ObjC — this IS the primary output
- **Bootstrap repos:** `csources_v2`, `csources_v3` — hundreds of generated `.c` files
- **Process:** Build C files with any C compiler -> minimal `nim` -> `koch boot -d:release`
- **Cross-compilation:** Inherent since all output is C. `nim c -d:mingw` cross-compiles to Windows

**Key insight:** If C output IS the language's native output format, bootstrap is trivially solved.

#### Hare — C11 Compiler + QBE Backend (minimalist)

- **Compiler:** Written in C11, deliberately NOT self-hosting
- **Backend:** QBE (~10K lines of C) instead of LLVM
- **Total size:** ~1.4 MB for compiler + backend
- **Philosophy:** Trade expressiveness for extreme simplicity

**Key insight:** Not every language needs to be self-hosting. A C compiler is the simplest seed.

#### D — Partial Self-Hosting

- **Three compilers:** DMD (custom backend), LDC (LLVM), GDC (GCC)
- **Frontend:** Written in D (shared across all three)
- **Backend:** DMD backend in C, LDC/GDC use LLVM/GCC
- **Bootstrap:** DMD 2.067 (last full C++ version) is the seed anchor

### 2.2 Languages That Use LLVM for Cross-Platform

| Language | Self-Hosting? | LLVM Role | Cross-Platform Strategy |
|----------|---------------|-----------|------------------------|
| Rust | Yes | Primary backend | LLVM handles all targets; CI matrix builds |
| Swift | No (C++) | Primary backend | Apple controls all platforms |
| Crystal | Yes | Primary backend | Pre-built binaries per platform |
| Julia | No (C++/LLVM) | JIT backend | LLVM JIT on each platform |
| Kotlin/Native | No (JVM) | Native backend | JVM hosts compiler, LLVM emits native |

### 2.3 GHC (Haskell) — Three Backends for Three Purposes

| Backend | Purpose | When Used |
|---------|---------|-----------|
| NCG (Native) | Performance | Default for all supported archs |
| C (unregistered) | Porting | First step on new platforms |
| LLVM | Max optimization | Scientific/numeric workloads |

**Porting strategy:** Enable C backend -> get Stage 1 working -> implement NCG -> disable C backend.

### 2.4 OCaml — Bytecode VM + Native Compiler

- **`ocamlc`:** Compiles to bytecode, interpreted by `ocamlrun` (portable C VM)
- **`ocamlopt`:** Compiles to native assembly (3-10x faster)
- **Bootstrap:** Bytecode is fully portable; native requires per-arch support
- **`camlboot`:** Achieved bootstrap from scratch (Guile -> MinML -> OCaml bytecode -> OCaml)

---

## 3. Cross-Platform Strategies

### 3.1 How Languages Reach Windows/macOS/FreeBSD

| Strategy | Used By | Pros | Cons |
|----------|---------|------|------|
| **C output + platform C compiler** | Nim, Zig (bootstrap), GHC (porting) | Works everywhere with C | Generated C is ugly, limited optimization |
| **LLVM cross-compilation** | Rust, Swift, Crystal, Zig (release) | Best optimization, many targets | LLVM is 1.5 GB, slow to build |
| **Self-hosted backends per arch** | Go, Zig (debug) | No external deps, fast compilation | Must implement each arch separately |
| **Pre-built binary distribution** | Rust, Crystal, Go | Easy for users | Trust chain, CI infrastructure needed |
| **CI matrix builds** | All modern languages | Native binaries per platform | Requires CI runners per platform |

### 3.2 Platform-Specific Challenges

**Windows:**
- MinGW or MSVC cross-compilation from Linux
- Go: self-contained runtime, `GOOS=windows` just works
- Zig: cross-compiles from any host (`-Dtarget=x86_64-windows-gnu`)
- Crystal: Added Windows native support in 1.11 (2024)

**macOS:**
- macOS SDK is proprietary (must obtain from Apple)
- Cross-compilation requires SDK headers/libraries
- Solution: Build on macOS CI runners (GitHub Actions has ARM64 macOS)

**FreeBSD:**
- Usually Tier 2/3 for most languages
- Cross-compilation feasible with FreeBSD sysroot
- Platform startup code needed (`src/runtime/startup/`)

### 3.3 Simple's Platform Coverage

Simple already has platform headers and startup code for:
- Linux (x86_64, AArch64)
- macOS (x86_64, AArch64)
- Windows (x86_64)
- FreeBSD, NetBSD, OpenBSD
- RISC-V (32/64)
- Baremetal

Located in `src/runtime/platform/` and `src/runtime/startup/`.

---

## 4. Bootstrap Artifact Comparison

| Approach | Artifact Size | Auditability | Portability | Maintenance | Used By |
|----------|--------------|--------------|-------------|-------------|---------|
| **Committed C sources** | 100s of .c files | Medium (machine-generated) | Excellent | Must regenerate periodically | Nim |
| **Committed WASM binary** | ~637 KB compressed | Low (binary) | Excellent (needs C + WASI interpreter) | Update only on breaking changes | Zig |
| **Downloaded prior binary** | 50-200 MB download | Low (trust build servers) | Good (per-platform) | Automatic (CI) | Rust, Go |
| **C compiler (not self-hosting)** | 0 (just C source) | Excellent | Excellent | None | Hare, Swift |
| **Bytecode VM** | Small VM + bytecode | High (VM is simple C) | Excellent | VM rarely changes | OCaml |

---

## 5. Recommended Strategy for Simple

### 5.1 Three-Tier Architecture

Based on the research, the optimal strategy for Simple is a **three-tier** model inspired by Zig but adapted to Simple's existing infrastructure:

```
                    ┌─────────────────────────────────────┐
                    │        Simple Compiler               │
                    └─────────┬───────────┬───────────────┘
                              │           │
              ┌───────────────┼───────────┼───────────────┐
              │               │           │               │
         ┌────▼────┐    ┌─────▼───┐  ┌────▼────┐   ┌─────▼─────┐
         │ C/C++   │    │Cranelift│  │  LLVM   │   │  Native   │
         │ Backend │    │  (JIT)  │  │ Backend │   │  Backend  │
         └────┬────┘    └────┬────┘  └────┬────┘   └─────┬─────┘
              │              │            │               │
         Bootstrap      Development    Release      Embedded/
         + Porting      (fast debug)   + Cross-     Baremetal
                                       platform
```

#### Tier 1: C Backend (Bootstrap + Porting)

**Purpose:** Bootstrap on any platform, port to new platforms

**Pipeline:**
```
Simple source -> MIR -> C++20 -> clang++/g++ -> native binary
```

**What exists:** MIR -> C++20 backend working (`c_backend.spl`, `c_ir_builder.spl`)
**What's needed:**
- Ensure ALL language features translate to C (currently covers basics)
- Test self-compilation through C backend end-to-end
- Generate committed C sources (Nim-style) OR committed binary (Zig-style)

**Recommendation: Committed C sources (Nim model)**

Why Nim-style over Zig-style for Simple:
1. Simple already generates C++20 — this IS the output format
2. C++ sources are partially auditable (more than WASM binary)
3. The runtime (`src/runtime/`) is already C — natural fit
4. CMake + Ninja build already works
5. No need to build a WASI interpreter

**Committed artifact:**
```
src/compiler_cpp/           # Already exists!
  CMakeLists.txt            # Build definition
  main.cpp                  # Generated from src/app/cli/main.spl
  *.c                       # Generated compiler C sources
  real_compiler.c           # Seed compiler (hand-written, self-contained)
```

**Bootstrap chain:**
```
Stage 0: clang/gcc compiles src/compiler_cpp/ -> bin/bootstrap/cpp/simple (85 KB)
Stage 1: Stage 0 compiles Simple compiler source via C backend -> bin1
Stage 2: bin1 compiles Simple compiler source -> bin2
Stage 3: bin2 compiles Simple compiler source -> bin3 (must match bin2)
```

#### Tier 2: Cranelift (Development)

**Purpose:** Fast debug builds during development

**Pipeline:**
```
Simple source -> MIR -> Cranelift IR -> JIT execution / native binary
```

**What exists:** Cranelift backend working, used as default for debug builds
**Advantage:** No external toolchain needed, fast iteration
**Status:** Already the default — no changes needed

#### Tier 3: LLVM (Release + Cross-Platform)

**Purpose:** Optimized binaries for all target platforms

**Pipeline:**
```
Simple source -> MIR -> LLVM IR -> llc -> native binary (any platform)
```

**What exists:** LLVM backend working (`llvm_backend.spl`, `llvm_ir_builder.spl`, `mir_to_llvm.spl`)
**What's needed:**
- Ensure `llc` is available (or bundle it)
- Test cross-compilation: Linux -> Windows, Linux -> macOS, Linux -> FreeBSD
- CI matrix builds for platform-specific releases

**Cross-platform targets via LLVM:**

| Target | Triple | Status |
|--------|--------|--------|
| Linux x86_64 | `x86_64-unknown-linux-gnu` | Primary |
| Linux AArch64 | `aarch64-unknown-linux-gnu` | Platform headers exist |
| macOS x86_64 | `x86_64-apple-darwin` | Platform headers exist |
| macOS AArch64 | `aarch64-apple-darwin` | Platform headers exist |
| Windows x86_64 | `x86_64-pc-windows-msvc` | Platform headers exist |
| FreeBSD x86_64 | `x86_64-unknown-freebsd` | Platform headers exist |
| RISC-V 64 | `riscv64-unknown-linux-gnu` | Target config exists |

### 5.2 Decision: C Backend for Bootstrap

**Why C backend (not LLVM) for bootstrap:**

| Factor | C Backend | LLVM Backend |
|--------|-----------|--------------|
| **Seed dependency** | Any C compiler (gcc/clang/msvc) | LLVM toolchain (~1.5 GB) |
| **Portability** | Runs everywhere | Only where LLVM is available |
| **Build complexity** | `cmake + ninja` (2 commands) | LLVM build + integration |
| **Bootstrap size** | 85 KB binary | 50+ MB binary |
| **Build speed** | Fast (C compilation) | Slow (LLVM optimization) |
| **Code quality** | Good enough for bootstrap | Not needed for bootstrap |

**Why LLVM for cross-platform releases:**

| Factor | C Backend | LLVM Backend |
|--------|-----------|--------------|
| **Optimization** | `-O2` from C compiler | Full LLVM optimization passes |
| **Code quality** | Good | Excellent |
| **Target coverage** | Limited by C runtime availability | All LLVM targets |
| **Debug info** | Basic | Full DWARF/CodeView |
| **LTO** | Compiler-dependent | Built-in |

### 5.3 Implementation Roadmap

#### Phase 1: Complete C Backend Self-Compilation (Current Priority)

```
Goal: bin/bootstrap/cpp/simple can compile the full Simple compiler
```

1. Audit C backend for missing language features
2. Fix any codegen gaps found during self-compilation
3. Verify 3-stage bootstrap produces identical binaries (Stage 2 == Stage 3)
4. Update committed C sources in `src/compiler_cpp/`

#### Phase 2: LLVM Cross-Platform Pipeline

```
Goal: simple build --release --target=<platform> produces optimized binaries
```

1. Implement `--target` flag in build system
2. Test LLVM IR generation for each target triple
3. Link against platform-specific runtime (`src/runtime/platform/`)
4. Set up CI matrix builds (GitHub Actions)

#### Phase 3: Reproducible Bootstrap

```
Goal: Anyone can verify the bootstrap chain from C source
```

1. Document the full bootstrap chain
2. Implement deterministic compilation (strip timestamps, normalize paths)
3. Create verification script (compare Stage 2 and Stage 3 outputs)
4. Consider diverse double-compiling (DDC) for Trusting Trust defense

#### Phase 4: Platform Distribution

```
Goal: Pre-built binaries for all tier-1 platforms
```

1. Create release pipeline in CI
2. Package format per platform (`.spk`, `.deb`, `.pkg`, `.msi`)
3. Distribute via GitHub releases + package managers

---

## 6. Comparison with Other Languages' Choices

### What Simple Can Learn From Each

| Language | Lesson for Simple |
|----------|-------------------|
| **Zig** | Three-tier backend architecture (fast debug / optimized release / portable bootstrap) |
| **Go** | Self-contained toolchain is achievable; reproducible builds matter |
| **Nim** | Committing generated C is practical and battle-tested |
| **Rust** | LLVM provides excellent cross-platform coverage; mrustc shows value of alternative bootstrap path |
| **GHC** | C backend for porting, native for performance — same tier separation |
| **OCaml** | Bytecode VM is another portable bootstrap option (less relevant for Simple) |
| **Hare** | Simplicity has value; QBE is an option if LLVM is too heavy |

### Simple's Unique Advantages

1. **C runtime already exists** (`src/runtime/`) — 36 KB of C with platform headers
2. **C backend already works** — MIR -> C++20 pipeline is functional
3. **Multiple backends already exist** — Cranelift, LLVM, C, Native, WASM, CUDA, Vulkan
4. **Platform startup code ready** — Linux, macOS, Windows, FreeBSD, RISC-V, baremetal
5. **Small bootstrap binary** — 85 KB (Stage 1) vs Go's 15 MB or Rust's 50 MB
6. **Committed C sources already in repo** — `src/compiler_cpp/` with CMakeLists.txt

### Simple's Unique Challenges

1. **Self-compilation not complete** — Stages 2-3 still invoke Cargo (Rust)
2. **Generics block CompilerDriver in interpreter** — Runtime parser limitation
3. **LLVM backend needs `llc` binary** — Not self-contained
4. **Pre-built runtime is Rust binary** — `bin/release/simple` is 33 MB Rust

---

## 7. Windows Cross-Compilation: MSVC vs MinGW

### The Two ABIs

LLVM can produce Windows binaries via two different ABIs:

| ABI | Target Triple | SDK Needed? | Static Linking | Runtime DLLs |
|-----|--------------|-------------|----------------|--------------|
| **MinGW/GNU** | `x86_64-w64-mingw32` | No (MinGW headers suffice) | Full static possible | `kernel32.dll` + `ucrtbase.dll` only |
| **MSVC** | `x86_64-pc-windows-msvc` | Yes (Windows SDK + CRT) | Partial (`/MT` flag) | `vcruntime140.dll` + `ucrtbase.dll` |

### Recommendation: MinGW (llvm-mingw) for Cross-Compilation

**MinGW is far easier** for cross-compilation from Linux. MSVC requires downloading the Windows SDK.

### Path 1: llvm-mingw (Recommended)

Pre-built Clang toolchain with MinGW headers bundled. Full C++20 support.

```bash
# Download llvm-mingw (one-time)
wget https://github.com/mstorsjo/llvm-mingw/releases/download/20241119/llvm-mingw-20241119-ucrt-ubuntu-20.04-x86_64.tar.xz
tar -xf llvm-mingw-*.tar.xz -C /opt/
export PATH=/opt/llvm-mingw-*/bin:$PATH

# Cross-compile Simple's C++20 output to Windows
x86_64-w64-mingw32-clang++ -std=c++20 -static -o simple.exe \
    main.cpp runtime.c runtime_thread.c runtime_memtrack.c runtime_fork.c
```

**Output:** Fully static `.exe`, only needs `kernel32.dll` + `ucrtbase.dll` (built into Windows 10+).

### Path 2: System MinGW-w64

```bash
sudo apt install gcc-mingw-w64-x86-64 g++-mingw-w64-x86-64

x86_64-w64-mingw32-g++ -std=c++20 -static -static-libgcc -static-libstdc++ \
    -o simple.exe main.cpp runtime.c
```

### Path 3: MSVC ABI (Only if MSVC interop needed)

Requires `xwin` tool to download Windows SDK headers/libs from Microsoft CDN:

```bash
cargo install xwin
xwin --accept-license splat --output /xwin

clang++ --target=x86_64-pc-windows-msvc -fuse-ld=lld-link -std=c++20 \
    -I/xwin/crt/include -I/xwin/sdk/include/ucrt \
    -I/xwin/sdk/include/um -I/xwin/sdk/include/shared \
    -L/xwin/crt/lib/x86_64 -L/xwin/sdk/lib/um/x86_64 \
    -L/xwin/sdk/lib/ucrt/x86_64 \
    -o simple.exe main.cpp runtime.c
```

### Path 4: Zig as C/C++ Cross-Compiler

Zig bundles MinGW headers internally. Zero external dependencies:

```bash
zig c++ -target x86_64-windows-gnu -std=c++20 -o simple.exe main.cpp runtime.c
```

### CMake Cross-Compilation Toolchain

For Simple's CMake-based bootstrap build:

```cmake
# toolchain-windows-mingw.cmake
set(CMAKE_SYSTEM_NAME Windows)
set(CMAKE_SYSTEM_PROCESSOR x86_64)
set(CMAKE_C_COMPILER x86_64-w64-mingw32-clang)
set(CMAKE_CXX_COMPILER x86_64-w64-mingw32-clang++)
set(CMAKE_RC_COMPILER x86_64-w64-mingw32-windres)
set(CMAKE_FIND_ROOT_PATH_MODE_PROGRAM NEVER)
set(CMAKE_FIND_ROOT_PATH_MODE_LIBRARY ONLY)
set(CMAKE_FIND_ROOT_PATH_MODE_INCLUDE ONLY)
```

```bash
cmake -B build-win -G Ninja \
    -DCMAKE_TOOLCHAIN_FILE=toolchain-windows-mingw.cmake \
    -S src/compiler_cpp
ninja -C build-win
# Produces: build-win/simple.exe
```

### LLVM Backend for Windows

When Simple's LLVM backend generates LLVM IR, the cross-compilation to Windows is:

```bash
# Generate LLVM IR (Simple -> LLVM IR)
simple compile --backend=llvm -o program.ll source.spl

# Cross-compile IR to Windows (LLVM toolchain)
llc -mtriple=x86_64-w64-mingw32 -filetype=obj -o program.obj program.ll
x86_64-w64-mingw32-clang++ program.obj -o program.exe -static
```

### Binary Size Comparison (Windows)

| Method | Static | Approx Size | Runtime DLLs |
|--------|--------|-------------|--------------|
| MinGW static | Yes | 1-5 MB | kernel32, ucrtbase |
| MSVC `/MT` | Yes | 0.5-3 MB | kernel32 |
| MSVC `/MD` | No | 0.3-2 MB | kernel32, ucrtbase, vcruntime140 |
| MinGW dynamic | No | 0.3-2 MB | kernel32, ucrtbase, libstdc++, libgcc, libwinpthread |

### Recommendation for Simple

**Use llvm-mingw for CI cross-compilation to Windows.** Reasons:

1. Zero SDK download — llvm-mingw bundles everything
2. Full C++20 support (Clang-based)
3. Produces fully static `.exe` with no MinGW DLL dependencies
4. Also supports ARM64 Windows (`aarch64-w64-mingw32`)
5. Works with Simple's existing CMake build via toolchain file
6. MSVC ABI only needed if linking against MSVC-compiled libraries (not our case)

For the LLVM backend path, target `x86_64-w64-mingw32` in the LLVM IR and link with MinGW.

---

## 8. macOS and FreeBSD Cross-Compilation

### macOS

**Challenge:** macOS SDK is proprietary. Cross-compilation from Linux requires SDK headers.

| Method | How | Complexity |
|--------|-----|------------|
| **Build on macOS CI** | GitHub Actions macOS runner | Easy (recommended) |
| **osxcross** | Open-source macOS cross-toolchain for Linux | Medium |
| **Zig cc** | `zig c++ -target aarch64-macos` | Easy but limited |

**Recommended:** Build natively on GitHub Actions macOS ARM64 runner. No SDK license issues.

```yaml
# GitHub Actions
jobs:
  build-macos:
    runs-on: macos-14  # ARM64 (Apple Silicon)
    steps:
      - run: |
          cmake -B build -G Ninja -S src/compiler_cpp
          ninja -C build
```

### FreeBSD

**Options:**
1. **Cross-compile from Linux** with FreeBSD sysroot
2. **Build on FreeBSD CI** (GitHub Actions has no FreeBSD runner, use Cirrus CI)
3. **C backend + system compiler** — Just compile `src/compiler_cpp/` on FreeBSD with clang

**Simplest:** Ship committed C sources. FreeBSD users compile with their system clang:

```bash
cmake -B build -G Ninja -S src/compiler_cpp
ninja -C build
```

Simple's runtime already has FreeBSD platform headers (`src/runtime/platform/`).

---

## 9. Alternative Approaches Considered

### Option A: Zig-Style WASM Bootstrap (Rejected)

**What:** Compile Simple compiler to WASM, commit it, include WASI interpreter
**Why rejected:** Simple doesn't have a WASM self-compilation path yet. The C backend is simpler and already works.

### Option B: Go-Style Full Self-Hosting (Deferred)

**What:** Eliminate LLVM entirely, implement all backends in Simple
**Why deferred:** LLVM provides too much value for cross-platform optimization. May revisit when native backends mature.

### Option C: Download Prior Binary (Rust-Style) (Rejected)

**What:** Download pre-built Simple binary as Stage 0
**Why rejected:** Creates trust dependency on build servers. Simple already has committed C sources — use them.

### Option D: Don't Self-Host (Hare-Style) (Rejected)

**What:** Keep compiler in Rust permanently
**Why rejected:** Self-hosting is a project goal. The C backend bootstrap is nearly complete.

### Option E: Bytecode VM Bootstrap (OCaml-Style) (Interesting but deferred)

**What:** Create a Simple bytecode VM in C, compile compiler to bytecode, use as seed
**Why deferred:** More infrastructure to build. C backend achieves the same portability with less effort. Could revisit for faster bootstrap.

---

## 10. Security Considerations

### The Trusting Trust Problem

Ken Thompson's 1984 insight: a backdoor in a compiler binary can perpetuate itself through all subsequent compiles, even from clean source.

### Mitigation Strategies for Simple

1. **Committed C sources are auditable** — Anyone can read `src/compiler_cpp/*.c`
2. **Three-stage verification** — Stage 2 and Stage 3 must produce identical output
3. **Diverse Double-Compiling (DDC)** — Compile with two different C compilers (gcc AND clang), compare results
4. **Alternative bootstrap path** — The `real_compiler.c` (seed compiler, 2422 lines) is hand-written and reviewable

### Recommended Verification Pipeline

```
# Build with clang
cmake -B build-clang -G Ninja -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
ninja -C build-clang

# Build with gcc
cmake -B build-gcc -G Ninja -DCMAKE_C_COMPILER=gcc -S src/compiler_cpp
ninja -C build-gcc

# Both should produce functionally identical Simple compilers
# (binary diff may differ due to compiler codegen, but output must match)
build-clang/simple compile test.spl -o test-clang
build-gcc/simple compile test.spl -o test-gcc
diff test-clang test-gcc  # Must be identical
```

---

## 11. Summary of Recommendations

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Bootstrap backend | **C (C++20)** | Already works, any C compiler suffices, 85 KB binary |
| Bootstrap artifact | **Committed C sources** (Nim model) | Already in `src/compiler_cpp/`, auditable, no binary blob |
| Development backend | **Cranelift** | Already default, fast JIT, no external deps |
| Release backend | **LLVM** | Best optimization, all target platforms |
| Cross-platform strategy | **LLVM cross-compilation + CI matrix** | Industry standard, platform headers ready |
| Verification | **3-stage + DDC** | Detect Trusting Trust, ensure reproducibility |

**Priority order:**
1. Complete C backend self-compilation (unblock full bootstrap)
2. Verify 3-stage bootstrap chain (Stage 2 == Stage 3)
3. LLVM cross-compilation for Windows/macOS/FreeBSD
4. CI matrix builds for automated releases
5. Reproducible build verification

---

## 12. References

### Languages Researched

- **Go:** [go.dev/doc/install/source](https://go.dev/doc/install/source), [Perfectly Reproducible Builds](https://go.dev/blog/rebuild)
- **Zig:** [Goodbye C++ Implementation](https://ziglang.org/news/goodbye-cpp/), [Self-Hosted Now What](https://kristoff.it/blog/zig-self-hosted-now-what/)
- **Rust:** [Bootstrapping Guide](https://rustc-dev-guide.rust-lang.org/building/bootstrapping/what-bootstrapping-does.html), [mrustc](https://github.com/thepowersgang/mrustc)
- **Nim:** [csources_v2](https://github.com/nim-lang/csources_v2), [Compiler Guide](https://nim-lang.org/docs/nimc.html)
- **Hare:** [Announcement](https://harelang.org/blog/2022-04-25-announcing-hare/), [QBE](https://c9x.me/compile/)
- **GHC:** [Backends](http://downloads.haskell.org/ghc/latest/docs/users_guide/codegens.html)
- **OCaml:** [Compiler Backend](https://ocaml.org/docs/compiler-backend), [camlboot](https://github.com/Ekdohibs/camlboot)
- **D:** [LDC](https://github.com/ldc-developers/ldc)

### Windows Cross-Compilation

- **llvm-mingw:** [github.com/mstorsjo/llvm-mingw](https://github.com/mstorsjo/llvm-mingw)
- **xwin (MSVC SDK from Linux):** [jake-shadle.github.io/xwin](https://jake-shadle.github.io/xwin/)
- **cargo-xwin:** [github.com/rust-cross/cargo-xwin](https://github.com/rust-cross/cargo-xwin)
- **Zig as cross-compiler:** [andrewkelley.me/post/zig-cc](https://andrewkelley.me/post/zig-cc-powerful-drop-in-replacement-gcc-clang.html)

### Security & Reproducibility

- [Bootstrappable Builds](https://bootstrappable.org/)
- [GNU Guix Full-Source Bootstrap](https://guix.gnu.org/blog/2023/the-full-source-bootstrap-building-from-source-all-the-way-down/)
- [Diverse Double-Compiling](https://dwheeler.com/trusting-trust/)
- [Thompson's Reflections on Trusting Trust](https://www.cs.cmu.edu/~rdriley/487/papers/Thompson_1984_ReflsectionsonTrustingTrust.pdf)
