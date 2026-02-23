# Self-Hosting Bootstrap Plan (2026-02-21)

## Overview

Three-stage pipeline to produce a fully self-hosted Simple compiler:

```
Stage 0  bin/simple (interpreter, 33MB)
   |
   | compile --backend=c  → src/compiler_cpp/*.c
   |
Stage 1  clang/cmake/ninja → bin/bootstrap/cpp/simple  (bin1, C-backend compiled)
   |
   | bin1 compile --backend=c  → build/stage2/src/*.c
   |
Stage 2  clang/cmake/ninja → bin/bootstrap/native/simple  (bin2, Simple-compiled)
   |
   | bin2 compile --backend=c  → build/stage3/src/*.c
   |
Stage 3  clang/cmake/ninja → build/stage3/simple  (bin3, self-hosting verify)
```

Self-hosting is verified when `bin2 ≡ bin3` (same output for same input).

---

## Current State

| Artifact | Path | Size | How Built |
|----------|------|------|-----------|
| Full interpreter | `bin/simple` | 33MB | Rust runtime |
| Seed compiler (hand-written) | `bin/bootstrap/cpp/simple` | 26KB | `src/compiler_cpp/real_compiler.c` via clang |
| Native bootstrap | `bin/bootstrap/native/simple` | 164KB | unknown |

Key directories:
- **C backend (app layer)**: `src/app/compile/` — mini C codegen, all fixed to `r"" + variable`
- **C backend (compiler layer)**: `src/compiler/70.backend/backend/c_backend.spl` — full IR → C
- **C output directory**: `src/compiler_cpp/` — contains `real_compiler.c` (seed, hand-written)
- **Runtime**: `src/runtime/runtime.c` + `runtime.h`
- **CMakeLists**: `src/compiler_cpp/CMakeLists.txt` — picks up all `.c`/`.cpp` files via glob

Toolchain available: `clang`, `cmake`, `ninja` all at `/usr/bin/`

---

## Stage 0 — Prerequisites Check

```bash
# Verify toolchain
clang --version
cmake --version
ninja --version

# Verify runtime sources exist
ls src/runtime/runtime.c src/runtime/runtime.h

# Verify current interpreter works
bin/simple --version || bin/simple help
```

---

## Stage 1 — Generate C + Build bin1

**Goal**: Use `bin/simple compile --backend=c` to compile the full Simple compiler
source into C, then build a native binary with clang.

### Step 1a: Generate C from compiler source

```bash
# Generate C output into src/compiler_cpp/
# This overwrites/supplements real_compiler.c with generated files
bin/simple compile --backend=c -o src/compiler_cpp/ src/app/cli/main.spl
```

Expected output: one or more `.c` files in `src/compiler_cpp/` representing
the full compiler. The CMakeLists.txt globs all `*.c`/`*.cpp` files there.

> **Check**: Inspect generated file size — should be much larger than the
> 1175-line hand-written `real_compiler.c`. If output is tiny/empty, the
> C backend is not yet generating full output (see Obstacles below).

### Step 1b: Build with cmake + ninja

```bash
cmake -B build/bootstrap/cpp \
  -G Ninja \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -S src/compiler_cpp

ninja -C build/bootstrap/cpp
```

### Step 1c: Install as bin1

```bash
mkdir -p bin/bootstrap/cpp
cp build/bootstrap/cpp/simple bin/bootstrap/cpp/simple
chmod +x bin/bootstrap/cpp/simple
```

### Step 1d: Verify bin1

```bash
bin/bootstrap/cpp/simple --help
# or
bin/bootstrap/cpp/simple --version
```

---

## Stage 2 — bin1 Compiles Simple Source → bin2

**Goal**: Use bin1 (C-backend compiled) to re-compile the Simple compiler source.
This is the first time a Simple-generated binary compiles the compiler.

### Step 2a: Generate C using bin1

```bash
mkdir -p build/stage2/src
bin/bootstrap/cpp/simple compile --backend=c \
  -o build/stage2/src/ \
  src/app/cli/main.spl
```

### Step 2b: Build bin2

```bash
# Copy CMakeLists.txt so the build system works
cp src/compiler_cpp/CMakeLists.txt build/stage2/src/

cmake -B build/stage2/build \
  -G Ninja \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -S build/stage2/src

ninja -C build/stage2/build
```

### Step 2c: Install as bin2

```bash
mkdir -p bin/bootstrap/native
cp build/stage2/build/simple bin/bootstrap/native/simple
chmod +x bin/bootstrap/native/simple
```

### Step 2d: Verify bin2

```bash
bin/bootstrap/native/simple --help
# Run a small test
echo 'fn main(): print "hello"' > /tmp/hello.spl
bin/bootstrap/native/simple compile --backend=c /tmp/hello.spl
```

---

## Stage 3 — bin2 Compiles Simple Source → bin3 (Self-hosting Verify)

**Goal**: Use bin2 (Simple-compiled) to re-compile the Simple compiler source.
If bin3 ≡ bin2 in behavior, self-hosting is proven.

### Step 3a: Generate C using bin2

```bash
mkdir -p build/stage3/src
bin/bootstrap/native/simple compile --backend=c \
  -o build/stage3/src/ \
  src/app/cli/main.spl
```

### Step 3b: Build bin3

```bash
cp src/compiler_cpp/CMakeLists.txt build/stage3/src/

cmake -B build/stage3/build \
  -G Ninja \
  -DCMAKE_C_COMPILER=clang \
  -DCMAKE_CXX_COMPILER=clang++ \
  -S build/stage3/src

ninja -C build/stage3/build
```

### Step 3c: Verify self-hosting

```bash
# Hash comparison (exact binary reproducibility)
sha256sum build/stage2/build/simple build/stage3/build/simple

# Functional equivalence (if hashes differ due to timestamps/randomness)
bin2=build/stage2/build/simple
bin3=build/stage3/build/simple

# Both should produce the same C output for the same input
$bin2 compile --backend=c /tmp/hello.spl -o /tmp/out2.c
$bin3 compile --backend=c /tmp/hello.spl -o /tmp/out3.c
diff /tmp/out2.c /tmp/out3.c
```

Self-hosting is proven if `diff` shows no differences (or only deterministic ones).

---

## Obstacle Analysis

### 1. C Backend Coverage

The full compiler (`src/compiler/`) uses advanced features (generics, traits,
async, etc.) that the mini-backend may not handle.

**Mitigation**: The full compiler backend at
`src/compiler/70.backend/backend/c_backend.spl` + `c_ir_builder.spl` is the
intended path for full-compiler bootstrap. The `--backend=c` flag routes to
whichever backend is wired in the driver.

**Check which backend `--backend=c` uses**:
```bash
grep -n "backend.*c\|c.*backend\|backend_c" \
  src/compiler/80.driver/driver.spl | head -20
```

### 2. String Interpolation (Fixed)

All C codegen files have been converted from `"{variable}"` to
`r"" + variable` to prevent Simple's interpolation engine from corrupting
generated C source. Files fixed:

- ✅ `src/app/compile/c_helpers.spl`
- ✅ `src/app/compile/c_codegen_defs.spl`
- ✅ `src/app/compile/c_runtime.spl`
- ✅ `src/app/compile/c_translate_decl.spl`
- ✅ `src/app/compile/c_translate_expr.spl`
- ✅ `src/app/compile/c_translate_stmt.spl`
- ✅ `src/compiler/70.backend/backend/c_backend.spl`
- ✅ `src/compiler/70.backend/backend/c_ir_builder.spl`

### 3. Runtime Completeness

The embedded runtime in `real_compiler.c` may be a subset of the full
`src/runtime/runtime.c`. When building with CMakeLists.txt, both are
linked (unless `SELF_CONTAINED=ON`). The generated C should work with the
full runtime.

**Conflict risk**: If generated C embeds partial runtime AND links full
`runtime.c` from `src/runtime/`, there will be duplicate symbol errors.
Use `SELF_CONTAINED=OFF` (default) to let the generated C rely on external runtime.

### 4. Non-Deterministic Output

If the compiler uses timestamps, temp filenames, or hash-based labels,
bin2 ≠ bin3 in bytes. This is acceptable if functional equivalence holds
(same output for same input).

### 5. Missing Features in C Backend

The C backend may not handle:
- Closures / lambda captures → need C function pointer + context struct
- Async/await → needs state machine expansion first
- Generics → needs monomorphization before C emission
- Traits → need vtable generation

The full pipeline should monomorphize and lower these before the C backend
runs. Verify by checking if the generated C is human-readable "flat" C with
no generics.

---

## Existing Pipeline Infrastructure

The project already has a sophisticated bootstrap pipeline in
`src/app/build/bootstrap_pipeline.spl` with 8 stages:

```
check → bootstrap → build → seed → core1 → core2 → full1 → full2
```

This user's 3-stage plan maps to:
- Stage 1 (bin1) ≈ `core1` stage
- Stage 2 (bin2) ≈ `core2`/`full1` stage
- Stage 3 (bin3) ≈ `full2` stage (reproducibility check)

**Consider invoking the existing pipeline** for stages that already have
working logic:
```bash
bin/simple build --bootstrap --from-stage=seed --to-stage=full2
```

---

## Success Criteria

| Stage | Success Condition |
|-------|------------------|
| Stage 1 | `bin/bootstrap/cpp/simple --help` works, binary > 1MB |
| Stage 2 | `bin/bootstrap/native/simple --help` works; compiles hello.spl |
| Stage 3 | bin2 and bin3 produce identical output for identical input |

---

## Immediate Next Step

Try Stage 1 to see the current state:

```bash
# First, probe what the C backend currently generates:
bin/simple compile --backend=c -o /tmp/test_gen/ src/app/cli/main.spl 2>&1 | head -50
ls -la /tmp/test_gen/
```

This reveals whether the backend is functional or what errors block it.
