# Porting LLVM to SimpleOS

Build LLVM from the `ormastes/llvm-project` fork for SimpleOS cross-compilation targets.

## Custom Target Triples

| Triple | Architecture | Notes |
|--------|-------------|-------|
| `x86_64-unknown-simpleos` | x86-64 | Primary desktop/server target |
| `aarch64-unknown-simpleos` | AArch64 | ARM64 boards and SBCs |
| `riscv64gc-unknown-simpleos` | RV64GC | RISC-V 64-bit with GC extensions |
| `riscv32imac-unknown-simpleos` | RV32IMAC | RISC-V 32-bit embedded |

## Prerequisites

- CMake >= 3.20
- Ninja
- Host Clang/LLVM >= 17 (for cross-compiling)
- Python 3.8+
- Git

## Getting the Source

```bash
git clone https://github.com/ormastes/llvm-project.git
cd llvm-project
git checkout --detach 3b33ba807a99855133981897fa8c9d91933f759d
```

That commit is the pinned, published SimpleOS toolchain source. Do not copy
changes from a dirty LLVM checkout into this repository.

## Building LLVM for SimpleOS

### Quick Build (x86_64)

```bash
cmake -S llvm -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS="clang;lld" \
  -DLLVM_TARGETS_TO_BUILD="X86;AArch64;RISCV" \
  -DLLVM_DEFAULT_TARGET_TRIPLE="x86_64-unknown-simpleos" \
  -DCMAKE_INSTALL_PREFIX=/opt/simpleos-toolchain

ninja -C build
ninja -C build install
```

### Cross-Compiling for All SimpleOS Targets

```bash
cmake -S llvm -B build -G Ninja \
  -DCMAKE_BUILD_TYPE=Release \
  -DLLVM_ENABLE_PROJECTS="clang;lld;compiler-rt" \
  -DLLVM_TARGETS_TO_BUILD="X86;AArch64;RISCV" \
  -DLLVM_DEFAULT_TARGET_TRIPLE="x86_64-unknown-simpleos" \
  -DCOMPILER_RT_DEFAULT_TARGET_ONLY=OFF \
  -DCOMPILER_RT_BAREMETAL_BUILD=ON \
  -DCMAKE_INSTALL_PREFIX=/opt/simpleos-toolchain

ninja -C build
ninja -C build install
```

### Building compiler-rt for SimpleOS

compiler-rt provides builtins needed by SimpleOS kernel and userspace:

```bash
cmake -S compiler-rt -B build-rt -G Ninja \
  -DCMAKE_C_COMPILER=/opt/simpleos-toolchain/bin/clang \
  -DCMAKE_AR=/opt/simpleos-toolchain/bin/llvm-ar \
  -DCMAKE_NM=/opt/simpleos-toolchain/bin/llvm-nm \
  -DCMAKE_RANLIB=/opt/simpleos-toolchain/bin/llvm-ranlib \
  -DCOMPILER_RT_BAREMETAL_BUILD=ON \
  -DCOMPILER_RT_BUILD_BUILTINS=ON \
  -DCOMPILER_RT_BUILD_SANITIZERS=OFF \
  -DCOMPILER_RT_BUILD_XRAY=OFF \
  -DCOMPILER_RT_BUILD_LIBFUZZER=OFF \
  -DCOMPILER_RT_BUILD_PROFILE=OFF \
  -DCMAKE_C_FLAGS="--target=x86_64-unknown-simpleos -ffreestanding -nostdlib" \
  -DCMAKE_INSTALL_PREFIX=/opt/simpleos-toolchain

ninja -C build-rt
ninja -C build-rt install
```

## SimpleOS Fork Contract

The pinned `ormastes/llvm-project` commit contains all necessary changes. Key changes:

1. **Target triple recognition** -- Adds `simpleos` as a known OS in `llvm/lib/TargetParser/Triple.cpp`
2. **Clang driver** -- SimpleOS driver in `clang/lib/Driver/ToolChains/SimpleOS.cpp` sets default flags (`-ffreestanding`, `-nostdlib`, correct linker)
3. **Clang linker wiring** -- the SimpleOS driver invokes `ld.lld` and appends the installed `lib/simpleos.lds` script
4. **compiler-rt** -- Builtins build configuration for freestanding SimpleOS targets

Files under `patches/` are historical porting notes, not an applicable patch
bundle. To update the pinned source revision, update and verify the fork first,
then change the commit above:

```bash
git fetch upstream
git rebase upstream/main
# Resolve conflicts in SimpleOS-specific files
git push origin simpleos
```

## Using the Toolchain

After installation, compile SimpleOS code with:

```bash
/opt/simpleos-toolchain/bin/clang \
  --target=x86_64-unknown-simpleos \
  -ffreestanding -nostdlib \
  -o output.o -c input.c

/opt/simpleos-toolchain/bin/ld.lld \
  -T linker.ld -o kernel.elf output.o
```

## Automated Build

Use the guarded staged wrapper in this directory. Keep host tools, the cross
compiler, and compiler-rt as separate resumable steps:

```bash
LLVM_SRC=~/llvm-project sh src/os/port/llvm/build.shs host-tools
LLVM_SRC=~/llvm-project SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos \
  sh src/os/port/llvm/build.shs cross
LLVM_SRC=~/llvm-project SIMPLEOS_TARGET_TRIPLE=x86_64-unknown-simpleos \
  sh src/os/port/llvm/build.shs compiler-rt
```
