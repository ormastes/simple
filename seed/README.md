# Simple Language Seed Compiler

The seed compiler is a minimal C/C++ transpiler that bootstraps the Simple language compiler from scratch.

## Overview

**Purpose:** Bootstrap the Simple compiler on systems with no existing Simple binary
**Language:** C (seed.c) and C++ (seed.cpp)
**Output:** Transpiles Simple (.spl) → C++ code
**Runtime:** Minimal C runtime library (runtime.c/h)

## Requirements

### Compiler (Clang Family Only)

- **Clang 20+** (recommended) or **Clang 15+** (minimum)
- C compiler: `clang` or `clang-20`
- C++ compiler: `clang++` or `clang++-20`
- **C++20 standard** support required
- **Note:** GCC is not supported. Use Clang family compilers only.

### Build Tools

- **CMake** 3.15 or newer
- **Ninja** (recommended) or Make
- Standard POSIX tools (sh, sed, find, etc.)

### Installation (Ubuntu/Debian)

```bash
# Add LLVM apt repository for Clang 20
wget -O - https://apt.llvm.org/llvm-snapshot.gpg.key | sudo apt-key add -
sudo add-apt-repository "deb http://apt.llvm.org/$(lsb_release -sc)/ llvm-toolchain-$(lsb_release -sc)-20 main"

# Install Clang 20 + build tools
sudo apt update
sudo apt install clang-20 cmake ninja-build

# Set as default (optional)
sudo update-alternatives --install /usr/bin/clang clang /usr/bin/clang-20 100
sudo update-alternatives --install /usr/bin/clang++ clang++ /usr/bin/clang++-20 100
```

## Quick Build

```bash
# From seed/ directory
mkdir -p build
cd build

# Configure with CMake + Ninja
cmake -G Ninja -DCMAKE_CXX_COMPILER=clang++-20 -DCMAKE_C_COMPILER=clang-20 ..

# Build all targets
ninja

# Verify build
./runtime_test   # Should show: All 202 tests passed
./seed_cpp --help 2>&1 | head -5
```

## Build Targets

| Target | Description | Output |
|--------|-------------|--------|
| `seed` | C version of seed compiler | `build/seed` |
| `seed_cpp` | C++ version of seed compiler | `build/seed_cpp` |
| `spl_runtime` | Static runtime library | `build/libspl_runtime.a` |
| `runtime_test` | Runtime test suite (202 tests) | `build/runtime_test` |
| `seed_test` | Seed compiler test suite | `build/seed_test` |
| `spl_crt_*` | Platform-specific C runtime startup | `build/startup/libspl_crt_*.a` |

## Architecture

```
seed/
├── seed.c               # C version of seed compiler
├── seed.cpp             # C++ version (main transpiler)
├── runtime.c/h          # Minimal C runtime (strings, arrays, I/O)
├── runtime_thread.c/h   # Threading support
├── runtime_test.c       # Runtime test suite (202 tests)
├── seed_test.cpp        # Seed compiler tests
├── startup/             # Platform-specific CRT startup code
│   ├── common/          # Common CRT functions
│   ├── linux/           # Linux x86_64 startup (_start, syscalls)
│   ├── freebsd/         # FreeBSD startup
│   └── macos/           # macOS startup
├── platform/            # Platform detection and configuration
└── CMakeLists.txt       # CMake build configuration
```

## Usage

### Transpile Simple to C++

```bash
# Single file
./build/seed_cpp example.spl > example.cpp

# Multiple files (order matters: __init__.spl first, main.spl last)
./build/seed_cpp __init__.spl module1.spl module2.spl main.spl > output.cpp
```

### Compile Generated C++

```bash
# Link with runtime library
clang++ -std=c++20 -O2 -I../seed output.cpp \
  -L../seed/build -lspl_runtime -lm -lpthread -ldl \
  -o binary

./binary
```

## Standards and Flags

### C++ Compilation

- **Standard:** C++20 (`-std=c++20` or `-std=gnu++20`)
- **Optimization:** `-O2` for production, `-g` for debug
- **Warnings:** `-Wall -Wextra -Wno-unused-parameter`
- **Memory Model:** `-mcmodel=large` (for large programs)

### C Compilation

- **Standard:** C11 (`-std=gnu11`)
- **Same flags as C++**

## Testing

```bash
# Run runtime tests (202 tests)
./build/runtime_test
# Output: === All 202 tests passed ===

# Run seed compiler tests
SEED_CPP=./build/seed_cpp ./build/seed_test
# Output: Test results with pass/fail counts

# Run all tests
ninja test
# Or with Make:
make test
```

## Platform Support

| Platform | Architecture | CRT Startup | Toolchain | Status |
|----------|--------------|-------------|-----------|--------|
| Linux | x86_64 | ✅ `start.S` | Clang/GCC | Verified |
| Linux | ARM64 | ✅ `start_arm64.S` | Clang/GCC | Supported |
| Linux | RISC-V 64 | ✅ `start_riscv64.S` | Clang/GCC | Supported |
| FreeBSD | x86_64 | ✅ `start.S` | Clang/GCC | Supported |
| macOS | x86_64, ARM64 | ⚠️  Uses system CRT | Clang | Supported |
| Windows | x86_64 | ✅ `crt_windows.c` | ClangCL (MSVC ABI) | ✅ Supported |
| Windows | x86_64 | ✅ `crt_windows.c` | MinGW Clang (GCC ABI) | ✅ Supported |
| Windows | x86_64 (cross) | ✅ `crt_windows.c` | MinGW Cross (Linux) | ✅ Supported |

**Windows builds:** See [WINDOWS_BUILD.md](WINDOWS_BUILD.md) for detailed instructions on building with ClangCL or MinGW Clang.

## Limitations

The seed compiler is intentionally minimal and has several limitations:

1. **Simple code only** - Cannot transpile complex compiler_core (441 files)
2. **No type checking** - Assumes input is valid Simple code
3. **Basic error messages** - Limited diagnostic information
4. **No optimization** - Generates straightforward C++ translation
5. **Limited language features** - Subset of full Simple language

**For full compiler:** Use the bootstrapped `bin/release/simple` binary.

## Troubleshooting

### "clangcc not found" error
**Cause:** Bootstrap script bug (fixed in commit XXX)
**Fix:** Use script from main branch or specify: `--cc=clang++`

### Segmentation fault during transpilation
**Cause:** seed_cpp has limited capacity for complex code
**Fix:** Use pre-built bootstrap binary or simplify input code

### "No Clang compiler found"
**Cause:** Clang not installed or not in PATH
**Fix:** Install Clang 20+ (see Installation section above)

### Tests fail with "undefined reference"
**Cause:** Runtime library not linked correctly
**Fix:** Ensure `-lspl_runtime -lm -lpthread -ldl` flags are present

## Development

### Modifying the Seed Compiler

```bash
# Edit seed.cpp
vim seed.cpp

# Rebuild
cd build && ninja seed_cpp

# Test changes
SEED_CPP=./seed_cpp ./seed_test
```

### Modifying the Runtime

```bash
# Edit runtime.c
vim runtime.c

# Rebuild and test
cd build && ninja runtime_test && ./runtime_test
```

## Bootstrap Chain

The seed compiler is **Step 1** of the full bootstrap:

```
Step 0: Pre-built binary (bin/release/simple)
  ↓
Step 1: Seed compiler (seed/build/seed_cpp) ← YOU ARE HERE
  ↓
Step 2: Core1 (seed_cpp transpiles compiler_core → native)
  ↓
Step 3: Core2 (Core1 self-compiles)
  ↓
Step 4: Full1 (Core2 compiles full compiler)
  ↓
Step 5: Full2 (Full1 self-compiles for reproducibility)
```

See `../script/bootstrap-from-scratch.sh` for the complete bootstrap process.

## License

Part of the Simple Language project. See top-level LICENSE file.

## References

- **Main Project:** `../README.md`
- **Bootstrap Script:** `../script/bootstrap-from-scratch.sh`
- **Windows Build Guide:** `WINDOWS_BUILD.md` (ClangCL and MinGW instructions)
- **Platform API:** `platform/PLATFORM_API.md` (Platform abstraction layer)
- **Architecture:** `ARCHITECTURE.md` (Seed compiler design)
- **Runtime Tests:** `runtime_test.c` (202 test cases)
- **Seed Tests:** `seed_test.cpp` (C++ transpilation tests)
