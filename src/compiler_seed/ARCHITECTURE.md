# Seed Compiler Architecture

## Overview

The Simple language uses a **unified seed compiler** that compiles identically on all platforms.
Platform differences are **completely isolated** to header files in `src/compiler_seed/platform/`.

**Key Principle**: The same `seed.c` and `seed.cpp` source files build on Windows, Linux, macOS, and FreeBSD without any changes.

## Bootstrap Chain

```
┌─────────────────────────────────────────────────────────────┐
│  Phase 0: Native C/C++ Compiler (clang, gcc, MSVC)         │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│  Phase 1: Build seed_cpp (C++ transpiler)                   │
│  - Input:  src/compiler_seed/seed.cpp + platform headers                 │
│  - Output: seed_cpp binary (platform-native)                │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│  Phase 2: Transpile Core Simple → C++                       │
│  - Input:  src/core/*.spl (Core Simple subset)              │
│  - Tool:   seed_cpp                                          │
│  - Output: C++ code                                          │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│  Phase 3: Build core_compiler                               │
│  - Input:  C++ code + runtime.c + startup CRT               │
│  - Tool:   clang++/g++/MSVC                                  │
│  - Output: core_compiler binary                             │
└─────────────────────────────────────────────────────────────┘
                           │
                           ▼
┌─────────────────────────────────────────────────────────────┐
│  Phase 4: Build full Simple compiler                        │
│  - Input:  src/compiler/*.spl (Full Simple)                 │
│  - Tool:   core_compiler                                     │
│  - Output: Full Simple compiler                             │
└─────────────────────────────────────────────────────────────┘
```

## Directory Structure

```
seed/
├── seed.c                  # Simple → C transpiler (2,067 lines)
├── seed.cpp                # Core Simple → C++ transpiler (4,296 lines)
├── runtime.c               # Runtime library (1,003 lines)
├── runtime.h               # Runtime interface
├── CMakeLists.txt          # Cross-platform build configuration
│
├── platform/               # Platform abstraction layer
│   ├── platform.h              # Dispatcher (auto-selects platform)
│   ├── PLATFORM_API.md         # API contract documentation
│   │
│   ├── unix_common.h           # Shared POSIX implementation (415 lines)
│   ├── platform_linux.h        # Linux: includes unix_common.h
│   ├── platform_macos.h        # macOS: includes unix_common.h
│   ├── platform_freebsd.h      # FreeBSD: includes unix_common.h
│   ├── platform_openbsd.h      # OpenBSD: includes unix_common.h
│   ├── platform_netbsd.h       # NetBSD: includes unix_common.h
│   └── platform_win.h          # Windows: standalone (489 lines)
│
└── startup/                # Platform/architecture startup CRT
    ├── common/
    │   ├── crt_common.c        # Shared CRT initialization
    │   └── crt_common.h        # CRT interface
    │
    ├── linux/
    │   ├── crt_linux.c         # Linux-specific CRT
    │   ├── x86/start.S         # 32-bit x86 entry point
    │   ├── x86_64/start.S      # 64-bit x86_64 entry point
    │   ├── aarch64/start.S     # ARM64 entry point (Linux naming)
    │   └── riscv64/start.S     # RISC-V 64-bit entry point
    │
    ├── macos/
    │   ├── crt_macos.c         # macOS-specific CRT
    │   ├── x86_64/start.S      # Intel Mac entry point
    │   └── arm64/start.S       # Apple Silicon entry point (Apple naming)
    │
    ├── windows/
    │   ├── crt_windows.c       # Windows-specific CRT
    │   ├── x86/start.S         # 32-bit Windows entry point
    │   ├── x86_64/start.S      # 64-bit Windows entry point
    │   └── arm64/start.S       # ARM64 Windows entry point
    │
    ├── freebsd/
    │   ├── crt_freebsd.c       # FreeBSD-specific CRT
    │   ├── x86/start.S         # 32-bit FreeBSD entry point
    │   └── x86_64/start.S      # 64-bit FreeBSD entry point
    │
    │   # OpenBSD/NetBSD currently reuse FreeBSD startup CRT path (Tier 2)
    │
    └── baremetal/
        ├── crt_baremetal.c     # Baremetal CRT
        ├── x86/start.S
        ├── x86_64/start.S
        ├── armv7/start.S       # ARM 32-bit (standard naming)
        ├── aarch64/start.S     # ARM 64-bit (standard naming)
        ├── riscv32/start.S
        └── riscv64/start.S
```

## Platform Abstraction Strategy

### Compile-Time Platform Selection

The `src/compiler_seed/platform/platform.h` header uses preprocessor macros to select the correct platform:

```c
#if defined(_WIN32)
#  include "platform_win.h"
#elif defined(__APPLE__)
#  include "platform_macos.h"
#elif defined(__FreeBSD__)
#  include "platform_freebsd.h"
#elif defined(__OpenBSD__)
#  include "platform_openbsd.h"
#elif defined(__NetBSD__)
#  include "platform_netbsd.h"
#else
#  include "platform_linux.h"
#endif
```

No runtime detection. Platform is determined at compile time.

### Code Sharing: unix_common.h

Unix platforms (Linux, macOS, FreeBSD, OpenBSD, NetBSD) share the same implementation:

```
platform_linux.h (9 lines)
    ├─→ #include "unix_common.h"  (415 lines of POSIX code)
    └─→ (no additional code)

platform_macos.h (13 lines)
    ├─→ #define _DARWIN_C_SOURCE
    ├─→ #include "unix_common.h"
    └─→ (no additional code)

platform_freebsd.h (13 lines)
    ├─→ #define __BSD_VISIBLE 1
    ├─→ #include "unix_common.h"
    └─→ (no additional code)
```

This ensures:
- Bug fixes apply to all Unix platforms simultaneously
- Consistent behavior across Linux/BSD/macOS
- Minimal maintenance burden (one implementation for all Unix targets)

### Windows: Standalone Implementation

Windows uses a standalone implementation because Win32 API is fundamentally different from POSIX:

```
platform_win.h (489 lines)
    ├─→ Directory ops: FindFirstFileA, CreateDirectoryA
    ├─→ File ops: CreateFileA, LockFileEx
    ├─→ Process ops: CreateProcessA, WaitForSingleObject
    └─→ Memory-mapped I/O: CreateFileMappingA, MapViewOfFile
```

Despite different implementation, **the API contract is identical** to Unix (see `PLATFORM_API.md`).

## Architecture Naming Conventions

Different platforms use different architecture naming:

| Architecture | Linux/FreeBSD | macOS | Windows | Baremetal (Standard) |
|--------------|---------------|-------|---------|---------------------|
| **32-bit x86** | `x86` | `x86` | `x86` | `x86` |
| **64-bit x86** | `x86_64` | `x86_64` | `x86_64` | `x86_64` |
| **64-bit ARM** | `aarch64` | `arm64` | `arm64` | `aarch64` |
| **32-bit ARM** | `armv7` | — | — | `armv7` |
| **RISC-V 32** | — | — | — | `riscv32` |
| **RISC-V 64** | `riscv64` | — | — | `riscv64` |

**Naming philosophy**:
- **Follow platform conventions** (Linux uses `aarch64`, Apple uses `arm64`)
- **Use LLVM triple names** for baremetal targets
- **Consistency within platform** (all Linux uses same naming scheme)

## Seed Compiler Variants

### seed.c - Simple → C Transpiler

**Purpose**: Legacy bootstrap path (deprecated)
**Input**: Subset of Simple (no structs, no enums, basic features)
**Output**: Portable C code
**Size**: 2,067 lines
**Status**: Maintained for compatibility, but `seed.cpp` is preferred

### seed.cpp - Core Simple → C++ Transpiler

**Purpose**: Primary bootstrap path
**Input**: Core Simple (structs, enums, impl blocks, methods)
**Output**: C++17 code
**Size**: 4,296 lines
**Status**: **Actively used** for all modern bootstraps

**Supported Core Simple features**:
- Typed structs with fields
- Enum variants (simple, no data)
- `impl` blocks with methods
- Struct constructors
- Module system (`use`/`export`)
- Multi-file compilation

**Why C++ instead of C**?
- Structs with methods map naturally to C++ classes
- Better type safety for Core Simple's type system
- Easier to maintain (less manual memory management)

## Build System

### CMake Configuration

Single `seed/CMakeLists.txt` builds on all platforms:

```cmake
# Detects platform automatically
project(simple-seed C CXX)

# Platform-independent targets
add_executable(seed seed.c)              # C transpiler
add_executable(seed_cpp seed.cpp)        # C++ transpiler (preferred)
add_library(spl_runtime STATIC runtime.c)

# Platform/architecture CRT libraries
add_subdirectory(startup)
```

### Build Commands

```bash
# Standard CMake build (any platform)
cmake -S seed -B build/seed
cmake --build build/seed

# Produces:
# - build/seed/seed          (Simple → C transpiler)
# - build/seed/seed_cpp      (Core Simple → C++ transpiler)
# - build/seed/libspl_runtime.a
# - build/seed/startup/libspl_crt_{platform}_{arch}.a
```

### Platform-Specific Flags

CMake automatically detects platform and sets appropriate flags:

- **Windows (MSVC)**: `/W3` warnings
- **Unix (clang/gcc)**: `-Wall -Wextra`
- **Coverage build**: `-fprofile-instr-generate -fcoverage-mapping` (Clang only)

No manual configuration needed.

## Runtime Library

### runtime.c - Core Runtime Functions

**Purpose**: Minimal runtime library for transpiled Simple code
**Size**: 1,003 lines
**Features**:
- String manipulation (concat, slice, interpolation)
- Array operations (allocate, push, pop, slice)
- Memory management (arena allocator)
- Panic/error handling
- Basic I/O wrappers

**Platform-independent**: All platform-specific code is in `platform/*.h`

### Platform Functions (rt_*)

All platform-specific functions start with `rt_` prefix:
- `rt_dir_*` - Directory operations
- `rt_file_*` - File operations
- `rt_mmap_*`, `rt_munmap`, `rt_msync` - Memory-mapped I/O
- `rt_process_*` - Process management

See `platform/PLATFORM_API.md` for complete function list.

## Platform Support Tiers

| Tier | Definition | Platforms | CI/CD |
|------|-----------|-----------|-------|
| **Tier 1** | Primary development, tested on every commit | Linux x86_64, macOS arm64 | ✅ Yes |
| **Tier 2** | Community supported, tested before releases | Windows x86_64, FreeBSD x86_64 | ⚠️ Manual |
| **Tier 3** | Experimental, best-effort support | Baremetal, ARM32, RISC-V | ❌ No |

### Tier 1 Platforms (Primary)

**Linux x86_64**
- Main development platform
- Full test coverage (3,891 tests)
- CI/CD: GitHub Actions

**macOS arm64 (Apple Silicon)**
- Primary macOS platform
- Full test coverage
- CI/CD: GitHub Actions

### Tier 2 Platforms (Supported)

**Windows x86_64**
- Community supported
- Manual testing before releases
- No CI/CD (requires Windows runner)

**FreeBSD x86_64**
- Community supported
- Test script: `scripts/bootstrap/bootstrap-from-scratch.sh --target=freebsd-x86_64`
- No CI/CD

### Tier 3 Platforms (Experimental)

**Baremetal** (all architectures)
- For embedded systems research
- Startup CRT exists, but minimal testing
- No standard library available

**Linux aarch64, riscv64**
- Cross-compilation tested
- Runtime tests passing
- Limited integration testing

## Testing Strategy

### Runtime Tests

```bash
# Build and run runtime tests
cmake --build build/seed --target runtime_test
./build/src/compiler_seed/runtime_test

# Tests: String ops, array ops, memory management
```

### Seed Compiler Tests

```bash
# Build and run seed compiler tests
cmake --build build/seed --target seed_test
./build/seed/seed_test

# Tests: Parsing, transpilation, code generation
```

### Platform Contract Tests

Each platform must pass identical contract tests to ensure API parity:

```bash
# Verify function signatures match across platforms
grep "^[a-z_]*\s*rt_" src/compiler_seed/platform/unix_common.h | sed 's/ {$/;/' > /tmp/unix_api.txt
grep "^[a-z_]*\s*rt_" src/compiler_seed/platform/platform_win.h | sed 's/ {$/;/' > /tmp/win_api.txt
diff /tmp/unix_api.txt /tmp/win_api.txt  # Should be empty
```

### Full Bootstrap Test

The ultimate test is self-compilation:

```bash
# Linux/macOS/FreeBSD
scripts/bootstrap/bootstrap-from-scratch.sh

# Windows
script\bootstrap-from-scratch.bat

# Verifies:
# 1. seed_cpp builds from C++
# 2. seed_cpp can transpile Core Simple
# 3. Core compiler builds from transpiled C++
# 4. Core compiler can compile Full Simple
# 5. Full compiler can compile itself (fixed point)
```

## Adding New Platform Support

### Step 1: Create Platform Header

Create `src/compiler_seed/platform/platform_newos.h`:

```c
/*
 * NewOS platform header
 */
#ifndef SPL_PLATFORM_NEWOS_H
#define SPL_PLATFORM_NEWOS_H

// Include system headers
#include <newos/syscalls.h>

// Implement all rt_* functions
// (see PLATFORM_API.md for full list)
bool rt_dir_create(const char* path, bool recursive) {
    // Implementation using NewOS syscalls
}

// ... implement all 21 functions ...

#endif
```

### Step 2: Add Platform Detection

Edit `src/compiler_seed/platform/platform.h`:

```c
#elif defined(__NEWOS__)
#  include "platform_newos.h"
```

### Step 3: Create Startup CRT

Create `seed/startup/newos/crt_newos.c`:

```c
#include "../common/crt_common.h"

void _start() {
    crt_common_init();
    extern int main(int argc, char** argv);
    int ret = main(__argc, __argv);
    crt_common_exit(ret);
}
```

### Step 4: Add Architecture Entry Points

For each supported architecture, create `seed/startup/newos/{arch}/start.S`:

```asm
.global _start
_start:
    # Set up stack
    # Jump to C entry point
    call _start
```

### Step 5: Update CMakeLists.txt

Add NewOS-specific configurations if needed.

### Step 6: Test Bootstrap

```bash
cmake -S seed -B build/seed-newos
cmake --build build/seed-newos
./build/seed-newos/seed_cpp --help
```

## Key Design Decisions

### Why Header-Only Platform Abstraction?

**Rationale**: Minimal runtime overhead, compile-time optimization
- No runtime dispatch (all platform selection at compile time)
- Compiler can inline and optimize platform-specific code
- Single binary per platform (no dynamic loading)

### Why Not #ifdef in Main Code?

**Rationale**: Separation of concerns, maintainability
- Seed compiler source remains platform-independent
- Platform differences isolated to single directory
- Easy to add new platforms without touching main code
- Reduces merge conflicts in main codebase

### Why Unix Code Sharing?

**Rationale**: DRY principle, consistent behavior
- Linux, macOS, FreeBSD are all POSIX-compliant
- 95% of implementation is identical
- Bug fixes automatically apply to all Unix platforms
- Only feature macros differ (for BSD extensions, Darwin APIs)

### Why Separate Windows Implementation?

**Rationale**: Fundamentally different API
- Win32 API is not POSIX-compatible
- Different paradigms (handles vs file descriptors)
- Attempting to unify would create abstraction overhead
- Better to have clean, native Windows implementation

## Future Improvements

### Potential Enhancements

1. **Extract windows_common.h** (Low priority)
   - Split platform_win.h into common utilities + rt_* implementations
   - Estimated effort: 2 hours
   - Benefit: Cleaner Windows code organization

2. **Add Windows CI/CD** (Medium priority)
   - Set up GitHub Actions Windows runner
   - Estimated effort: 1 day
   - Benefit: Automated Windows testing

3. **Standardize architecture naming** (Low priority)
   - Decide: Use platform conventions or standardize on LLVM triples?
   - Estimated effort: 4 hours (renaming + documentation)
   - Benefit: Reduced confusion

4. **Contract verification tests** (High priority)
   - Automated tests that verify all platforms implement identical API
   - Estimated effort: 1 day
   - Benefit: Catch API drift early

5. **Baremetal platform completion** (Low priority)
   - Complete baremetal implementation for embedded targets
   - Estimated effort: 2 weeks
   - Benefit: Enable embedded Simple development

## Version History

- **2026-02-13**: Initial architecture documentation
- **2026-02-13**: Windows platform critical functions implemented
- Platforms: Linux (Tier 1), macOS (Tier 1), Windows (Tier 2), FreeBSD (Tier 2)
- Total platform code: ~900 lines (415 Unix + 489 Windows)
