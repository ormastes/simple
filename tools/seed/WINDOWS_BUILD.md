# Windows Build Guide — ClangCL and MinGW Clang

This guide covers building the Simple seed compiler on Windows using two different toolchains:

1. **ClangCL** (MSVC ABI, recommended for Windows developers)
2. **MinGW Clang** (GCC ABI, cross-platform consistency)

## Table of Contents

- [Toolchain Comparison](#toolchain-comparison)
- [ClangCL Build (MSVC ABI)](#clangcl-build-msvc-abi)
- [MinGW Clang Build (GCC ABI)](#mingw-clang-build-gcc-abi)
- [Cross-Compilation from Linux](#cross-compilation-from-linux)
- [Troubleshooting](#troubleshooting)

---

## Toolchain Comparison

| Feature | ClangCL (MSVC ABI) | MinGW Clang (GCC ABI) |
|---------|-------------------|---------------------|
| **Target Triple** | `x86_64-pc-windows-msvc` | `x86_64-w64-mingw32` |
| **C++ ABI** | MSVC (incompatible with GCC) | Itanium (GCC-compatible) |
| **Runtime Library** | UCRT (api-ms-win-crt-*.dll) | msvcrt.dll + libstdc++ |
| **Headers** | Windows SDK | mingw-w64 |
| **Compiler Flags** | MSVC-style (`/MD`, `/O2`) | GCC-style (`-O2`, `-static`) |
| **Best For** | Windows-native development | Cross-platform, Linux compatibility |
| **Binary Interop** | ❌ Cannot link with MinGW | ✅ Can link with GCC/Clang |
| **DLL Dependencies** | Smaller (UCRT only) | Larger (libstdc++.dll) |
| **Build Complexity** | Requires Visual Studio Build Tools | Works with standalone LLVM |

**CRITICAL:** Do NOT mix object files or libraries from ClangCL and MinGW. They use incompatible ABIs and symbol mangling.

---

## ClangCL Build (MSVC ABI)

### Prerequisites

1. **Visual Studio Build Tools** (free download)
   - Install from: https://visualstudio.microsoft.com/downloads/
   - Select: "Desktop development with C++"
   - Components needed:
     - MSVC v143 - VS 2022 C++ x64/x86 build tools
     - Windows 11 SDK (or Windows 10 SDK)
     - CMake tools for Windows

2. **LLVM/Clang** (includes clang-cl)
   - Download from: https://github.com/llvm/llvm-project/releases
   - Install version 15.0.0 or newer
   - Add LLVM bin directory to PATH: `C:\Program Files\LLVM\bin`

3. **CMake** (if not installed with VS Build Tools)
   - Download from: https://cmake.org/download/
   - Add to PATH during installation

4. **Ninja** (recommended build tool)
   - Download from: https://github.com/ninja-build/ninja/releases
   - Extract `ninja.exe` to a directory in PATH (e.g., `C:\Program Files\LLVM\bin`)

### Build Steps (ClangCL)

#### Option 1: Visual Studio Developer Command Prompt

```cmd
# Open "x64 Native Tools Command Prompt for VS 2022"
# This automatically sets up MSVC environment

cd C:\path\to\simple\seed

# Create build directory
mkdir build-clangcl
cd build-clangcl

# Configure with ClangCL toolchain
cmake -G Ninja ^
  -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-clangcl.cmake ^
  -DCMAKE_BUILD_TYPE=Release ^
  ..

# Build
ninja

# Test
runtime_test.exe
seed_cpp.exe --help
```

#### Option 2: Standalone Build (PowerShell)

```powershell
# Set up environment (if not using Developer Command Prompt)
$env:PATH = "C:\Program Files\LLVM\bin;$env:PATH"
$env:PATH = "C:\Program Files\Microsoft Visual Studio\2022\BuildTools\VC\Tools\MSVC\14.XX.XXXXX\bin\Hostx64\x64;$env:PATH"

cd C:\path\to\simple\seed

# Create build directory
mkdir build-clangcl
cd build-clangcl

# Configure
cmake -G Ninja `
  -DCMAKE_TOOLCHAIN_FILE=..\cmake\toolchains\windows-x86_64-clangcl.cmake `
  -DCMAKE_BUILD_TYPE=Release `
  ..

# Build
ninja

# Test
.\runtime_test.exe
.\seed_cpp.exe --help
```

### Verify ClangCL Build

```cmd
# Check compiler version
clang-cl --version
# Output: clang version 15.0.0 (or newer)
# Target: x86_64-pc-windows-msvc

# Check build output
.\seed_cpp.exe --version
# Output: Simple Seed Compiler (C++ version)

# Run runtime tests
.\runtime_test.exe
# Output: === All 202 tests passed ===

# Check dependencies (should only show UCRT)
dumpbin /DEPENDENTS seed_cpp.exe
# Expected DLLs:
#   KERNEL32.dll
#   api-ms-win-crt-runtime-l1-1-0.dll
#   api-ms-win-crt-stdio-l1-1-0.dll
```

---

## MinGW Clang Build (GCC ABI)

### Prerequisites

1. **LLVM/Clang with MinGW support**

   **Option A: LLVM-MinGW (Standalone toolchain)**
   - Download from: https://github.com/mstorsjo/llvm-mingw/releases
   - Extract to `C:\llvm-mingw`
   - Add to PATH: `C:\llvm-mingw\bin`

   **Option B: MSYS2 (Package manager)**
   - Install MSYS2: https://www.msys2.org/
   - Open MSYS2 MinGW 64-bit shell
   - Install packages:
     ```bash
     pacman -S mingw-w64-x86_64-clang mingw-w64-x86_64-cmake mingw-w64-x86_64-ninja
     ```

2. **CMake and Ninja** (if using standalone LLVM-MinGW)
   - Download CMake: https://cmake.org/download/
   - Download Ninja: https://github.com/ninja-build/ninja/releases

### Build Steps (MinGW Clang)

#### Option 1: MSYS2 Environment

```bash
# Open MSYS2 MinGW 64-bit shell
cd /c/path/to/simple/seed

# Create build directory
mkdir build-mingw
cd build-mingw

# Configure with MinGW toolchain
cmake -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-mingw.cmake \
  -DCMAKE_BUILD_TYPE=Release \
  ..

# Build
ninja

# Test
./runtime_test.exe
./seed_cpp.exe --help
```

#### Option 2: Standalone LLVM-MinGW (PowerShell)

```powershell
# Set up environment
$env:PATH = "C:\llvm-mingw\bin;$env:PATH"

cd C:\path\to\simple\seed

# Create build directory
mkdir build-mingw
cd build-mingw

# Configure
cmake -G Ninja `
  -DCMAKE_TOOLCHAIN_FILE=..\cmake\toolchains\windows-x86_64-mingw.cmake `
  -DCMAKE_BUILD_TYPE=Release `
  ..

# Build
ninja

# Test
.\runtime_test.exe
.\seed_cpp.exe --help
```

### Verify MinGW Build

```bash
# Check compiler target
clang --version --target=x86_64-w64-mingw32
# Target: x86_64-w64-mingw32

# Check build output
./seed_cpp.exe --version

# Run runtime tests
./runtime_test.exe
# Output: === All 202 tests passed ===

# Check dependencies (static linking - minimal DLLs)
objdump -p seed_cpp.exe | grep "DLL Name"
# Expected DLLs:
#   KERNEL32.dll
#   msvcrt.dll
#   (possibly libwinpthread-1.dll if not statically linked)
```

---

## Cross-Compilation from Linux

You can build Windows binaries from Linux using the MinGW cross-compiler.

### Prerequisites (Ubuntu/Debian)

```bash
sudo apt update
sudo apt install \
  mingw-w64 \
  gcc-mingw-w64-x86-64 \
  g++-mingw-w64-x86-64 \
  cmake \
  ninja-build
```

### Build Steps

```bash
cd seed

# Create cross-build directory
mkdir build-windows-cross
cd build-windows-cross

# Configure for Windows cross-compilation
cmake -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-mingw.cmake \
  -DCMAKE_BUILD_TYPE=Release \
  ..

# Build Windows executables
ninja

# Output: seed.exe, seed_cpp.exe (Windows PE binaries)
file seed_cpp.exe
# Output: PE32+ executable (console) x86-64, for MS Windows

# Test on Windows or Wine
wine ./runtime_test.exe
```

---

## Troubleshooting

### ClangCL Issues

#### "clang-cl: command not found"

**Cause:** LLVM not in PATH or not installed.

**Fix:**
```cmd
# Verify LLVM installation
dir "C:\Program Files\LLVM\bin\clang-cl.exe"

# Add to PATH (PowerShell)
$env:PATH = "C:\Program Files\LLVM\bin;$env:PATH"

# Or add permanently via System Environment Variables
```

#### "Cannot find Windows SDK"

**Cause:** Visual Studio Build Tools not installed or SDK path not set.

**Fix:**
1. Install Visual Studio Build Tools
2. Use Developer Command Prompt which sets up SDK paths automatically
3. Or manually set `WindowsSdkDir` environment variable

#### Error: "LNK1104: cannot open file 'ucrt.lib'"

**Cause:** UCRT library not found (part of Windows SDK).

**Fix:**
```cmd
# Verify Windows SDK installation
dir "C:\Program Files (x86)\Windows Kits\10\Lib\*\ucrt"

# Use Developer Command Prompt which sets LIB paths automatically
```

#### Error: "undefined reference to `__declspec(dllimport)` functions"

**Cause:** Mixing ClangCL and MinGW object files.

**Fix:** Clean rebuild using single toolchain only:
```cmd
cd build-clangcl
ninja clean
ninja
```

### MinGW Issues

#### "x86_64-w64-mingw32-gcc: command not found" (Linux cross-compile)

**Cause:** MinGW cross-compiler not installed.

**Fix:**
```bash
sudo apt install gcc-mingw-w64-x86-64 g++-mingw-w64-x86-64
```

#### "undefined reference to `std::__cxx11::basic_string`"

**Cause:** ABI mismatch or missing `-static-libstdc++`.

**Fix:** Rebuild with static linking:
```bash
cmake -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-mingw.cmake \
  -DCMAKE_CXX_FLAGS="-static-libgcc -static-libstdc++" \
  ..
ninja
```

#### MinGW binary fails to run on Windows: "missing DLL"

**Cause:** libstdc++.dll or libwinpthread.dll not statically linked.

**Fix:** Verify static flags in toolchain file or rebuild:
```bash
clang++ -static-libgcc -static-libstdc++ -static ...
```

#### Error: "long double mismatch" when linking

**Cause:** MinGW uses 80-bit long double, incompatible with MSVC's 64-bit.

**Fix:** Do NOT mix ClangCL and MinGW code. Rebuild all sources with same toolchain.

### General Issues

#### CMake Error: "No CMAKE_C_COMPILER found"

**Fix:**
```bash
# Specify compiler explicitly
cmake -DCMAKE_C_COMPILER=clang -DCMAKE_CXX_COMPILER=clang++ ...
```

#### Build succeeds but runtime_test.exe crashes

**Possible causes:**
1. DLL version mismatch (ClangCL UCRT vs MinGW msvcrt)
2. Mixed toolchain object files
3. Missing runtime libraries

**Fix:**
```cmd
# Clean rebuild
ninja clean
ninja

# Check dependencies
dumpbin /DEPENDENTS runtime_test.exe  # ClangCL
objdump -p runtime_test.exe | grep DLL # MinGW

# Verify no mixing
# ClangCL should only link UCRT DLLs
# MinGW should only link msvcrt.dll
```

---

## Best Practices

1. **Choose ONE toolchain per project** - never mix ClangCL and MinGW
2. **Use ClangCL for Windows-native apps** - better integration with Visual Studio
3. **Use MinGW for cross-platform projects** - consistent ABI across Linux/Windows
4. **Static link MinGW binaries** - avoids DLL deployment issues
5. **Test on target platform** - Wine testing is not always accurate
6. **Use separate build directories** - `build-clangcl/` vs `build-mingw/`

---

## Platform Status

| Build Configuration | Status | Tested |
|---------------------|--------|--------|
| ClangCL (Windows native) | ✅ Supported | Verified on Win 11 |
| MinGW Clang (Windows native) | ✅ Supported | Verified on Win 11 |
| MinGW Cross (Linux → Windows) | ✅ Supported | Verified on Ubuntu 22.04 |

---

## References

- **ClangCL Documentation:** https://clang.llvm.org/docs/UsersManual.html#clang-cl
- **LLVM-MinGW Project:** https://github.com/mstorsjo/llvm-mingw
- **MinGW-w64 Official Site:** https://www.mingw-w64.org/
- **MSVC Runtime Library Docs:** https://learn.microsoft.com/en-us/cpp/build/reference/md-mt-ld-use-run-time-library
- **CMake Toolchains:** https://cmake.org/cmake/help/latest/manual/cmake-toolchains.7.html
- **Clang vs ClangCL:** https://blog.conan.io/2022/10/13/Different-flavors-Clang-compiler-Windows.html

---

## Next Steps

After successfully building:

1. **Run tests:** `runtime_test.exe` (should pass all 202 tests)
2. **Test transpilation:** `seed_cpp.exe example.spl > example.cpp`
3. **Bootstrap compiler:** See `../scripts/bootstrap-from-scratch.sh`
4. **Read main docs:** `../README.md` and `../doc/guide/bootstrap.md`

For issues, see [Troubleshooting](#troubleshooting) or file a bug report.
