# Quick Windows Build Reference

**One-page reference for building the Simple seed compiler on Windows.**

See [WINDOWS_BUILD.md](WINDOWS_BUILD.md) for full documentation.

---

## ClangCL (MSVC ABI) — Windows Native

```cmd
# Prerequisites: Visual Studio Build Tools + LLVM

# Open "x64 Native Tools Command Prompt for VS 2022"
cd C:\path\to\simple\seed
mkdir build-clangcl && cd build-clangcl

cmake -G Ninja ^
  -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-clangcl.cmake ^
  -DCMAKE_BUILD_TYPE=Release ..

ninja
runtime_test.exe
```

**Output:** `seed_cpp.exe` (MSVC ABI, links UCRT)

---

## MinGW Clang (GCC ABI) — Windows Native

```bash
# Prerequisites: LLVM-MinGW or MSYS2

# MSYS2 MinGW 64-bit shell
cd /c/path/to/simple/seed
mkdir build-mingw && cd build-mingw

cmake -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-mingw.cmake \
  -DCMAKE_BUILD_TYPE=Release \
  ..

ninja
./runtime_test.exe
```

**Output:** `seed_cpp.exe` (GCC ABI, static libstdc++)

---

## MinGW Cross-Compile — Linux → Windows

```bash
# Prerequisites: mingw-w64 (sudo apt install mingw-w64)

cd seed
mkdir build-windows-cross && cd build-windows-cross

cmake -G Ninja \
  -DCMAKE_TOOLCHAIN_FILE=../cmake/toolchains/windows-x86_64-mingw.cmake \
  -DCMAKE_BUILD_TYPE=Release \
  ..

ninja
wine ./runtime_test.exe  # Test with Wine
```

**Output:** `seed_cpp.exe` (Windows PE binary, runs on Windows)

---

## Quick Test

```bash
# Automated test (both toolchains)
cd seed
./test-windows-builds.sh all
```

---

## Toolchain Comparison

| | ClangCL | MinGW |
|---|---|---|
| **ABI** | MSVC | GCC |
| **Runtime** | UCRT | msvcrt.dll |
| **DLLs** | 3-5 | 1-2 |
| **Best for** | Windows-native | Cross-platform |

**NEVER mix ClangCL and MinGW object files!**

---

## Troubleshooting

| Issue | Fix |
|-------|-----|
| `clang-cl: command not found` | Install LLVM, add to PATH |
| `Cannot find Windows SDK` | Install VS Build Tools or use Developer Command Prompt |
| `x86_64-w64-mingw32-gcc: not found` | `sudo apt install mingw-w64` (Linux) |
| Tests crash | Verify single toolchain used (no mixing) |

---

**Full Guide:** [WINDOWS_BUILD.md](WINDOWS_BUILD.md)
