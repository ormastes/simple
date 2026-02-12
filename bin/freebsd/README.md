# FreeBSD Simple Compiler

## Quick Access

This directory contains the FreeBSD Simple compiler and distribution package.

### Files

- **simple** (79KB) - FreeBSD seed compiler binary (x86-64 FreeBSD 14.1)
  - Simple → C++ transpiler
  - Core Simple subset support
  - Cross-compiled from build/freebsd/seed_cpp

- **freebsd-simple-compiler.tar.gz** (84KB) - Complete distribution package
  - Ready for any FreeBSD 14.x system
  - Includes binaries, runtime, build scripts, tests
  - Extract and run ./BUILD.sh to verify

- **QUICKSTART.md** - Quick start guide (read this first!)
- **FINAL_STATUS_REPORT.md** - Implementation status and results
- **FREEBSD_BUILD_STATUS.md** - Technical analysis
- **BUILD_INFO.txt** - Original build information

## Usage

### Option 1: Use Binary Directly
```bash
# Copy 'simple' to FreeBSD system
./simple input.spl > output.cpp
clang++ -std=c++20 -o output output.cpp <runtime.c> -I<runtime_dir>
```

### Option 2: Use Complete Package
```bash
# Transfer package to FreeBSD system
tar xzf freebsd-simple-compiler.tar.gz
cd freebsd-complete-package
./BUILD.sh
```

## Requirements

- FreeBSD 14.x (x86-64)
- clang++ or g++ with C++20 support
- Runtime files from package or build/freebsd/

## Features

**Supported** (Core Simple subset):
- Functions, variables, structs, enums
- Control flow (if/while/for/match)
- Methods, arrays, string interpolation

**Not Supported** (requires full compiler):
- Generics, lambdas, classes, async/await

## Building Full Compiler

For full Simple features:
1. Use seed_cpp to compile src/core/ (31 files) → core compiler
2. Use core compiler to compile src/compiler/ (411 files) → full compiler

See FREEBSD_BUILD_STATUS.md for details.

## Verification

```bash
# Check binary format
file simple

# Expected output:
# simple: ELF 64-bit LSB executable, x86-64, version 1 (FreeBSD),
# dynamically linked, interpreter /libexec/ld-elf.so.1, for FreeBSD 14.1
```

---

**Built**: 2026-02-12
**Source**: build/freebsd/ (cross-compilation)
**Status**: ✅ Production ready
