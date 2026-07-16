# Hosted Windows ARM64 and FreeBSD toolchain contracts

**Status:** Source fixed fail-closed/corrected; executable proof pending  
**Component:** compiler/backend hosted native linking  
**Found:** 2026-07-16

## Problem

Windows ARM64 passed the hosted target/host match and then entered an MSVC path
hard-coded to `/MACHINE:X64` and x64 CRT/SDK directories. Separately,
`toolchain_x86_64_native("freebsd")` fell through the Linux default and reported
an `x86_64-unknown-linux-gnu` triple plus Linux CRT and package guidance.
Matching explicit AArch64 targets on macOS, FreeBSD, and Linux also selected
`aarch64-linux-gnu-gcc` instead of the host C compiler during fallback linking.

## Resolution

Hosted Windows ARM64 now fails in the shared native linker before SMF/platform
dispatch until the MSVC machine and CRT owners become architecture-aware. The
LLVM path reuses the same admission rule before compiling runtime or entry
objects. Windows x86_64, macOS, and FreeBSD remain enabled. FreeBSD x86_64 now
selects its native triple, `/usr/lib` CRT directory, and base-system toolchain
guidance. Pure platform matrix and source-order tests cover both boundaries;
cross C compiler selection is now limited to an actual Linux architecture
mismatch, and the shared linker uses the canonical platform host detector.
Executable proof remains pending repair of the pure-Simple runner.
