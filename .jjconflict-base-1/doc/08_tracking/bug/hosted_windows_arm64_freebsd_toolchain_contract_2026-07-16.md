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
The shared admission rule still accepted Windows 32-bit x86 and FreeBSD ARM32 even
though their linker/CRT owners are not implemented. FreeBSD AArch64 was admitted
but its toolchain descriptor still reported the Linux triple, CRT directory,
and package guidance. RV64 descriptors similarly reported Linux toolchains on
non-Linux hosts instead of failing closed.

## Resolution

Hosted Windows ARM64 now fails in the shared native linker before SMF/platform
dispatch until the MSVC machine and CRT owners become architecture-aware. The
LLVM path reuses the same admission rule before compiling runtime or entry
objects. FreeBSD x86_64 now selects its native triple, `/usr/lib` CRT directory,
and base-system toolchain guidance. Cross C compiler selection is limited to an
actual Linux architecture mismatch, and the shared linker uses the canonical
platform host detector.

The shared admission rule now allows Windows x86_64 only, macOS and FreeBSD
x86_64/AArch64 only, and Linux x86_64/AArch64/RV64. Toolchain descriptors use
the canonical platform host architecture, provide native FreeBSD AArch64
metadata, fail every hosted ARMv7 route closed, and fail RV64 closed outside
Linux with OS-correct diagnostic triples. The pure regression matrix covers
these contracts. Executable proof remains pending repair of the pure-Simple
runner.
