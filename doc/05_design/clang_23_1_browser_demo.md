<!-- codex-design -->
# Clang 23.1 Browser Demo Detail Design

## Interfaces

- `resolve_clang_23_1_toolchain`: resolve explicit paths/prefix, otherwise a
  bounded list of 23.1 names and prefixes.
- `validate_clang_23_1_toolchain`: parse tool output, require 23.1, require a
  coherent prefix/family, and print actionable diagnostics.
- Browser builder inputs: `LLVM_23_1_PREFIX`, `CLANG`, `LINKER`,
  `SIMPLEOS_SYSROOT`; outputs: ELF plus a line-oriented evidence manifest.
- Guest commands: `clang`, `clang-23.1`, `lld`, and LLVM utilities resolve to
  versioned manifest entries whose version file declares 23.1.

## Resolution algorithm

1. If an explicit executable is supplied, require it to exist and validate it.
2. Else if `LLVM_23_1_PREFIX` is supplied, use unversioned tools below `bin/`.
3. Else try only bounded 23.1-specific names/prefixes; unversioned host tools are
   admitted only after their reported version parses as 23.1.
4. Resolve LLD and utilities from the same prefix where possible and validate
   every tool used.  Never select an older linker merely because it is present.
5. Cache the resolved structure for the operation.

## Browser build

Provision the sysroot, rebuild the copied libc with the exact admitted compiler,
compile `browser_demo.c` for `x86_64-unknown-simpleos`, link with admitted LLD,
then require x86-64 ELF and a resolved `getpid`.  Write compiler/linker versions,
paths, hashes, command target and output hash beside the ELF.  The disk builder
must stage those exact bytes as `BROWSMF.SMF`.

## Simple compiler and bootstrap

Pure-Simple discovery candidates begin with 23.1 and reject an explicit
incompatible provider.  Capability diagnostics name the new prefix contract.
Rust bootstrap changes the binding feature only when upstream supports LLVM 23;
otherwise the LLVM-backed Rust bootstrap remains a concrete blocker and must
not claim migration based on renamed variables.

## SimpleOS filesystem

Package metadata, shell manifest lookup, VFS launch mapping, image builders and
ported LLVM scripts use the versioned canonical path.  `clang` remains an alias
for operator compatibility.  Tests prove both names resolve to the same
manifest identity and that the launchable payload exists in the image catalog.

## Error and evidence contract

Every rejection includes the observed path/version and expected `23.1.x`.
Provider/bootstrap/browser/QEMU logs are retained under the isolated build tree.
The QEMU report must prove font, baseline, fullscreen, restored and browser
frames plus correlated keyboard, pointer/click and browser provenance events.
