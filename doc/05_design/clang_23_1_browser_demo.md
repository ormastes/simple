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
incompatible provider. Capability diagnostics name the prefix and exact-tool
contract. The admitted capsule contains Clang, LLD, LLC, Opt, ar, nm, objdump,
objcopy, and llvm-config, and every consumer receives canonical absolute paths.
Rust bootstrap remains on Cranelift until upstream supports LLVM 23; its
provenance-verified full Stage 4 output, not Stage 2/3, drives external LLVM.
Renamed Rust LLVM-18 variables or a minimal bootstrap artifact never count as
migration.

## SimpleOS filesystem

Package metadata, shell manifest lookup, VFS launch mapping, image builders and
ported LLVM scripts use the versioned canonical path.  `clang` remains an alias
for operator compatibility.  Tests prove both names resolve to the same
manifest identity and that the launchable payload exists in the image catalog.

## Error and evidence contract

Every rejection includes the observed path/version and expected `23.1.x`.
Provider/bootstrap/browser/QEMU logs are retained under the isolated build tree.
The fullscreen wrapper defaults to LLVM, requires matching provider prefixes,
sets `SIMPLE_BOOTSTRAP=0`, validates full Stage 4 provenance, and scopes its
native cache by backend before compiling the current-source kernel.
The QEMU report must prove font, baseline, fullscreen, restored and browser
frames plus correlated keyboard, pointer/click and browser provenance events.

## Focused pre-QEMU renderer probe

The x86_64 freestanding probe imports only public debug seams around the
production custom-property collector, resolution state, substitution, style
lookup, and backdrop admission. It must prove exact Aetheric values before a
full QEMU cycle: two serialized properties, resolved `rgba(31,31,33,0.80)` and
`blur(30px)`, gradient colors, memo color, and admission `true:4:1700`.
Concatenation intermediates remain statically `text`; exact admission uses
bounded ASCII byte parsing so the probe does not depend on incomplete
freestanding dynamic dispatch or string-to-integer helpers.
