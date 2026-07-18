# Stage4 runtime-native legacy compatibility owner gap

## Status

Source-fixed; execution pending.

Strict Stage4 selected `runtime_native.o`, whose complete member dependency
closure still needs 18 small legacy string, console, environment, file, sleep,
directory, and async-process helpers. Raw `runtime_legacy_core.o` was not an
admissible owner because it also exported legacy array/split layouts, no-op
dictionary functions, thread/platform overlaps, and other broad helpers.

## Root Cause

The provider inventory had no exact owner for the 18 transitive dependencies.
Owner resolution therefore stopped before the already intentional archive
projection barrier. Adding the raw legacy object would have hidden the missing
owner while reopening duplicate and invalid ABI definitions.

## Fix

The hosted pure-Simple runtime-object path now adds `runtime_legacy_core.o`
only for strict Stage4. A dedicated builder copies that fresh object, requires
each audited export exactly once, localizes every other definition, verifies the
localized symbol table and sole `rt_value_bool` runtime dependency, and creates
a deterministic one-member `runtime_legacy_compat` archive.

The exact archive owns both direct compiler-emitted calls such as
`spl_str_len`/`spl_str_slice` and transitive dependencies from `runtime_native`.
Array, dictionary, split, and thread helpers remain non-exported.

The admitted `rt_dir_remove_all` helper now recursively removes directory
trees without following POSIX symlinks or Windows reparse points; the prior
single `remove()` call could not clean non-empty Stage4 transaction trees.
The existing core-C focus probe now preserves a nested/symlink fixture until
this helper removes the full tree.

## Verification

`test/01_unit/compiler/backend/stage4_runtime_legacy_compat_provider_spec.spl`
covers the exact raw/localized contracts for ELF, Mach-O, COFF-MSVC, and
COFF-MinGW; missing, duplicate, extra, and forbidden symbols; direct and
transitive cyclic ownership; and production wiring/cleanup.

Static review and repository audits may run in this session. Native compiler,
C, and bootstrap execution remain pending under the active execution
restriction. Exact selected-archive projection and strict final-link routing
are now source-implemented; complete requested-owner and executable evidence
remain pending.

Full strict Stage4 production is currently Linux/macOS native-host only because
the compiler-backfill producer still rejects FreeBSD and Windows. FreeBSD ELF,
COFF-MSVC, and COFF-MinGW coverage here is source-level symbol-contract
coverage, not an execution claim; MSVC-form objects require LLVM/GNU companion
archive and object tools rather than `lib.exe`. The broader hosted architecture
surface is Linux x86_64/AArch64/RISC-V64, macOS x86_64/AArch64, FreeBSD
x86_64/AArch64, and Windows x86_64; x86, ARM32, and RISC-V32 are not claimed
for Stage4.
