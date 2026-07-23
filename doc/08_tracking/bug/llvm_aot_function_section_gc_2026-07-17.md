# LLVM AOT module-wide `.text` defeats strict dead-code linking

Date: 2026-07-17
Status: SOURCE-FIXED — Rust-seed regression passes; fresh bounded Stage 2 pending
Priority: P0 bootstrap blocker

## Symptom

A fresh Rust-hosted Stage 2 build compiles every Simple module but fails at the
final strict link with references from functions that are not in the bootstrap
entry closure. The linker already receives `--gc-sections`.

## Reproduction evidence

The retained Stage 2 object `mod_679.o` contains many defined functions and one
shared `.text` section. That section also contains undefined references such as
`rt_file_modified`, `rt_list_dir_recursive`, and legacy path helpers. Because a
reachable function retains the shared section, the linker cannot discard the
unreachable functions and their relocations individually.

The selected Rust-hosted native archive is present. It defines canonical
providers including `rt_file_stat`, `rt_dir_walk`, `rt_path_basename`, and
`rt_path_ext`; adding another runtime archive would mask naming drift and risk
duplicate ownership without fixing section liveness.

## Historical root cause

LLVM AOT object emission did not assign a distinct discardable section to each
defined function. Module-level section granularity made the entry-closure and
linker garbage collection weaker than the function-level liveness contract.

## Resolution

Commit `940d2396e276` (`fix(llvm): emit discardable function sections`) fixes
the Rust seed backend used by the Rust-hosted Stage 2. After function bodies are
compiled, it walks the LLVM module and assigns `.text.simple.<index>` only to
functions with basic blocks. Declarations retain external linkage and receive
no section. The explicit spelling is restricted to ELF targets: Linux,
FreeBSD, SimpleOS, and bare metal.

The regression
`llvm_aot_function_sections_allow_strict_dead_reference_gc` in
`src/compiler_rust/compiler/src/codegen/llvm/backend_core.rs` parses the emitted
object and requires at least two `.text.simple.*` sections. It then proves that
`--gc-sections` links when the missing external is referenced only by an
unreachable function and fails when that function is the entry.

## Smallest solution

Implemented in the Rust seed's shared LLVM module finalization pass. Do not
project the ELF section spelling onto Mach-O or COFF; those formats need their
native atom/COMDAT mechanisms and target-native evidence.

## Required prevention tests

1. DONE (Linux Rust seed): prove at least two distinct function text sections.
2. DONE (Linux Rust seed): strict-link an unreachable missing external with GC.
3. DONE (Linux Rust seed): make that function reachable and prove link failure.
4. PENDING: run one fresh bounded Stage 2 and classify only unresolved symbols
   that survive function-level GC.

Do not add speculative runtime aliases or permissive zero-return stubs.
