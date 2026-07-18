# LLVM AOT module-wide `.text` defeats strict dead-code linking

Date: 2026-07-17
Status: OPEN — root diagnosed; implementation and focused regression pending
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

## Root cause

LLVM AOT object emission does not assign a distinct discardable section to each
defined function. Module-level section granularity makes the entry-closure and
linker garbage collection weaker than the function-level liveness contract.

## Smallest solution

After LLVM module construction, assign every function with a body a unique
target-appropriate function section. Do not assign sections to declarations.
Keep target spelling isolated; Linux ELF is the immediate bootstrap lane.

## Required prevention tests

1. Emit an LLVM object with two defined functions and prove it contains at
   least two distinct function text sections.
2. Strict-link an object where an unreachable function references a missing
   external symbol: linking with section GC must pass.
3. Make that function reachable: the same strict link must fail.
4. Run one fresh bounded Stage 2 after the implementation and classify only the
   unresolved symbols that survive function-level GC.

Do not add speculative runtime aliases or permissive zero-return stubs.
