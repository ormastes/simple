# Mach-O dynamic provider metadata

Authority: `test/03_system/app/compiler/feature/item4_linker_macho_dylib_spec.spl`.
Requirements: ITEM4-REQ-004, 006. Status: authored manual; Simple execution and canonical
SPipe regeneration are **UNRUN**. This is not generated PASS evidence.

1. Read actual x86-64 and ARM64 dylibs produced by LLVM's Mach-O linker.
2. Preserve install name, versions, ordered dependency ordinals, exported
   symbols and actual reexport relationships.
3. Validate trie offsets, termination, cycles, symbol strings and load-command
   extents before exposing provider metadata.
4. Reject wrong CPU/file type, malformed records and unsupported contracts.

Reading a provider is not a hosted executable linker. Stub/GOT allocation,
rebasing/binding, TLS/unwind, code signing and native execution remain open.
