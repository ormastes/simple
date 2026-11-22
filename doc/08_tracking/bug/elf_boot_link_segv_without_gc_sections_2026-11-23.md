# elf_boot_link exits 139 (SIGSEGV) linking the arm64 kernel without --gc-sections

- **Status:** open
- **Found:** 2026-11-23, arm64 elf_boot_link-vs-lld comparison for PR #10912 (merge `fb4d21dd37d`)
- **Component:** `src/compiler/70.backend/linker/elf/elf_boot_link.spl`, Pure Simple boot linker

## Symptom
The arm64 fs-exec kernel objects (572 `.o` files from
`check-simpleos-arm64-user-elf-link.shs --link-only`, linked with
`examples/09_embedded/simple_os/arch/arm64/fs_exec_linker.ld`) link correctly
with `--gc-sections`: same entry address `0x40200000` and identical `.text` as
ld.lld. The same link WITHOUT `--gc-sections` crashes the process with exit 139.
A linker must never segfault: a too-large or unsupported input has to give a
named error.

## Not yet known
Whether the cause is input size (about 10x more retained sections and symbols),
a specific relocation or section kind that gc normally drops, or a runtime/stack
limit in the host process. No repro smaller than the full kernel exists yet.

## Next steps
1. Reproduce under `simple run` with a trace, and bisect the object set to a
   minimal repro.
2. Add a failing spec in `test/01_unit/compiler/backend/linker/` from that
   minimal object set.
