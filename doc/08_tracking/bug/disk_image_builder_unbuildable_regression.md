# BUG: os.port.disk_image builder is unbuildable (both interp and native paths)

**Status:** open
**Severity:** high (blocks building any SimpleOS FAT disk image from Simple)
**Component:** compiler (interp semantic + LLVM native codegen) / `os.port.disk_image`
**Found:** 2026-07-08, staging a clang hello ELF onto a FAT32 image

## Symptom

`bin/simple run build/os/elfexec/build-fsexec-img.spl` (and any program importing
`os.port.disk_image`) fails to build via BOTH execution paths:

- **Interpreter / JIT fallback:**
  `error: semantic: cannot iterate over this type`
  (preceded by `HIR lowering error: Unsupported feature: cannot infer field type
  while lowering _push_str8: struct 'String' field 'length'`).
- **Native-build (`bin/simple native-build ...`):** gets past semantics, then
  `llc-18: error: multiple definition of local value named 'l5'` (LLVM IR name
  collision in the emitted `.ll`).

The existing `build-fsexec-img.spl` (unchanged, git-untracked) fails identically —
so this is a **shared regression in `os.port.disk_image` or a dependency**, not in
any one caller. The committed `fat32-fsexec.img` / `fat32-clang.img` were built
2026-07-06 (before the regression) and still work; they cannot currently be
rebuilt.

## Notes

- Basic `[u8]` I/O (`rt_file_read_bytes` / `rt_file_write_bytes` / index
  assignment) builds and runs fine via the interpreter — so the break is specific
  to a construct in `disk_image` (a `for ... in` over a type whose element type is
  unresolved because of the `String.length` field-inference gap), not to byte I/O
  generally.
- Likely introduced by parallel-session churn between 2026-07-06 and 2026-07-08.

## Workaround in place

`examples/09_embedded/simpleos_hello_c/patch_fsexec_image.spl` binary-patches a
known-good base image (replacing the `/FSEXEC.ELF` payload + FAT chain + dirent
size) using only `[u8]` ops, bypassing `disk_image.build`. This is how
`scripts/os/build_clang_hello_ring3.shs` stages the clang hello. It depends on a
pre-existing base image, so `disk_image` still needs fixing to bake images from
scratch.

## Fix direction

Two independent compiler bugs to chase (either unblocks the interp path or the
native path):
1. Interp: resolve the `String.length` field-type inference so the `for ... in`
   in `disk_image` type-checks (`cannot iterate over this type`).
2. Native: the `llc` "multiple definition of local value 'l5'" — a duplicate SSA
   value name in emitted LLVM IR for whatever construct `disk_image` uses.

## Triage note (2026-07-17)

Likely fixed by commit `2138b3d9fca6` ("fix(disk-image): FAT32 builder — field default, truncate u64 unbox, 8.3 names, dynamic FAT sizing", 2026-07-11): commit's own E2E verification shows `nested_payloads` omitted, `ring-3 FSEXEC_OK rc=42` — a working disk-image build+boot. The interp-path `cannot iterate over this type` symptom is resolved. The native-build LLVM "multiple definition of local value 'l5'" half of the symptom is not explicitly re-confirmed in that commit message; pending runtime verification via native-build from source on current HEAD.
