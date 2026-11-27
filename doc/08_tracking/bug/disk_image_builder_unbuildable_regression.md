# BUG: os.port.disk_image builder is unbuildable (both interp and native paths)
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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

## Runtime re-check (2026-07-17)

Probe: `probe10_disk_image.spl` (minimal reproduction of `os.port.disk_image` usage).

- **Interpreter path (`bin/simple run`):** The JIT-rejection message reproduces
  verbatim (`HIR lowering error: Unsupported feature: cannot infer field type while
  lowering _push_str8: struct 'String' field 'length'`), but this is only an
  INFO-level JIT rejection; **the interpreter fallback succeeds** with output
  `BUILD_OK` and produces a valid, verified FAT32 image (`file` output: "DOS/MBR boot
  sector... OEM-ID SIMPLEOS... FAT (32 bit)... label SIMPLEOS"). This contradicts
  the doc's earlier hard `error: semantic: cannot iterate over this type` claim on
  the interp path — **the interpreter path is FIXED-AT-TIP**.

- **Native-build path (`bin/simple native-build`):** Still fails, but with a
  different error signature than documented. The doc's quoted `llc: error: multiple
  definition of local value named 'l5'` is no longer seen; instead:
  ```
  MIR lowering error: unresolved method call: is_ok
  MIR lowering error: unresolved method call: upper
  ```
  (repeated). The native path remains broken, but the specific blocking construct
  and symptom have shifted since 2026-07-08.

**Status correction:** Interp path is now fixed; native path still open with
altered error signature. Status remains OPEN (native blocker unchanged).


## Resolution (2026-11-25)

Root cause of the remaining interpreter-path failure: the 2026-09 tree
transplant `88aac2ffe28` resurrected a pre-fix revision of
`src/os/port/disk_image.spl`, dropping every declaration the 2026-07 fixes
added. `build()` referenced `flat_name83`, `nested_leaf_keys`,
`dir_long_name`, `nested_leaf_long_name` and `_push_vfat_name_units`
referenced `units`, none of which were declared, so any config with at
least one payload failed with `error: semantic: variable 'flat_name83'
not found` (the 2026-07-17 "interp FIXED-AT-TIP" note predates the
transplant).

Fix: restored `src/os/port/disk_image.spl` from the last known-good
revision `ae55a746719` (verbatim; its `std.common.encoding` imports are
still present and signature-compatible at HEAD).

Verification on this Windows host with the pinned seed
(`SIMPLE_LIB=src bin/simple.exe run`, interpreter fallback path):
- Flat payload probe: `BUILD_OK`, 2097152-byte image, `file` reports a
  valid FAT32 ("DOS/MBR boot sector ... OEM-ID SIMPLEOS ... FAT (32 bit)"),
  `HELLO   TXT` dirent present with correct payload bytes.
- Nested payload probe (`guest_path: "/usr/bin/clang"`): `BUILD_OK`, root
  dir contains `USR` and `BIN` subdirectory entries (attr 0x10) and the
  `CLANG` leaf entry.

Verification limits: `bin/simple.exe test test/01_unit/os/port/disk_image_builder_spec.spl
--mode=interpreter` cannot run at release/1.0.0 HEAD — the spec runner
itself fails with `unknown decorator '@representation_boundary'`
(known source/binary inconsistency between the 940-annotation commit
cfd89933699 and the pinned v1.0.0-rc.1 seed). For the same reason the
native-build half of the original symptom could not be re-attempted:
`native-build` stops at the same decorator in
`src/app/cli/native_build_main.spl` before reaching `disk_image` codegen.
The interpreter path — the blocker for building FAT images from Simple —
is fixed and verified; the native-build half remains unverifiable at HEAD
until the seed/decorator inconsistency is resolved.

**Status:** resolved (interpreter path); native-build half deferred to the
repo-wide seed/decorator repair, not a `disk_image` defect.
