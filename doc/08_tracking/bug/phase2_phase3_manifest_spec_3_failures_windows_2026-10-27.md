# phase2_phase3_compatibility_manifest_spec: 3 failures on Windows seed (2026-10-27)

Spec: `test/02_integration/compiler/cache/phase2_phase3_compatibility_manifest_spec.spl`
Seen on the Windows Rust seed `bin/simple.exe`: 11/14 passing, identical 3 failures on the
base (10/13). Root causes found by small repro; two were NOT Windows-specific.

## 1. "keep writable caches separate and treat Phase 2 as read-only" (all platforms)
`phase_compatibility_manifest_read_only_v1` tested `wrong-phase3-cache-root` before
`phase2-cache-not-read-only`, so passing the Phase 2 root returned the wrong reason.
Fix: check the Phase 2 root first (`src/compiler/00.common/cache/phase_compatibility_manifest.spl`).

## 2. "consume only the current admitted M2 frontend projection" ("manifest-empty-or-unreadable")
Two causes:
- (all platforms) commit 8f7539a311a made `reverse_reference_receipt_digest_v1` return an
  algorithm-tagged `sha256:<hex>`, but the manifest validator and `phase_compatibility_admit_v1`
  only accepted bare 64-hex. `phase_compatibility_manifest_encode_v1` therefore returned `""`
  for every real manifest, the spec wrote an empty file, and the production reader reported
  `manifest-empty-or-unreadable`. Fix: new `phase_compatibility_receipt_digest_valid_v1`
  (accepts `sha256:<hex>` and bare hex).
- (Windows) the spec built roots from `rt_path_absolute(..)` which returns mixed
  `C:\dev\x\build/...`; the driver canonicalizes to `/`, so the manifest's Phase 3 root never
  matched (`wrong-phase3-cache-root`). Fix: normalize the spec roots with `.replace("\\", "/")`
  like the Windows-separators example already did.

## 3. "leave no final object when publication is interrupted" (Windows-only, OPEN)
`rt_file_copy_create_excl_no_follow` and `rt_file_link_create_excl_no_follow` are explicit
stubs returning false under `_WIN32`/`#[cfg(not(unix))]` in ALL three runtimes:
`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs` (seed),
`src/runtime/runtime.c`, `src/runtime/runtime_native.c`. So
`phase_compatibility_stage_artifact_io_v1` returns `staging-copy-failed` and the final object
is never published. This is runtime/seed Windows file I/O, not pure-Simple code. A pure-Simple
fallback is not possible without dropping the O_EXCL + no-follow + same-inode guarantees the
function exists for (`rt_file_copy` overwrites and follows links; no exclusive-create-and-link
primitive is exposed). Needed: Windows implementations in the three runtimes
(CreateFileW CREATE_NEW + FILE_FLAG_OPEN_REPARSE_POINT; CreateHardLinkW + file-id recheck),
llvm-mingw/windows-gnu only. Not done here.

Also affected: `src/lib/nogc_sync_mut/storage_roots/publisher.spl:135` uses the same stubbed primitives, so it is disabled on Windows too (Fable review note).
