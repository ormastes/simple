# Full CLI native link: 5 Simple symbols with no implementation

Status: verification-pending
Date: 2026-11-15

## Symptom
`native-build src/app/cli/main.spl` with the phase-1 seed compiled every
module (`compiled=5 reused=3141 failed=0`) and then refused the link:
`5 internal Simple symbol(s) have no implementation ...: _now_ms,
file_metadata, spl_fonts_call_init_blob, spl_fonts_call_init_path,
spl_fonts_call_layout_text`. The hosted lane links the C core runtime
(`core_c_runtime/simple_runtime.lib`), not the Rust runtime.

## Root causes
1. `_now_ms` (`src/os/_QemuRunner/os_build_run.spl:219`): the function is
   `pub fn _now_ms` in `runner_targets.spl`, imported only through
   `use os._QemuRunner.runner_targets.*`. The glob import resolves it for
   type-checking but native codegen emits the bare name `_now_ms` instead of
   `os___QemuRunner__runner_targets___now_ms` (glob import of an
   underscore-prefixed name is a resolver/codegen gap). Fixed locally with an
   explicit `use ...runner_targets.{_now_ms}`; the glob gap itself remains open.
2. `file_metadata` (`std.nogc_{sync,async}_mut.fs.flat`): a bare
   `extern fn file_metadata` with no runtime symbol in either runtime
   (interpreter: `unknown extern function: file_metadata`). Replaced by a
   pure-Simple composition of `dir_exists`/`file_exists`/`file_size`/
   `file_is_regular_no_follow`/`file_modified_time`.
   **Remaining gap:** `is_symlink`, `readonly`, `created` are not observable
   through any C-runtime scalar probe and are reported `false/false/0`.
3. `spl_fonts_call_*`: implemented only in the Rust runtime
   (`wsffi_native.rs`); the C runtime had no twin. Added C twins in
   `src/runtime/runtime_native.c` with the same (ptr,len) contract.

## Evidence
Regression spec: `test/01_unit/lib/nogc_sync_mut/fs/flat_file_metadata_spec.spl`
(RED: `semantic: unknown extern function: file_metadata`; GREEN: 1 passed).

## Native CLI smoke (phase-1 seed, K1 `llvm` composition)
Build: `native-build --source src/compositions/kernel_llvm --source src/compositions/cuda_disabled --source src/compiler --source src/app --source src/lib --source src/plugins --entry-closure src/app/cli/main.spl`
-> `Build complete: 3153 compiled, 0 cached, 0 failed`, 84027 KB, 415 abort-stubs.
sha256 `7f9c35460ecc4deb39ba43a3cc76c81de87573d52b6b41032183a38a0b14bf40`.
(Without the K1 composition every command fails closed with `PLUG-E-K1-POLICY`.)
- `--version` -> rc=0, `Simple v1.0.0-rc.1`.
- `test <spec>` -> rc=1, `SCV-E-ADMISSION: snapshot-read-failed:test/cert/tool_qual/meta/deterministic/01_arithmetic.spl`
  (that path is a git symlink -> `../../positive/01_arithmetic.spl`; the native
  SCV snapshot reader (`src/lib/scv/compile_snapshot.spl`) refuses it, while the
  seed interpreter runs the same spec GREEN). **Open**, next gap for the native CLI.
