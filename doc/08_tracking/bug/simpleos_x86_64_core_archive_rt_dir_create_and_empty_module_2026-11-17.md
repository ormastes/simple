# SimpleOS x86_64 core runtime archive: core_fs rt_dir_create ICE and empty-module "no C compiler"

Status: verification-pending
Found: 2026-11-16 (WSL Ubuntu-24.04, src b45dd8065b5, phase-2 `~/xc/simple-p2`, cranelift, `--target x86_64-unknown-simpleos`)

## Symptoms
1. `core_fs`: `Failed to compile function: rt_dir_create`; cranelift verifier:
   `mismatched argument count ... got 3, expected 2` (two call sites).
2. `io_runtime`: `no C compiler available for empty module object`.

## Root causes
1. `src/compiler/50.mir/text_extern_abi.spl` registers the `rt_dir_*` family in
   `text_arg_indices` (index 0 is split into ptr+len) but had no
   `text_extern_semantic_arity` row, so `expand_text_abi_args` split even the
   already-raw calls. `src/runtime/simple_core/core_fs.spl` DEFINES
   `rt_dir_exists` / `rt_dir_create_all` as raw `(path_ptr, path_len)` providers
   and calls them with two integer words; the first word was split again into
   3 operands against a 2-parameter callee. Rows added for the whole family
   (facade arity 1, create/remove 2) so only the text facade is split.
   Which two call sites the verifier flagged is NOT established. Two readings,
   neither reproduced: (a) the two `rt_dir_exists(...)` calls in
   `rt_dir_create_all` (inlined into `rt_dir_create`); (b) the
   `rt_dir_create_all(...)` and `rt_dir_exists(...)` calls written directly in
   `rt_dir_create`. The same arity rows cover both; the fix does not depend on
   which is right.
2. `driver_empty_object.spl::_eo_is_elf` did not recognise `*-simpleos`
   (an ELF target), returned nil, and the caller fell back to `find_c_compiler()`.

## Tests
- `test/01_unit/compiler/mir/dir_text_extern_arity_spec.spl` (red before, green after)
- `test/01_unit/compiler/80.driver/driver_empty_object_spec.spl` (SimpleOS, riscv64 EM 243 flags 5, i686 EM 3, armv7 EM 40 flags 0x05000400; follow-up added riscv64 + ELF32 writer)

## Unverified
Needs a rebuilt compiler: re-run `sosrt_core.sh`-style core archive build
(`check-simple-core-runtime-smoke.shs`, ARCHIVE_ONLY=1, TARGET=x86_64-unknown-simpleos).
The core_fs diagnosis comes from reading the code + log, not a reproduced
single-part build (the part build needs the SCV git context of ~/xcsos).

