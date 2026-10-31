# `std.file_system` write functions are mocks that return `true` without writing

- **Filed:** 2026-09-06
- **Severity:** blocker (release critical path — `native-build` could not build a three-line hello world)
- **Status:** RESOLVED 2026-10-31 — every mock in both `std.*.file_system` families removed; driver importers migrated to `std.io_runtime` (see below)
- **Host:** aarch64-unknown-linux-gnu, Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`

## Symptom

```
bin/simple native-build hw.spl -o hw     # three-line hello world
```

exits 1. Every lowering checkpoint reports zero errors
(`[bootstrap-error-count] point=entry|post-lowering|post-diagnostics|post-store count=0`),
the object file is produced correctly, and then the post-compile capsule
receipt check rejects it:

```
reason: native-capsule-receipt-invalid:.tmp.<...>.hw
error: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s)
```

## Which condition fired

`driver_native_capsule_result_valid_v1`
(`src/compiler/80.driver/driver_aot_native_output.spl`) has five independent
failure modes. **Condition 3 fired: `<object_path>.capsule-receipt` does not
exist.**

The two values, measured with temporary instrumentation on both sides of the
same build (instrumentation since removed):

```
[DBG-W] path=build/native_cache/s635.../object..tmp....hw.o.capsule-receipt
        wrote=true  len=1451  exists_after=false
[DBG-C] path=build/native_cache/s635.../object..tmp....hw.o.capsule-receipt
        exists=false  obj_exists=true  identity_valid=true
```

So the writer's `_sffi_file_write_text` returned **`true`** and
`_sffi_file_exists` on the very same path immediately afterwards returned
**`false`**. Nothing else was wrong: the object existed, the capsule identity
was valid, the paths on both sides were byte-identical.

## Root cause

`driver_aot_native_output.spl:10` imported
`use std.file_system.{file_write_text, file_read_text}`.

`std.file_system` resolves into `nogc_async_mut.file_system.file_ops`, whose
header says outright "Mock implementations for pure Simple demonstration"
(`src/lib/nogc_async_mut/file_system/file_ops.spl:5`). Its `file_write_text`
(`:58-68`) performs **no I/O at all**:

```
fn file_write_text(path: text, content: text) -> bool:
    if path == "" or content == nil:
        return false
    true
```

Reproduced in isolation, independent of the compiler driver:

```
use std.file_system.{file_write_text}
use std.io_runtime.{file_exists, file_write_exact}
...
MOCK write ok=true exists=false      # std.file_system.file_write_text
REAL write ok=true exists=true       # std.io_runtime.file_write_exact
```

This is the **second instance of a hazard the same file's own header already
documents** at `:34-40`, where `file_read_bytes` was removed for exactly this
reason: *"the flat function registry is keyed on NAME ALONE, so it could hijack
any call site in an import closure that included this module"*. The compiler
itself warns about the live collision during the build:

```
warning: public function `file_write_text` has 3 co-compiled definitions with
2 differing signatures ((text,text)->() vs (text,text)->bool); JIT call sites
resolve by exact arg-type match ... falling back to the last definition when
types are ambiguous [compiler_cross_module_private_symbol_collision]
```

### Second silent breakage from the same cause

The receipt was not the only casualty. Two other writes in the same driver used
the same mock and also vanished while reporting success:

- `phase.marker` (`:977`) — the codegen-phase forensic marker.
- `.cache_scope` (`:987`) — the lane-ownership marker that
  `scripts/check/check-cache-scope-ownership.shs` reads **fail-closed**. A
  fail-closed gate was reading a file that was never being written.

Both are present again after the fix.

## Fix applied (this change)

`src/compiler/80.driver/driver_aot_native_output.spl` only:

- dropped `use std.file_system.{file_write_text, file_read_text}`;
- `_sffi_file_write_text` now calls `std.io_runtime.file_write_exact`
  (`io_runtime.spl:250`) — the one-call honest runtime status, correct here
  because every caller writes into `cache_scope_root`, which
  `_sffi_dir_create(cache_scope_root, true)` has already created, and every
  caller treats `false` as a hard build error;
- `_sffi_file_read_text` now calls `std.io_runtime.file_read_nullable`
  (`io_runtime.spl:181`). Note: measured 2026-09-06 the real definition
  happened to win for **reads**, so the read side was fragile-by-luck, not
  observed-broken; it is moved for the same reason, and that is stated in the
  code comment rather than claimed as a fixed break.

The capsule receipt check itself was **not** weakened. It is an authenticated
cache checkpoint and still verifies identity, object existence, source
identity, fingerprint, and exact receipt text.

## Resolved 2026-10-31 (signature-differing mocks: `dir_create`, `dir_list`, `file_size`, `file_write_bytes`)

Scope: only these four, in both `std.nogc_sync_mut.file_system` and
`std.nogc_async_mut.file_system`. Items 1-3 under "Still open" stay open for
the remaining identical-signature mocks (`file_write_text`, `file_read_text`,
`file_create`, `file_write_lines`, `file_move`, `dir_delete`, ...).

- **Root cause.** `dir_ops.spl` defined `dir_create(path) -> bool` and
  `dir_list(path) -> [text]?`, `metadata.spl` defined `file_size(path) -> i64?`
  and `file_ops.spl` defined `file_write_bytes(path, [i64])` as no-effect
  mocks whose signatures differ from the real `std.nogc_sync_mut.io_runtime`
  owners. The seed binds an unqualified call by bare name over the whole
  co-compiled closure (interpreter: flat `functions` map,
  `src/compiler_rust/compiler/src/interpreter_eval.rs:606`; MIR:
  last-definition fallback in `mir/lower/lowering_expr_call.rs:847-867`), so the
  build printed `compiler_cross_module_private_symbol_collision` for all four
  and calls could reach the wrong body. Independently, `dir_walk_dirs` filtered
  `dir_walk` output for directories, but `rt_dir_walk` only returns
  non-directory entries, so it was `[]` for every tree.
- **Fix (option b, stdlib).** The four mocks are deleted and the modules
  `export use` the real io_runtime functions. `dir_copy`, `dir_is_empty` and
  `dir_list_detailed` use `dir_list_optional` (so a read failure is still
  `false`/`nil`), `dir_list_detailed` reports real `is_directory`/`size`,
  `dir_size` and `disk_usage` use the `i64` `file_size`, `temp_dir_create`
  calls `dir_create(path, false)`, `tree_print_recursive` uses the array
  `dir_list`, and `dir_walk_dirs` walks breadth-first over `dir_list` +
  `dir_exists`. The four collision warnings no longer appear.
- **Why not option a.** Making unqualified calls prefer the caller's own or
  imported symbol needs the caller's module and import table to be carried
  into candidate selection in two engines: the interpreter, where every module's
  functions are merged into one by-name map at many insert sites, and MIR
  lowering, which has no import map. That change is not narrow, and it needs a
  seed rebuild. `interpreter_bare_fn_name_collision_file_read_text_at_2026-10-30.md`
  tracks it.
- **Test.** `test/01_unit/lib/io/file_system_dir_walk_dirs_copy_real_spec.spl`
  checks filesystem state for sync and async `dir_walk_dirs` / `dir_copy`:
  0/2 before, 2/2 after.

## Resolved 2026-10-31 (all remaining mocks, both families)

Follow-up to the section above, on the same branch. Every function in
`src/lib/{nogc_sync_mut,nogc_async_mut}/file_system/` is now a re-export of a
real owner or a real wrapper over a runtime primitive. `file_exists_mock` is
gone.

| Name | Was | Now |
|---|---|---|
| `file_read_text` | `text?`, "mock file content: <path>" | re-export `io.file_ops.file_read_text` (`text`, "" when unreadable) |
| `file_read_lines` | wrapper over the mock read | re-export `io.file_ops.file_read_lines` |
| `file_write_text` | `true`, nothing written | re-export `sffi.io.file_write_text` |
| `file_move` | copy+delete over mocks | re-export `sffi.io.file_move` (`rt_file_move`) |
| `file_create` | `true`, nothing created | `file_create_exclusive(path, "")` (O_EXCL) |
| `file_write_lines` / `file_append_lines` | over the mock write | over the real write/append |
| `dir_delete` | `true`, nothing deleted | re-export `sffi.fs.dir_delete`, which now calls `rt_dir_remove(path, false)`: the `rt_dir_delete` it declared exists in neither runtime |
| `dir_delete_all` | `true` | `dir_remove_all` |
| `file_modified_time` | `Some(1700000000)` | re-export `io.file_ops.file_modified_time` (`i64`, 0 = unavailable); `watch_*` adapted |
| `file_created_time` / `file_accessed_time` | `Some(1700000000)` | `nil`: no runtime primitive, so fail closed |
| `file_is_file` | "has an extension" | `file_exists and not dir_exists` (stat) |
| `file_is_symlink` | `false` | exists and lstat sees neither a regular file nor a directory |
| `file_is_readable/writable/executable` | exists / extension | owner bits from `rt_file_mode` |
| `file_info` | size 1024, mtime 1700000000, mode 755 | real size, mtime and mode |
| `file_get_permissions` | decimal 755 | `rt_file_mode` |
| `file_set_mode/_permissions`, `file_make_*` | `true`, nothing changed; decimal 755/644/444 | chmod via `rt_package_chmod`; octal 0o755/0o644/0o444 |
| `glob_match` | own copy taking `(pattern, path)` | re-export `std.glob.glob_match(path, pattern)`. Same parameter types in the opposite order, so name binding swapped the arguments silently |
| `glob_find(pattern, root)` | collided with `fs.glob_find(pattern)` | renamed `glob_find_under` (it had no callers) |
| `symlink_create` / `symlink_read` | `true` / "/mock/target" | `false` / `nil`: no symlink(2)/readlink(2) primitive, so fail closed |
| `symlink_resolve` | the path itself | `sffi.fs.file_canonicalize` (realpath) |
| `random_suffix` | "abc123" | `{pid}_{unix micros}` |

Callers adapted:
- `src/app/itf/*`: `file_read_text` changed to `io_runtime.file_read_nullable`, so the `== nil` checks keep their meaning.
- All "Still open" item-2 driver importers, plus `driver_vhdl_artifacts` and `driver_compile_vhdl_source_map`, migrated off `std.file_system`:
  - writes go to `io_runtime.file_write`, which creates a missing parent directory, so a real write cannot start failing where the mock said `true`;
  - reads go to `file_read_nullable`;
  - `shb_writer`'s tmp-to-final step uses `file_rename`.
- `driver_api_interpret`'s redundant `unsafe` wrappers are dropped. That makes
  `interpreter_cache_io_facade_contract_spec` pass (it failed 0/1 before).

Test: `test/01_unit/lib/io/file_system_dir_walk_dirs_copy_real_spec.spl` now
has 6 examples: 2/6 against the parent commit e32f8326dbb (the 4 new examples fail), 6/6 after. It covers `dir_walk_dirs`, `dir_copy`, `dir_walk_files` with an
extensionless file, real `file_write_text`/`file_read_text`/`file_modified_time`,
`file_create`/`file_move`/`dir_delete`/`file_set_mode` on disk, and the
`glob_match` argument order. No `compiler_cross_module_private_symbol_collision`
warning names a file_system function any more.

Residual risk:
- The `path_ops` wrappers (`path_join`, `path_basename`, ...) are real, but their names are reused by about 40 helpers across the tree.
- `dir_delete_all` and `dir_is_empty` share a name and signature with `std.nogc_*.fs`, and do the same thing.
- The seed's name-only binding is unchanged (`interpreter_bare_fn_name_collision_file_read_text_at_2026-10-30.md`).

### Review follow-up 2026-10-31 (data safety of the now-real recursive ops)

When the mocks became real, recursive operations could destroy data:
- `dir_move` (copy then `dir_delete_all`) destroyed the tree when `dest` was the source itself or lay inside it. It now compares canonical paths and refuses that case. It also refuses a `dest` that already exists. It tries `file_rename` first and copies then deletes only when the rename fails.
- `dir_walk_dirs` and `dir_copy` followed symlinks to directories through `dir_exists`, so a link cycle would recurse without end. Both now check `dir_is_real_no_follow` (lstat). `dir_copy` copies only real directories and regular files and skips links; the runtime has no symlink(2) primitive to recreate a link.
- `dir_delete_all` refuses a root that is not a real directory, so the target of a directory symlink is never emptied.
- `sffi.fs.dir_delete` now goes through `host_path_native`. `permissions.spl` uses `sffi.host.package_chmod` instead of declaring its own extern.

Spec: 5 new data-safety examples in the same file. 3 of them failed before this follow-up and all 11 pass after.

Latent homonym, not fixed: `src/compiler/10.frontend/core/aop.spl:120` defines
`glob_match(pattern: text, target_name: text) -> bool`. That is the REVERSED
argument order of `std.glob.glob_match(path, pattern)`, with identical types, so
no collision warning can fire. If both ever land in one co-compiled closure,
name-only binding can silently swap the arguments, exactly as the
`file_system` copy did. Rename it, for example to `aop_glob_match`, when that
module is next touched.

## Previously open (now addressed above)

1. **The mock itself.** `src/lib/nogc_async_mut/file_system/file_ops.spl` still
   exports `file_write_text`, `file_write_bytes`, `file_write_lines`,
   `file_append_text`, `file_append_lines`, `file_create`, `file_delete`,
   `file_rename`, `file_copy`, `file_move` and `file_exists` as mocks that
   report success without doing anything (`file_exists_mock` claims any path
   starting with `/` or `.` exists). Making them real changes stdlib semantics
   for every caller and needs its own reviewed change; deleting them, as was
   done for `file_read_bytes`, breaks the `use std.file_system.{...}` imports
   below. Either route is out of scope for a release-blocker fix.

2. **11 other product-code importers of the mock writers**, each a potential
   silent no-op with a `true` return (not investigated, not fixed):

   ```
   src/compiler/80.driver/driver_riscv_gen2_product.spl:9        file_write_text
   src/compiler/80.driver/driver_public_headers.spl:2            file_write_text, file_read_text
   src/compiler/80.driver/driver_api_project_build.spl:9         file_write_text
   src/compiler/80.driver/driver_vhdl_artifacts.spl:5            file_write_text
   src/compiler/80.driver/driver_compile_vhdl_source_map.spl:11  file_write_text
   src/compiler/80.driver/shb/shb_writer.spl:8                   file_move
   src/compiler/80.driver/cache/lease/lease.spl:23               file_write_text
   src/compiler/80.driver/cache/gc/fast_gc.spl:74                file_move
   src/compiler/80.driver/cache/gc/mark_sweep.spl:28             file_move
   src/compiler/80.driver/watcher/smf_manifest.spl:14            file_write_text
   ```

   `cache/lease/lease.spl` and `watcher/smf_manifest.spl` are the two worth
   looking at first: a lease file and a cache manifest that are never written
   but always report written are the same failure shape as the receipt.

3. **No gate covers this class.** Nothing fails when a stdlib function reports
   success without performing its effect. A `check-` guard that asserts
   post-conditions for the `std.file_system` write API would have caught both
   this and the `file_read_bytes` precedent.
