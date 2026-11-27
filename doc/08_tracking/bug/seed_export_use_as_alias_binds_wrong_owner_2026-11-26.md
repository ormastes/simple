# Seed: `export use X.{name as alias}` binds a co-compiled directory name to the wrong owner

- Found: 2026-11-26, SOSIX fs facade lane (`src/lib/nogc_sync_mut/sosix/fs_v1.spl`).
- Seed: `C:/dev/keep/seeds/simple-local-20261126.exe` (interpreter, `test`).

## Repro
In `sosix/fs_v1.spl`:

    export use std.nogc_sync_mut.io.dir_ops.{is_dir as sosix_fs_is_dir, dir_create_all as sosix_fs_dir_create_all, dir_remove_all as sosix_fs_dir_remove_all}

Repoint `pure_runtime_v1.spl` to the aliases, then run
`test/03_system/app/container/feature/pure_simple_container_v1_spec.spl`.
Passing drops from 18 to 6. Re-exporting the same names without `as` passes 18/18.
Aliases of names from other modules in the same file (`file_hardlink as sosix_fs_hardlink`, `file_write as sosix_fs_write_file`) work.

## Expected
An `as` alias resolves to exactly the named owner symbol, whether or not another compiled module defines the same name.

## Workaround (in tree)
`fs_v1.spl` re-exports the directory names under their owner names. Remove this once the seed is fixed.

## Status 2026-11-26 (seed-alias lane): NOT REPRODUCIBLE on release/1.0.0 (c917ac12f15)
- Minimal repro `test/fixtures/export_alias_owner/` (owner_a and owner_b both define `is_dir`; facade does
  `export use ...owner_a.{is_dir as fa_is_dir}`) resolves correctly on `simple-local-20261126.exe`:
  alias -> owner_a, direct import -> owner_b. Guarded by
  `test/01_unit/compiler/interpreter/export_use_alias_owner_spec.spl` (2/2).
- The exact scenario (alias the three dir names in `sosix/fs_v1.spl`, repoint `pure_runtime_v1`) gives 18/18 on
  `pure_simple_container_v1_spec.spl`; so does aliasing without repointing. The re-export owner binding
  (`record_reexport_binding`, 1142e65f4de) already names the facade source's own declaration.
- No Rust change made. The original 18 -> 6 drop was probably the lane's tree state: `storage/rootfs_materialize_v1.spl`
  and `storage/storage_view_v1.spl` import the unaliased `is_dir`/`dir_*` names from `fs_v1`. A selective import of a
  name the module does NOT export silently binds another co-compiled `is_dir` (owner_b in the fixture) instead of
  failing; that leniency is the only wrong-owner behaviour found. Re-file with the failing tree if it recurs.

## Root cause and fix (2026-11-26, same lane)
Root cause: `collect_provided_names` (`interpreter_module/module_loader.rs`) built a module's provided surface from
`export_target_names`, which for `export use a.{x as y}` lists BOTH `x` and `y`. A facade therefore "provided" `x`,
and `use facade.{x}` passed the use-list check; the loader registers whole surfaces, so `x` then resolved to
whichever co-compiled module defined it (the wrong owner). The check was also warning-only (`[use-warning]`).
Fix: new `published_target_names` (alias only) feeds the provided set, and `check_unprovided_use_names` makes an
unprovided braced `use` name a hard semantic error naming module and symbol (cache-hit and fresh-load paths).
Evidence on `simple-local-20261126c.exe`: `test/fixtures/export_alias_owner/unexported_import.spl` now errors
(old seed printed `bound=owner_b`); Rust unit test `aliased_reexport_does_not_provide_the_source_name`;
specs: alias spec 2/2, pure container 18/18, containment_v1 19/19, plus 5 broad specs green. No in-tree site
relied on the fallback in the specs run.
