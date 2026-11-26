# Seed: `export use X.{name as alias}` binds a co-compiled directory name to the wrong owner

- Found: 2026-11-26, SOSIX fs facade lane (`src/lib/nogc_sync_mut/sosix/fs_v1.spl`).
- Seed: `C:/dev/keep/seeds/simple-local-20261126.exe` (interpreter, `test`).

## Repro
In `sosix/fs_v1.spl`:

    export use std.nogc_sync_mut.io.dir_ops.{is_dir as sosix_fs_is_dir, dir_create_all as sosix_fs_dir_create_all, dir_remove_all as sosix_fs_dir_remove_all}

Repoint `pure_runtime_v1.spl` to the aliases, then run
`test/03_system/app/container/feature/pure_simple_container_v1_spec.spl`.
Passing drops from 18 to 6. Re-exporting the same names without `as` passes 18/18.
Aliases of names from other modules in the same file (`file_hardlink as sosix_fs_hardlink`, `getpid as sosix_fs_getpid`) work.

## Expected
An `as` alias resolves to exactly the named owner symbol, whether or not another compiled module defines the same name.

## Workaround (in tree)
`fs_v1.spl` re-exports the directory names under their owner names. Remove this once the seed is fixed.
