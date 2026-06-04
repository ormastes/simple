# SimpleOS NVFS Submodule Migration — Detail Design

## File Movement
- Copy `examples/11_advanced/nvfs/src/*` to `src/os/services/nvfs/*`.
- Copy usable `examples/11_advanced/nvfs/test/unit/*` to `test/01_unit/os/services/nvfs/*`.
- Remove obsolete skip-only tests that existed only because the submodule was not linked.

## Adaptation
- Rewrite `examples.nvfs.src.*` imports to `os.services.nvfs.*`.
- Add `src/os/services/nvfs/__init__.spl`.
- Export `os.services.nvfs` from `src/os/services/mod.spl`.
- Replace migrated executable `pass_todo` sites with real in-memory extent behavior or `Err(FsError.Unsupported)` for unsupported async scrub.

## Cleanup
- Remove the `examples/nvfs` section from `.gitmodules`.
- Remove the `examples/11_advanced/nvfs` gitlink and working tree.
- Retire the remote GitHub project after verification.
