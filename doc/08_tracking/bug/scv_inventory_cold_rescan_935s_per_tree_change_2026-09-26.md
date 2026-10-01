# SCV inventory rescan costs about 935 s and 2 GB on the first compile after any checkout change

**Status:** open. **Host:** Windows x86_64-pc-windows-msvc, stage-2 self-hosted `simple_cli.exe`.

## Measurements

The first `simple_cli compile <file> -o <x>.smf` after the checkout changed:

| Trigger | Wall | Peak working set |
|---|---|---|
| fresh worktree, `SIMPLE_SCV_INVENTORY_COLD_INIT=1` | 952.1 s | 1,922,016 KiB |
| after `git checkout` to another commit | 744.4 s | 2,056,432 KiB |
| after a 1-file edit + CLI rebuild | 943.0 s | 2,057,108 KiB |
| fresh worktree, cold init, `ast_native_arena_spec` | 934.5 s | 1,923,424 KiB |

The next compile in the same tree takes 10–12 s and 745 MB.

Without cold init, a fresh checkout fails fast with
`SCV-E-ADMISSION: compile-event-journal-missing (first build in this checkout: rerun with SIMPLE_SCV_INVENTORY_COLD_INIT=1)`
(`src/app/compiler_entrypoint/inventory_events.spl:249`).

## Why it matters

- Any timing taken on a tree that is not primed is dominated by this rescan. One 900 s "compile hang"
  reported on the stage-2 lane matched it.
- The stage-2 lane primes the tree once with `scripts/bootstrap/bootstrap-scv-prime.shs`. A worktree
  that changes between builds, or an agent tree primed ad hoc, pays the full rescan again.
- The journal cursor (`build/scv/compile-events/CURRENT`) is keyed on `git_head`, so a checkout
  alone invalidates it even when the source content has not changed.

## Wanted

An incremental rescan keyed on changed paths, or on content rather than `git_head`. At minimum, a progress line,
so a rescan is not mistaken for a hang.
