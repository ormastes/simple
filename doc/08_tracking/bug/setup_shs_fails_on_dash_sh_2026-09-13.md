# scripts/setup/setup.shs fails on a dash /bin/sh host (rc=2, `bin/simple` never created)

- Status: OPEN (2026-09-13)
- Host: this Linux aarch64 box, `/bin/sh -> dash`
- Found setting up a fresh worktree for a todo-fixing lane.

## Repro

```
$ sh scripts/setup/setup.shs
/path/scripts/setup/materialize-symlinks-windows.shs: 39: set: Illegal option -o pipefail
setup: FAILED to materialize git symlinks (rc=2); the checkout will not compile
```

`setup.shs` (`scripts/setup/setup.shs:33-40`) unconditionally runs
`sh "${repo_root}/scripts/setup/materialize-symlinks-windows.shs" ...` — an
explicit `sh` invocation, not `./materialize-symlinks-windows.shs` honoring its
own shebang. `materialize-symlinks-windows.shs` starts with:

```
set -u
set -o pipefail
```

`set -o pipefail` is a bash/ksh extension; POSIX `sh`/dash rejects it as an
illegal option and exits 2 **before** the script reaches its own `uname -s`
guard (which would otherwise correctly no-op on non-Windows and exit 0). Since
`setup.shs` treats any non-zero exit from this helper as fatal
(`materialize_rc -ne 0` → `exit "${materialize_rc}"`), the whole setup aborts
on any host where `/bin/sh` is dash (Debian/Ubuntu default) — `bin/simple` is
never symlinked, and the checkout cannot run tests.

## Impact

Affects every fresh worktree/clone setup on a dash-`/bin/sh` Linux host. In
this session the workaround was to manually symlink
`bin/release/<triple>/simple` from a sibling worktree that already had it
(`bin/simple` and `bin/release/<triple>/simple` point at the already-built
binary in the primary clone) rather than rely on `setup.shs`.

## Suggested fix

Either invoke the helper with `bash` explicitly
(`bash "${repo_root}/scripts/setup/materialize-symlinks-windows.shs" ...`) in
`setup.shs`, or move `set -o pipefail` inside
`materialize-symlinks-windows.shs` to after the `uname -s` MINGW*/MSYS*/CYGWIN*
guard (or drop it — the script's own commentary says it should be a no-op on
non-Windows by construction, and pipefail is not load-bearing for its actual
NTFS-junction/hardlink logic).
