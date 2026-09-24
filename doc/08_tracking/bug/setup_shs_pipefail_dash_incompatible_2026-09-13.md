# `setup.shs` fails on every Linux host where `/bin/sh` is dash

- **ID:** `setup_shs_pipefail_dash_incompatible_2026-09-13`
- **Date:** 2026-09-13
- **Status:** OPEN (2026-09-13)
- **Severity:** P1 (blocks the documented `sh scripts/setup/setup.shs` entrypoint
  on any fresh Linux checkout with a POSIX `/bin/sh`)
- **Component:** `scripts/setup/materialize-symlinks-windows.shs`
- **Found in:** BUGFIX-6 fan-out lane, worktree `/home/yoon/dev/simple-bugfix-6`,
  base `a6450c9d6f5`

## Symptom

```
$ sh scripts/setup/setup.shs
/home/yoon/dev/simple-bugfix-6/scripts/setup/materialize-symlinks-windows.shs: 39: set: Illegal option -o pipefail
setup: FAILED to materialize git symlinks (rc=2); the checkout will not compile
```

`/bin/sh -> dash` on this host (Ubuntu default). `setup.shs:39` invokes
`materialize-symlinks-windows.shs` explicitly via `sh` (not `bash`), and that
script's own first statements are:

```sh
#!/bin/sh
...
set -u
set -o pipefail   # line 39 — NOT POSIX, dash rejects it
...
case "$(uname -s ...)" in
    MINGW*|MSYS*|CYGWIN*) : ;;
    *) echo "... this script is Windows-only ..."; exit 0 ;;
esac
```

The `set -o pipefail` line runs **before** the `uname -s` platform guard that
is supposed to make this script a documented no-op on Linux/macOS ("the
script's own first statement is a uname -s case that exits 0 for anything that
is not MINGW*/MSYS*/CYGWIN*" — comment in `setup.shs`, no longer true: `set -u`
and `set -o pipefail` are the actual first statements). Under dash, `set -o
pipefail` is an "Illegal option", exits 2 immediately, and `setup.shs` treats
any nonzero `materialize_rc` as fatal, so the entire setup aborts before
reaching the part that actually creates the `bin/simple` symlink.

## Distinction from the related record

`run_phase1_local_invokes_bash_bootstrap_with_posix_sh_2026-09-09.md` covers a
different bug with the same error text: there, a genuinely Bash-authored
script (`bootstrap-windows.sh`, `#!/bin/bash` semantics) was invoked with `sh`
by its *caller*, so the fix was to call it with `bash`. Here the script itself
is declared `#!/bin/sh` and is meant to be POSIX-portable (it deliberately
no-ops on non-Windows platforms) — the bug is that its own body uses a
bash/ksh-only builtin option before the OS guard that would make that
irrelevant on Linux. Invoking it with `bash` would silence the symptom but
misrepresents the script's own contract (`#!/bin/sh`, called via `sh` by
design per its usage comment).

## Reproduction (Linux, aarch64, this host)

```
$ sh scripts/setup/setup.shs
setup: FAILED to materialize git symlinks (rc=2); the checkout will not compile
$ echo $?
2
```

Confirmed with a 3-line isolated fixture: `#!/bin/sh` + `set -u` + `set -o
pipefail` run via `sh fixture.sh` reproduces the identical
`Illegal option -o pipefail` text and exit 2 (`dash` package, no
Windows-specific content needed).

## Fix direction (not applied — out of this lane's shard)

Move `set -o pipefail` (and any other bash-only option) to *after* the
`uname -s` platform guard, so the Linux/macOS no-op path never reaches a
bash-only builtin. The Windows-only body below the guard already runs under
git-bash/MSYS `sh`, which is bash-backed, so `set -o pipefail` remains valid
there.

## Workaround used by this lane

Bypassed `setup.shs` entirely for this worktree: created
`bin/release/aarch64-unknown-linux-gnu/simple` as a symlink to the sibling
shared clone's already-built seed
(`/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple`,
sha256 prefix `3d120a6f9ab5704b`) and `bin/simple ->
release/aarch64-unknown-linux-gnu/simple`, matching what `setup.shs` would
have produced had a release binary already existed in this worktree. This
worktree has no build of its own; every fan-out lane on this host most likely
hits the same `rc=2` and needs either this workaround or a real fix.
