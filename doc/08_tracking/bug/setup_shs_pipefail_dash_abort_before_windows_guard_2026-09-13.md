# `scripts/setup/setup.shs` aborts on Linux: `set -o pipefail` under dash fires before the Windows-only early-exit guard

- Status: OPEN (2026-09-13)
- Filed: 2026-09-13, lane BUGFIX-8, while preparing a fresh worktree
  (`/home/yoon/dev/simple-bugfix-8`) for `bin/simple`
- Component: `scripts/setup/setup.shs` -> `scripts/setup/materialize-symlinks-windows.shs`
- Host: Ubuntu 24.04.4 LTS, `/bin/sh -> dash`

## Symptom

A plain, first-time `sh scripts/setup/setup.shs` on a fresh Linux worktree
fails outright and never creates `bin/simple`:

```
$ sh scripts/setup/setup.shs
/home/yoon/dev/simple-bugfix-8/scripts/setup/materialize-symlinks-windows.shs: 39: set: Illegal option -o pipefail
setup: FAILED to materialize git symlinks (rc=2); the checkout will not compile
```

Exit code 2 (`materialize_rc=2`, propagated from
`scripts/setup/setup.shs:39`'s `sh "${repo_root}/scripts/setup/materialize-symlinks-windows.shs" ... || materialize_rc=$?`).

## Root cause

`scripts/setup/materialize-symlinks-windows.shs` is a Windows-only helper.
Its own header comment says as much, and it is designed to be a no-op
everywhere else via a `uname -s` case dispatch:

```sh
#!/bin/sh
...
set -u
set -o pipefail          # <-- line 39, BEFORE the uname guard below

SELF=materialize-symlinks-windows

case "$(uname -s 2>/dev/null || echo unknown)" in
    MINGW*|MSYS*|CYGWIN*) : ;;
    *)
        echo "$SELF: this script is Windows-only (git-bash/MSYS); nothing to do on $(uname -s 2>/dev/null)" >&2
        exit 0
        ;;
esac
```

`set -o pipefail` is a bash/ksh extension, not POSIX `sh`. On any system where
`/bin/sh` is dash (Debian/Ubuntu default, and this host) — or any other
POSIX-only `sh` — that line itself is a hard error and aborts the script
**before** the `uname -s` case statement ever runs, so the documented
"Windows-only, no-op elsewhere" contract never takes effect. The script was
apparently authored/tested only on a `bash`-as-`/bin/sh` or macOS
(`/bin/sh` there is also not dash, so this may not reproduce on macOS)
system where `set -o pipefail` silently succeeds.

`scripts/setup/setup.shs` invokes it unconditionally (`scripts/setup/setup.shs:33-39`)
with `sh "${repo_root}/scripts/setup/materialize-symlinks-windows.shs" ...`,
explicitly using `sh` (not `bash`), and treats **any** non-zero exit as fatal:

```sh
if [ "${materialize_rc}" -ne 0 ]; then
    echo "setup: FAILED to materialize git symlinks (rc=${materialize_rc}); the checkout will not compile" >&2
    exit "${materialize_rc}"
fi
```

So the net effect on a dash-`/bin/sh` Linux host is: `setup.shs` always fails
at this step, before it ever reaches the part that actually creates
`bin/simple` (`scripts/setup/setup.shs:45` onward, `ln -sf
"release/${PLATFORM_TRIPLE}/simple" simple`). A fresh clone/worktree cannot
bootstrap `bin/simple` via the documented `scripts/setup/setup.shs` entry
point on such a host at all.

## Reproduction

```sh
$ ls -la /bin/sh
lrwxrwxrwx 1 root root 4 ... /bin/sh -> dash
$ cd <fresh-worktree>
$ sh scripts/setup/setup.shs
/.../scripts/setup/materialize-symlinks-windows.shs: 39: set: Illegal option -o pipefail
setup: FAILED to materialize git symlinks (rc=2); the checkout will not compile
$ echo $?
2
```

Isolated to the one line:

```sh
$ dash -c 'set -o pipefail'
dash: 1: set: Illegal option -o pipefail
```

## Impact

Blocks the documented, sanctioned `scripts/setup/setup.shs` path
(`.claude/rules/commands.md` "## Setup") for creating `bin/simple` and the
MCP server wrappers on any fresh Linux (or other dash-`/bin/sh`) worktree —
exactly the situation a newly created bugfix-lane worktree is in. Every
already-set-up worktree in this fleet either predates this regression, was
set up on a host where `/bin/sh` happens to be bash/POSIX-`pipefail`-tolerant,
or had `bin/simple` symlinked in by hand (as this lane did, working around it
by hand-linking `bin/release/<triple>` from the shared main worktree instead
of running `setup.shs`).

## Fix direction (not applied here — filed per instruction, not fixed)

Either:
1. Move `set -o pipefail` to after the `uname -s` case's early `exit 0`, so
   the Windows-only body opts into it only once it knows it is actually
   running under a bash-like shell (git-bash/MSYS/Cygwin normally ship
   `bash` as `sh` or the script could `#!/usr/bin/env bash` instead of
   `#!/bin/sh`), or
2. Drop `set -o pipefail` entirely if the script's own pipelines already
   check exit codes directly (the header comment for the rest of the script
   already emphasizes reading exit status "directly into a variable... never
   through a pipe", suggesting `pipefail` may not even be load-bearing for
   this script's actual logic), or
3. Have `scripts/setup/setup.shs` invoke it with `bash` explicitly instead of
   the generic `sh` it uses today, if MSYS/git-bash's `sh` is expected to be
   bash-compatible anyway.

Whichever direction is chosen, add a regression check that runs
`materialize-symlinks-windows.shs` under dash (or plain POSIX `sh`) on a
non-Windows `uname -s` and asserts exit 0.
