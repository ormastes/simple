# `scripts/setup/setup.shs` aborts on Linux: `set -o pipefail` under dash fires before the Windows-only early-exit guard
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


## Verification 2026-11-05 (worktree /tmp/wt-libbug-setupshs, branch work/libbug-linux-setupshs-20261105)

Host: aarch64 Linux, `/bin/sh -> dash`.

### Finding: the code fix is already present on release/1.0.0; a regression
### check was missing and has been added.

The pipefail-before-gate defect no longer exists on `origin/release/1.0.0`
(HEAD adfeae3765c). It was resolved on main and transplanted to the release
line by `88aac2ffe28` ("rebase(main): transplant current main tree onto
release/1.0", 2026-09-29/10-01), which both:

- moved `set -o pipefail` to AFTER the `uname -s` case gate in
  `scripts/setup/materialize-symlinks-windows.shs` (with an explicit comment:
  "Keep this after the host gate: /bin/sh is commonly dash on Linux, where
  `set -o pipefail` is a fatal error"), changed its shebang to
  `#!/usr/bin/env bash`, and
- changed `scripts/setup/setup.shs` to invoke the materializer with
  `bash` instead of `sh`.

### RED (historical reproduction, exact bug-doc failure)

The 2026-09-12 version of the materializer (commit `863438ffac8`, the state
the bug doc quotes) still fails exactly as filed:

```
$ dash /tmp/buggy-materialize.sh          # = 863438ffac8:scripts/setup/...
/tmp/buggy-materialize.sh: 39: set: Illegal option -o pipefail
EXIT=2
```

The same commit's `setup.shs` invoked the helper with plain `sh`
(`sh "${repo_root}/scripts/setup/materialize-symlinks-windows.shs" ...`),
propagating rc=2 as fatal — matching the bug doc verbatim.

### GREEN (current release/1.0.0)

```
$ sh scripts/setup/setup.shs              # /bin/sh is dash
materialize-symlinks-windows: this script is Windows-only (git-bash/MSYS); nothing to do on Linux
...
setup: LLVM toolchain available: major 23 (clang version 23.1.0 ...)
EXIT=0

$ bash scripts/setup/setup.shs            # full run, also exit 0
EXIT=0

$ dash scripts/setup/materialize-symlinks-windows.shs --bogus-option
materialize-symlinks-windows: ... nothing to do on Linux
EXIT=0                                    # gate fires before arg parsing

$ sh -n scripts/setup/setup.shs && dash -n scripts/setup/setup.shs   # OK
```

Notes:
- The Windows-guard behavior was verified by simulating a MINGW `uname`: the
  script no longer takes the no-op exit and proceeds into the body (under
  `bash` an unknown option is then rejected with exit 2, proving the gate
  passes MINGW-family hosts through).
- `sh -n`/`dash -n` on `materialize-symlinks-windows.shs` itself fails at
  line 1396 (`}` unexpected) because the post-gate Windows-only body
  legitimately uses bash-only syntax (`$'\r'`, `exec 8>&${fd}` coprocess
  style). That is by design: only the guarded prefix must be POSIX-clean, and
  behavioral exit-0 under dash on Linux is the real contract.
- `setup.shs` full runs emit a pre-existing WARNING that the tracked
  `bin/simple.exe` cannot run a std-importing program (rc=126) — unrelated
  stale-binary report, non-fatal by design (BUG-IT-1 guard is a report, not
  a gate).

### Regression check added

`test/01_unit/scripts/materialize_symlinks_windows_posix_sh_guard_test.shs`
(POSIX sh, no bashisms): asserts (1) exit 0 + "nothing to do on" note under
both `sh` and `dash` on a non-Windows host even when passed an unknown
option, and (2) with a simulated MINGW `uname` under `bash`, argument parsing
is reached (unknown option -> exit 2), proving the gate still admits Windows
hosts. Mutated-against-the-buggy-version check: pointing the test at the
`863438ffac8` version of the script fails with
`FAIL: sh: non-Windows no-op exited rc=2: ... Illegal option -o pipefail`
(exit 1), i.e. the test reproduces the original defect. Passes under
`sh`, `bash`, and `dash` on the fixed tree.
