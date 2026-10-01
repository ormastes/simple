# Windows MSVC bootstrap depends on an UNTRACKED env script

- **Date:** 2026-09-02
- **Status:** RESOLVED 2026-09-06 — the script is tracked and was validated by
  real execution on Windows 11 + MSVC (transcript below). The recurrence guard
  proposed in *Unblock condition* remains UNIMPLEMENTED: no `scripts/check/`
  script asserts that files sourced by `scripts/bootstrap/**` are tracked.
- **Severity:** blocker for any fresh clone / worktree / CI on Windows MSVC

## Symptom

The sanctioned Windows MSVC bootstrap route cannot be run from a clean
checkout of any commit. Sourcing the documented env script fails:

```
/usr/bin/bash: line 7: scripts/setup/windows-msvc-bootstrap-env.shs: No such file or directory
```

## Root cause

`scripts/setup/windows-msvc-bootstrap-env.shs` has **never been committed**.
It exists only as an untracked file in one developer working copy.

Measured 2026-09-02 in `C:\Users\ormas\dev\simple`:

```
$ git ls-files --error-unmatch scripts/setup/windows-msvc-bootstrap-env.shs
error: pathspec '...' did not match any file(s) known to git

$ git status --porcelain scripts/setup/windows-msvc-bootstrap-env.shs
?? scripts/setup/windows-msvc-bootstrap-env.shs
```

Confirmed absent from the tracked tree of the session lane commit
`6e9660e36719c9775c742b7e7c331c8b55068184` (134,490 files):

```
$ git ls-tree --name-only 6e9660e3671 scripts/setup/ | grep -i msvc
(no output)
```

The sibling `scripts/setup/llvm-toolchain-env.shs` IS tracked, which is why
the gap is easy to miss — the directory looks populated.

Local copy for reference: 5,050 bytes, md5 `687134754cc3803d035eaf1b41c8edbd`.
It puts LLVM 18 on PATH (`llvm-config` 18.1.8), which `llvm-sys 180` requires;
CLAUDE.md's LLVM-23 script is explicitly NOT a substitute, and the two must not
be sourced into one shell.

## Why the other guards miss it

Every pre-push guard checks tree structure, symbol sets, or source that is
present. None asserts that a file the documented build path SOURCES is
tracked. An untracked file is invisible to all of them.

## Impact

- Any fresh clone, `git worktree add`, or CI runner on Windows MSVC cannot
  bootstrap: the env script is simply not there.
- The dependency is silent — the failure surfaces as a missing-file error from
  the shell, far from the cause.
- Bootstrap receipts record `git rev-parse HEAD` and `git status --porcelain`
  (`produce-bootstrap-planner-admission-v2.shs:179-181`), so working around it
  by copying the file INTO the tree dirties the tree the receipt attests to.

## Unblock condition

Commit `scripts/setup/windows-msvc-bootstrap-env.shs`. Then add a guard
asserting that every script sourced or executed by `scripts/bootstrap/**` is
tracked, so this class cannot recur.

## Cross-platform impact

None. The file is Windows-MSVC-only and is not referenced by any Unix lane;
committing it changes no Unix behaviour.

## Resolution (2026-09-06)

`scripts/setup/windows-msvc-bootstrap-env.shs` was first ADDED to the tracked
tree by `cad645606aa` ("fix(bootstrap): Windows MSVC Stage 2 ADMITTED — six
distinct defects, hash-verified (#335)") and later touched by `1aa098f0973` and
`dae91969f20`. Re-verified at `origin/main` `a12a19eb775`:

```
$ git ls-files --error-unmatch scripts/setup/windows-msvc-bootstrap-env.shs
scripts/setup/windows-msvc-bootstrap-env.shs        # rc=0, tracked
$ git status --porcelain scripts/setup/windows-msvc-bootstrap-env.shs
                                                    # clean, no local delta
```

Tracked size is 8,347 bytes; the 5,050-byte / md5 `687134754cc3803d035eaf1b41c8edbd`
copy recorded above is the older untracked snapshot and is history, not the
current file.

### Real-execution evidence (Windows 11 Pro, MSVC 2022 Community, Git Bash)

Sourcing the tracked script and probing the toolchain:

```
$ . scripts/setup/windows-msvc-bootstrap-env.shs && echo "SOURCE_RC=0" \
    && command -v cl.exe && command -v link.exe && command -v llvm-config
SOURCE_RC=0
/c/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/cl.exe
/c/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/link.exe
/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc/bin/llvm-config

INCLUDE=C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC\14.44.35207\include
LIB=C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC\14.44.35207\lib\x64
ABI=msvc/msvc/1        # SIMPLE_WINDOWS_ABI / SIMPLE_LINKER_FLAVOR / SIMPLE_NO_STUB_FALLBACK
LLVM_SYS_180_PREFIX=/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc
```

End-to-end compile + link + run, proving `INCLUDE` and `LIB` actually resolve
(not merely that the variables are set):

```
$ cat > t.c <<'C'
#include <stdio.h>
int main(void){ printf("msvc-env-ok\n"); return 0; }
C
$ ( . scripts/setup/windows-msvc-bootstrap-env.shs \
     && cl.exe -nologo t.c -Fe:t.exe && ./t.exe && echo "run_rc=$?" \
     && llvm-config --version )
t.c
msvc-env-ok
run_rc=0
18.1.8
```

`cl.exe` reports 19.44.35228 (x64) and drives `link.exe` 14.44.35228.0. Note
that MSVC-style `/flags` are path-mangled by MSYS in Git Bash (`/nologo` became
`C:/dev/tool/Git/nologo`); use the `-flag` spelling, as above.

### Still open (tracked here, not fixed by this change)

- **No recurrence guard.** The *Unblock condition*'s second clause — a check
  that every script sourced or executed by `scripts/bootstrap/**` is tracked —
  has no implementation; `scripts/check/` contains no such guard.
- **Host paths are hard-coded** in the script: MSVC `14.44.35207`, Windows SDK
  `10.0.26100.0`, and `/c/dev/install/clang+llvm-18.1.8-x86_64-pc-windows-msvc`.
  A CI runner or fresh clone with a different layout gets the script's
  fail-closed `missing PATH component` error rather than a silent misbuild, but
  it still will not bootstrap without matching that layout.
