# Bootstrap cannot start on Windows Git Bash / MSYS (lock identity + symlink mode)

- **Date:** 2026-08-24
- **Status:** FIXED (four defects), one PRE-EXISTING RED recorded below
- **Host:** `MINGW64_NT-10.0-26200`, Git Bash / MSYS, jj 0.38.0, perl 5.38.2 (msys)
- **Gate:** `sh scripts/check/check-bootstrap-portability.shs`

## Symptom

`scripts/bootstrap/bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap
--stop-after-stage2 --output=build/bootstrap` — the sole receipt-free lane —
exited immediately with:

```
ps: unknown option -- o
error: timed out waiting for bootstrap output ownership: /c/Users/ormas/dev/simple/build/bootstrap
```

No bootstrap had ever run on this host. The lock directory was empty, so there
was no concurrent bootstrap and nothing to time out against.

## Root causes

### 1. `ps -o` is unsupported by MSYS ps — lock identity unobtainable

`scripts/check/lib/portable-hardlink-lock.pl:ps_value` ran
`ps -o <field>= -p <pid>`. MSYS / Git Bash `ps` accepts only `-aeflsupW`, so
every call failed, `process_snapshot` returned empty, and
`portable_lock_actual_process_identity` returned 1 → `portable_lock_acquire`
returned **70**. The bootstrap can therefore never acquire its output lock on
Windows, despite the script's own `--help` advertising "Windows (Git Bash or
MSYS2)".

Fix: added `proc_stat_snapshot` reading `/proc/<pid>/stat` (field 22 =
starttime, field 5 = pgrp), which MSYS provides, as a **fallback only** — the
POSIX `ps -o` path is unchanged so Linux/macOS/FreeBSD behaviour is untouched.
The fallback preserves the read-twice-and-compare that guards PID reuse.
`ps_value` now forks explicitly so the child's stderr is discarded; otherwise
the usage error printed on every single call.

### 2. Every lock failure was reported as a timeout

`bootstrap-from-scratch.sh` collapsed rc 64/69/70/73/75 into
`error: timed out waiting for bootstrap output ownership`. The real fault (rc=70,
identity unavailable) was invisible, and the message actively pointed at a
nonexistent concurrent bootstrap. Now each rc names its actual cause; only rc=75
is reported as a timeout.

### 3. `ln -s` copies instead of linking on Windows shells

MSYS / Git Bash default to *copying* on `ln -s`. Two consequences:

- the immutable bootstrap authority publishes the seed as a symlink
  (`target/bootstrap` -> a generation dir); a copy leaves every generation stale
  while looking correct;
- Stage 3 source snapshotting classifies **dangling** links
  (`link-missing-hex`), which the default mode cannot create at all
  (`ln: failed to create symbolic link ...: No such file or directory`).

Fix: new `scripts/check/lib/portable-symlink-mode.shs` exports
`MSYS=winsymlinks:nativestrict` on MSYS/MINGW/CYGWIN only. That creates real
NTFS symlinks (including dangling ones) and **fails loudly** where the host
lacks Developer Mode / `SeCreateSymbolicLinkPrivilege` rather than copying
silently. It is a no-op on every other platform. Sourced by the bootstrap
script and the three symlink-dependent tests.

`portable_process_lock_test.shs` additionally asserts its symlink precondition:
where a host genuinely cannot create symlinks it prints an explicit
`UNSUPPORTED:` line for that lane instead of reporting a lock defect that does
not exist. It never passes the lane silently.

### 4. `jj git init` colocation default flipped (not Windows-specific)

`test/02_integration/bootstrap_stage3_jj_state_test.shs` asserts a **pure** jj
repo (`[ ! -e "$tmp/repo/.git" ]`) but called plain `jj git init`. jj 0.38
documents `--colocate` as "**This is the default**", so the repo now gets a
`.git` and the assertion fails on any current jj, on every platform. The test
now pins `--config git.colocate=false`, making its precondition explicit rather
than inherited from a default that moved.

## Verification

`sh scripts/check/check-bootstrap-portability.shs` progressed from failing at
its **first** lock check to passing all of:

```
portable process lock behavioral tests passed
PASS: immutable bootstrap authority publication and compatibility pointer
bootstrap_stage3_source_snapshot=true
bootstrap_stage3_jj_state=true
```

The symlink-alias lane is now genuinely exercised on this host (no `UNSUPPORTED`
line), so these are real passes, not skips.

## Still RED — pre-existing, NOT introduced here

`FAIL: MinGW runtime DLL is not staged`. The guard (line 224) requires
`"${rust_authority_profile_dir}/simple_runtime.dll"` to appear in
`scripts/bootstrap/bootstrap-from-scratch.sh`. The string `simple_runtime.dll`
appears **nowhere** in that script, at `origin/main` as well as in the working
tree — verified with
`git show origin/main:scripts/bootstrap/bootstrap-from-scratch.sh | grep -Fc ...`
→ `0`. The guard asserts a MinGW staging capability the script has never had.
This blocks the `x86_64-pc-windows-gnu` lane, is independent of the four fixes
above, and is left open deliberately rather than papered over.

`check-bootstrap-portability.shs` is not in the enforced `push`-tier rows of
`config/check/must_check_gates.sdn`, so this red does not gate pushes.
