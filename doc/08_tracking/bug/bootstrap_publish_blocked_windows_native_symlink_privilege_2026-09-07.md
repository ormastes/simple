# Bootstrap Publish Blocked on Windows: Native Symlink Requires SeCreateSymbolicLinkPrivilege
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

**Status:** OPEN — environmental, not a code defect. Needs a decision from the
user; nothing here should be changed without one.
**Severity:** Blocking — phase-1 publish cannot complete on this Windows host
(and, by the same mechanism, presumably any Windows host whose session lacks
the privilege).
**Affected file:** `scripts/check/lib/bootstrap-stage3/authority.shs:2158-2169`
(`bootstrap_stage3_create_compatibility_link`), called from
`bootstrap_stage3_publish_compatibility_pointer` (`authority.shs:2108-2156`),
called from `bootstrap_stage3_publish_seed_generation`
(`authority.shs:1972-1975`) and from `bootstrap_stage3_recover_seed_transaction`
(`authority.shs:2044-2047`).
**Host:** Windows 10 / Git Bash / MSYS, `x86_64-pc-windows-gnu`, user `yoon`
(non-elevated session).
**Path:** `bug` track.

## Symptom

After the directory-mode fix in the sibling record
(`bootstrap_publish_blocked_windows_dir_mode_assert_2026-09-07.md`), the real
lane (`sh scripts/bootstrap/run-phase1-local.shs`) got all the way through
`prepare` and into `publish`, then failed with:

```
ln: failed to create symbolic link '/c/Users/User/dev/simple/src/compiler_rust/target/.bootstrap-link.129054': Operation not permitted
error: could not commit immutable Rust authority generation
```

## Root cause

`bootstrap_stage3_create_compatibility_link` forces a real native Windows
symlink:

```sh
MSYS="${MSYS:+${MSYS} }winsymlinks:nativestrict" \
    ln -s "$bootstrap_stage3_link_target" \
        "$bootstrap_stage3_link_path" || return 1
```

`winsymlinks:nativestrict` requires the process token to hold
`SeCreateSymbolicLinkPrivilege` and fails outright (no junction/shortcut
fallback) rather than degrading. This account's session does not have it.
Confirmed independently by both the assistant and the coordinator:
`MSYS=winsymlinks:nativestrict ln -s target link` → `Operation not permitted`,
rc=1, run directly in this shell. Granting the privilege (Developer Mode, or
elevation) requires a **fresh logon** to take effect for an already-running
session — this is the same class of limitation `bootstrap-windows.sh`
documents for git-checked-out symlinks (see its `materialize-symlinks-windows.shs`
call and comment about `SeCreateSymbolicLinkPrivilege`), but **that script
does not cover this case**: it fixes symlinks materialized at *checkout* time;
this symlink (`src/compiler_rust/target/.bootstrap-link.$$` renamed onto
`src/compiler_rust/target/bootstrap`) is created **live during publish**, so
there is nothing for it to materialize beforehand.

**Plainly: phase-1 publish cannot complete on this Windows host without this
privilege.**

## Recovery-marker state (as left, not touched further)

Two partial-transaction markers are on disk from the failed publish attempt:
- `src/compiler_rust/target/bootstrap.current.env.transaction`
- `src/compiler_rust/target/bootstrap.migration.env`

Read `bootstrap_authority_recover_or_refuse` (`bootstrap-authority-wiring.shs:83-95`)
and `bootstrap_stage3_recover_seed_transaction` (`authority.shs:2002-2060`)
rather than guessing: on the **next** `--full-bootstrap` run (this
transaction file existing routes it there; `run-phase1-local.shs` always
passes `--full-bootstrap`), recovery is attempted automatically and will
correctly re-validate the already-published generation (hash and stamp both
check out). **But recovery itself calls `bootstrap_stage3_publish_compatibility_pointer`
again** (line 2044-2047) — i.e. it will hit the identical `ln -s`
`SeCreateSymbolicLinkPrivilege` failure and refuse again. The markers are
self-consistent and not corrupting anything further, but **will not clear
themselves** without either the privilege or a code change; this is not a
"just rerun it" situation.

Other state left in place, also not touched:
- New complete, valid generation:
  `src/compiler_rust/target/bootstrap.generations/8efab6a0e4181b644202eb1225dfbc2bf257b2dcf7e088956253f8a7abb5734d-7512a46651af05295a7a2c1a1e20ada03b5413aa788229b6f29781a1d64f1b5b/`
  (all 5 tuple files + valid `.inputs.sha256` stamp).
- `src/compiler_rust/target/bootstrap.generations/legacy-fdb94778034eb093cbfdcf383b45475f7ec1f9c0ccb466889bff35be51a0c91a/`
  — the **previous hand-rolled `cargo build` artifact** (see the sibling
  provenance finding: sha256 `2760b005...`, 34,235,119 bytes, links=1,
  did NOT match the authority-published copy), migrated here intact by
  `bootstrap_stage3_publish_compatibility_pointer`'s legacy-quarantine step
  (authority.shs:2123-2141) when it found a real (non-symlink) directory at
  the target path. **Not deleted; do not delete it or recreate/restore
  `src/compiler_rust/target/bootstrap` yourself** — another lane may still be
  reading from it.
- A fresh stale lock at `build/.simple-bootstrap-locks/.output-e9939c81....lock`,
  owner_pid=129054 (confirmed dead). Should self-reclaim on the next
  `portable_lock_acquire`, same as the two prior stale locks in this session.

## Consequence: `src/compiler_rust/target/bootstrap` no longer exists

The migration above means that path is currently **absent** (not a symlink,
not a directory — nothing). Two other places read it directly:
- `bin/simple.cmd:8-11` — sets `BOOTSTRAP_BIN` from
  `%REPO_ROOT%\src\compiler_rust\target\bootstrap\simple.exe` if present
  (falls through silently to `CURRENT_DRIVER_BIN`/other fallbacks if absent —
  not a hard failure, but a lost fast-path).
- `scripts/setup/deploy-local-temp-mcp.shs:89` — default `seed=` value is
  `"${repo_root}/src/compiler_rust/target/bootstrap/simple${exe_suffix}"`
  (used unless `--seed PATH` is passed explicitly).

## Candidate resolutions (not chosen — for the user)

1. **Grant the privilege.** Enable Windows Developer Mode (or run elevated)
   and obtain a **fresh logon** so the new token actually carries
   `SeCreateSymbolicLinkPrivilege`. No code change; publish should then
   complete and self-recover the pending transaction on the next run.
2. **Windows junction fallback** in `bootstrap_stage3_create_compatibility_link`.
   Not a drop-in: junctions are directory-only reparse points and behave
   differently under `rename()` than a symlink does, which changes the
   atomicity contract `bootstrap_stage3_publish_compatibility_pointer` relies
   on (`perl -e 'rename($ARGV[0], $ARGV[1])'` at authority.shs:2152-2154).
   Needs deliberate design, not a tolerance mirror.
3. **Keep Windows publish unsupported** and document it plainly (phase 1
   remains buildable/testable on Windows via the immutable generation
   directory; only the mutable compatibility pointer at
   `src/compiler_rust/target/bootstrap` would be unavailable there).


## 2026-09-24: elevation is not obtainable from an agent session (new evidence)

Re-hit on DESKTOP-5A4V03J while running the documented local phase-1 entry.
Everything up to the publish now works: the GNU lane builds the Rust seed,
native-all, runtime-nolto and compiler-backfill cleanly, and the run reaches
the authority commit before failing. The failing call is the perl helper, not
`ln`:

```
scripts/check/lib/bootstrap-authority-generation-publish.pl:46
  symlink("$generation_leaf/$final_leaf", $compat_tmp) or die "create compatibility: $!\n"
```

invoked from `bootstrap_stage3_publish_seed_generation`
(`bootstrap-stage3/authority.shs:3727-3733`) under
`MSYS="...winsymlinks:nativestrict"`. Reproduced in isolation, same message:

```
$ cd src/compiler_rust/target
$ MSYS=winsymlinks:nativestrict perl -e 'symlink("bootstrap",".x") or die "create compatibility: $!\n"'
create compatibility: Operation not permitted
$ perl -e 'symlink("bootstrap",".x") or die' && echo ok    # no nativestrict
ok
```

So the guard is behaving exactly as designed; only the privilege is missing.

**Why the "or run elevated" half of resolution 1 does not work from here.**
`scripts/setup/windows-symlink-privilege.shs run -- ...` (added 2026-09-24)
re-launches the command through `Start-Process -Verb RunAs`. It was attempted
THREE times in one session and every attempt returned:

```
This command cannot be run due to the error: The operation was canceled by the user.
```

with no elevated process started and no log written. The token state explains
why the privilege is absent but not why consent never arrives:

```
$ whoami /priv      # no SeCreateSymbolicLinkPrivilege at all -- not even Disabled
$ whoami /groups
BUILTIN\Administrators   Alias   S-1-5-32-544   Group used for deny only
Mandatory Label\Medium Mandatory Level
```

That is an ordinary UAC-filtered admin token, so the ACCOUNT very likely holds
the right through Administrators; this PROCESS's token does not. Developer Mode
is off (`HKLM\...\AppModelUnlock\AllowDevelopmentWithoutDevLicense` absent).

The operative new fact is narrower and worth recording separately from the
privilege question: **a UAC consent dialog raised from an agent/automation
session on this host is not reachable and resolves as cancelled.** Any
remedy whose last step is "accept a prompt" therefore cannot be driven from a
session like this one, however the privilege is otherwise arranged.

Unblocking still requires a human at the machine, one of:
- open Git Bash elevated (right-click -> Run as administrator), then
  `cd /c/Users/User/dev/simple && SIMPLE_WINDOWS_ABI=gnu sh scripts/bootstrap/run-phase1-local.shs`
  -- no UAC dialog is raised mid-run, so this is the path that works; or
- enable Developer Mode / grant the right in local policy, then obtain a FRESH
  LOGON so a new token carries it. (Whether Developer Mode alone suffices for
  MSYS `nativestrict` was NOT verified here and should not be assumed -- MSYS
  must pass SYMBOLIC_LINK_FLAG_ALLOW_UNPRIVILEGED_CREATE for that to help.)

`SIMPLE_WINDOWS_ABI=gnu` is required on this host for an unrelated reason: it
has no Visual Studio and no Windows SDK, so the hardcoded MSVC default cannot
build `ring`. See
`bootstrap_windows_abi_default_ignores_host_triple_2026-09-24.md`.

Diagnosis helper for future sessions (no elevation needed, changes nothing):
`sh scripts/setup/windows-symlink-privilege.shs check`.
