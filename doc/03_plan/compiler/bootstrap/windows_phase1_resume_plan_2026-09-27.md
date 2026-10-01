# Windows bootstrap phase 1 — what is done, what is left

Host: DESKTOP-5A4V03J (Windows 11, Git Bash/MSYS2, `x86_64-pc-windows-gnu`,
clang/LLVM 23.1.0 at `C:\llvm\install`, 15.7 GiB RAM, 30.1 GiB commit limit).
Written 2026-09-27 at a machine restart, so the session's scratchpad launcher
scripts are reproduced below before they are wiped.

## Bottom line

**Phase 1 is NOT complete.** No pure-Simple `simple.exe` has ever been produced
on this host, so `simple test` GREEN does not prove self-hosted here. Everything
else in the surrounding goal is done and landed.

## Done

| item | evidence |
|---|---|
| LLVM/clang 23.1 toolchain setup | PR #1515 |
| Bootstrap-script environment setup, host config wiring | PR #1592 |
| MCP servers built, deployed locally, Claude/Codex/Kimi configs | landed |
| spipe skill work; stitch MCP removed from all three CLIs | landed |
| gh sync, main rebase, spipe submodule sync | landed |
| Antivirus-exclusion script updated and run | landed |
| MAX_PATH / quarantine, Windows ABI, symlink-privilege findings | PRs #1618, #1646 |
| 6 phase-1 defects fixed | PRs #1735, #1769 |
| 7th defect (fingerprint cc-probe) | fixed on `main` by another session — see below |

### How far phase 1 now gets

| stage | state |
|---|---|
| fingerprint (pre) | PASS |
| Rust seed + runtime rebuild | PASS (~19–27 min) |
| **authority publish** | **PASS** — first success after defect 7 below |
| preflight (5 checks) | PASS (~20–26 min) |
| tool-authority bind | PASS |
| git-state / source-inputs audits | PASS |
| Stage 2 admission | PASS |
| Stage 2 compile (901 modules) | best `[850/901]`, then OOM |
| Stage 2 native link | reached once; LLD crashed (fix landed, UNVERIFIED) |
| Stage 3 / Stage 4 | never reached |

### The seven defects fixed (do not re-investigate)

1. `env` transiently fails to exec under memory pressure (`shell-status=125`),
   aborting the fingerprint stage. Retry in
   `bootstrap_stage3_native_metadata_probe`, status-125 only (2/2 failures under
   load vs 0/70 at rest).
2. The Stage 4 tool-authority bind aborted on the same class, with a message
   naming none of its ~20 failure sites. Retry + xtrace on the final attempt.
   Confirmed working: `bootstrap tool authority bound on attempt 2`.
3. The "Rust inputs changed" refusal overwrote the `pre` fingerprint details
   with the `post` ones, destroying the evidence — it could say *that* an input
   changed, never *which*. Details kept per phase; the refusal diffs categories.
   **This diagnostic is what found defect 7.**
4. GNU ld cannot consume `\\?\` verbatim cache-root paths — each object was
   truncated to its last component (`cannot find \\_main_stub.o`).
   `respell_args_for_external_tool` at both link spawn points.
5. The windows-gnu lane never selected a linker, so clang's mingw driver used
   whatever bare `ld` PATH offered. `-fuse-ld=lld` now emitted with the
   `--target=`, before any `SIMPLE_LINKER` override so an explicit request wins.
6. `resolve_defined_suffix_alias` aliased libc/winsock names to same-named
   Simple functions: winsock `select` resolved to
   `lib__nogc_async_mut__async__combinators__select` and a global `select` was
   emitted against ws2_32's. **Had it linked, every socket `select()` would have
   jumped into an async combinator, silently** — the LLD crash prevented a
   miscompile. Fixed by `PLATFORM_C_SYMBOLS`.
7. **Uncommitted.** The seed fingerprint recorded `cc-version-status` from a bare
   `env -i <clang> --version` with no retry, so a transient 125 became part of
   the seed's *content identity*. Pre and post observations disagreed and every
   publish was refused with `category_native_tools_sha256` differing — the two
   hashes (`e77382..`/`e4e31d8b..`) alternated in **both directions** across runs
   with no file changed. Fixed by a 125-only retry loop in
   `scripts/check/lib/bootstrap-stage3/authority.shs` (~line 5449,
   `bootstrap_stage3_seed_cc_*`). The next run published on its first attempt.

   Two earlier explanations for this same symptom were **wrong**, recorded so
   they are not retried: `SIMPLE_LINKER` set in the environment, and reordering
   PATH so LLVM precedes mingw-winlibs. Both were reverted; the probe was the
   cause all along.

## Left to do

### 0. Nothing to land for defect 7 — `main` already fixes it, better

Checked 2026-09-27 after the restart: `origin/main` now routes that probe through
`bootstrap_stage3_native_metadata_probe cc-fingerprint-version` (the retrying
probe hardened by fix 1 above), fails closed with `|| exit 1`, and records
`cc-version-status=0` as a **constant**. The transient status can no longer enter
the fingerprint at all — strictly better than the local retry loop, which was
therefore discarded rather than landed as a worse duplicate.

**Do not push this working tree wholesale.** Measured at the restart it is
*behind* `origin/main`: 35 insertions / 67 deletions in
`scripts/check/lib/bootstrap-stage3/authority.shs` and ~152 lines in
`src/compiler_rust/compiler/src/pipeline/native_project/`, because other sessions
landed there after PRs #1735/#1769 merged. Rebase onto `origin/main` before any
push from it; a wholesale push would revert their work.

### 1. Stage 2 memory exhaustion

`doc/08_tracking/bug/stage2_memory_grows_monotonically_with_module_count_2026-09-26.md`

The module it dies on tracks commit headroom, so the requirement is unbounded:

| free physical at Stage 2 start | died at |
|---|---|
| ~9 GiB | `[850/901]` |
| 4.2 GiB | `[650/901]` |
| ~4–5 GiB under load | `[400/901]` |

Preflight consumes the headroom itself: 7.7 GiB free *before* a run was 4.2 GiB
by the time Stage 2 started, so "run it when the machine is quiet" does not help.

**Step 1 — human, needs Administrator.** Agent elevation failed:
`Start-Process -Verb RunAs` could not raise a UAC prompt from the session.

```powershell
$cs = Get-CimInstance Win32_ComputerSystem
Set-CimInstance -InputObject $cs -Property @{AutomaticManagedPagefile=$false}
New-CimInstance -ClassName Win32_PageFileSetting -Property @{
  Name='C:\pagefile.sys'; InitialSize=20480; MaximumSize=28672 }
```

Commit limit 30.1 GiB → ~44 GiB, leaving the disk above the 20 GiB preflight
minimum. Reboot to apply. This **moves** the wall; 901 modules only grows.

**Step 2 — the real fix.** Capture a per-module RSS curve for the Stage 2
process. A straight line implicates per-module retention; a step function
implicates one phase. No curve has been captured yet: this is a measurement, not
a guess at the culprit.

**Do not raise `--jobs` before step 1.** It is one knob for both
`CARGO_BUILD_JOBS` and the Stage 2 native build jobs (CLI overrides
`SIMPLE_NATIVE_BUILD_THREADS`), so it speeds the seed rebuild and multiplies
Stage 2's concurrent working sets at the same time.

### 2. Verify the LLD crash fix — never yet observed

`doc/08_tracking/bug/lld_231_crashes_on_generated_compat_alias_archive_2026-09-27.md`

With `PLATFORM_C_SYMBOLS` in place the `select` alias should not be generated and
the link should proceed, but **no run has shown this**: both candidates were
stopped or restarted first. Verify from the Stage 2 log
(`.simple/storage/build/bootstrap/logs/x86_64-pc-windows-gnu/stage2-native-build.log`):

- no `Compatibility alias preview: select`
- the link command contains `-fuse-ld=lld`
- no `checkAndSetWeakAlias` stack dump

The LLD-side defect is real and unreported upstream — a linker must diagnose a
symbol conflict, not segfault. A reduced case is still to be built. Reproducer
artifacts were kept under
`.simple/storage/build/bootstrap/stage3/x86_64-pc-windows-gnu/native-objects-*/`
(`_compat_alias_0.s`, `.obj`, `_compat_aliases.lib`); those sit under
`build/`-ignored paths and will not survive a clean.

### 3. Then Stage 3 / Stage 4

Never reached. No estimate is honest yet.

## Operational traps — each one cost a run

- **Never edit a tracked file while a full bootstrap runs.** The publish-time
  fingerprint compares pre/post and refuses; a markdown edit at 15:20 aborted a
  27-minute rebuild. (That a doc counts as a "Rust seed input" looks over-broad
  and may deserve its own record — one observation so far.)
- **Never reorder PATH so LLVM precedes mingw-winlibs.** See defect 7.
- **`SIMPLE_LINKER` cannot be set from outside.** The env scrub drops every
  `SIMPLE_*` except three session vars, so it never reaches the Stage 2
  compiler, and it perturbs the same fingerprint.
- **Reap orphans before judging memory.** A killed run can leave a multi-GiB
  orphan; reaping one took free memory 0.5 → 9.2 GiB.
- **Run pre-push gates on an idle machine.** `push-tree-size` overran its 10 s
  budget (11.7 s) during a bootstrap and refused the push with verdict UNKNOWN.
- **Do not build in a worktree or clone.** A worktree's `.git` is a file (seed
  fingerprinting fails), a longer path crosses MAX_PATH on a *normal* generation
  (250/260 here — zero margin at +10 chars), and a clone's git-lfs smudge
  rewrites `src/compiler_rust` mid-build.

## How to run it

Scheduled task `SimplePhase1Bootstrap`; start with
`schtasks /run /tn SimplePhase1Bootstrap` from PowerShell (MSYS mangles `/run`).
Its action is `C:\Users\User\p1launch.cmd`, which exists only to give bash **no
inherited console** — a task whose action is bash directly inherits the console
of whatever ran `schtasks`, and when that console closes bash dies with Task
Scheduler `Last Result: -1073741510` (0xC000013A `STATUS_CONTROL_C_EXIT`):

```bat
@echo off
powershell.exe -NoProfile -WindowStyle Hidden -Command "Start-Process -FilePath 'C:\Users\User\scoop\apps\git\2.55.0.5\usr\bin\bash.exe' -ArgumentList '<path>\phase1_main.sh' -WindowStyle Hidden"
```

The job script (was in the session scratchpad; point LOG/STATUS somewhere
durable):

```sh
#!/bin/sh
set -u
cd /c/Users/User/dev/simple || exit 2
RUSTUP_HOME='C:\Users\User\scoop\persist\rustup\.rustup'
CARGO_HOME='C:\Users\User\scoop\persist\rustup\.cargo'
export RUSTUP_HOME CARGO_HOME
# Every PATH component must exist AND already be canonical:
# bootstrap_stage3_tool_authority_snapshot does `cd -- "$dir" && pwd -P` per
# component and returns 1 unless the result is byte-identical. Scoop's
# `current` junctions are fatal here -- they resolve to persist/, versioned
# dirs, even /cmd -- surfacing only as "could not bind bootstrap tool
# authority". The inherited PATH is deliberately NOT appended: same junctions.
# Order matters: mingw-winlibs BEFORE /c/llvm/install/bin (see defect 7).
PATH="/usr/bin:/mingw64/bin:/c/Users/User/scoop/persist/rustup/.cargo/bin:/c/Users/User/scoop/apps/mingw-winlibs/16.2.0-14.0.0-r1/bin:/c/Users/User/scoop/apps/nodejs/26.8.1:/cmd:/c/Users/User/scoop/shims:/c/llvm/install/bin:/c/Windows/system32:/c/Windows:/c/Windows/System32/WindowsPowerShell/v1.0"
export PATH
LOG=<durable>/phase1-main.log
STATUS=<durable>/phase1-main.status
: > "$STATUS"
exec > "$LOG" 2>&1
echo "=== phase 1 start $(date '+%Y-%m-%d %H:%M:%S') ==="
command -v rustup >/dev/null 2>&1 || { echo "FATAL: rustup not on PATH"; printf '127' > "$STATUS"; exit 127; }
SIMPLE_WINDOWS_ABI=gnu SIMPLE_NATIVE_LOW_MEMORY=1 SIMPLE_NATIVE_BUILD_THREADS=1 \
    sh scripts/bootstrap/run-phase1-local.shs
rc=$?
echo "=== phase 1 end $(date '+%Y-%m-%d %H:%M:%S') rc=$rc ==="
printf '%s' "$rc" > "$STATUS"
```

`SIMPLE_WINDOWS_ABI=gnu` is required here: the MSVC lane is unsatisfiable (no
Visual Studio/Windows SDK, so `ring` fails on `assert.h`) — see
`doc/08_tracking/bug/bootstrap_windows_abi_default_ignores_host_triple_2026-09-24.md`.

## Order of work on resume

1. Port and land defect 7 onto `origin/main` content.
2. Apply the pagefile change as Administrator; reboot.
3. Run phase 1; verify item 2 from the Stage 2 log before assuming it is fixed.
4. If Stage 2 still OOMs, capture the RSS curve — do not just raise limits again.
5. Reconcile the working tree against `origin/main` before any push from it.

## Note on this file's location

`doc/03_plan/compiler/bootstrap/` held 17 files against a fan-out baseline of 15
before this one was added, i.e. it was already over baseline from other sessions'
work. This file makes that 18. The fan-out guard is advisory (extended CI tier),
not blocking at push. Correct placement was chosen over gate-gaming; the
directory needs a split, which is a separate change.
