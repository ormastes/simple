# The Stage-3 materialized consumer retains an open handle per walked entry, so a post-build tree either trips bound.entries or gets OOM-killed

Filed: 2026-09-25
Host: DESKTOP-5A4V03J (Windows 11, 15.7 GB RAM, Git Bash / MSYS2, `x86_64-pc-windows-gnu`)
Severity: Blocking on a memory-constrained host. There is no setting that fixes
it — the two available outcomes are a clean refusal or a kill.

## What happens

`stage3-materialized-consumer` walks HEAD plus the physical working tree and
opens every entry, retaining the handle for the whole walk
(`scripts/check/lib/bootstrap-stage3/authority.shs`, the `held.Add(Open(...))`
calls in the walk). Entry count is bounded by `MaxEntries`
(`BOOTSTRAP_STAGE3_GIT_MAX_ENTRIES`, default 400,000) but the RETAINED HANDLES
are not bounded independently.

Measured on this host, after a completed bootstrap:

| | entries |
|---|---|
| tracked (HEAD) | 138,273 |
| physical (working tree) | 355,042 |
| **total the walk must cover** | **~493,000** |

That exceeds the 400,000 ceiling, so the audit refuses with `bound.entries`
before any pure-Simple stage starts.

Raising the ceiling does not help — it makes things worse:

- `MaxEntries` was raised to 1,000,000 and phase 1 re-run. The walk then
  proceeded past 400k and the OS **killed the whole bootstrap for low memory**
  (two runs, both killed mid-audit, ~5 GB free at launch). The change was
  reverted.
- A clean fail-closed `bound.entries` is strictly more useful than an OOM kill,
  which leaves orphaned children holding locks (see "Knock-on" below).

So on a tree this size the audit cannot complete, and the ceiling is the only
thing preventing a kill.

## Why the default is calibrated wrong for a real host

The pre-existing comment recorded its own measurement as "137461 + 176143
entries at the admitted source state" — i.e. a CLEAN checkout. The physical half
more than doubles the moment the host builds anything, because these appear:

| path | entries |
|---|---|
| `build/c/` (cargo content-addressed cache) | 119,089 |
| `src/compiler_rust/target/` | 38,564 |
| `.simple/` | 14,255 |

A budget measured before the first build is therefore exceeded by every host
immediately after its first build — which is exactly when this consumer next
runs. The ceiling is not wrong as a resource bound; it is wrong as a
*prediction* of how many entries a working host has.

## Workaround (what unblocked this host)

Delete the regenerable cargo cache only — `build/c/` — keeping the tracked
content under `build/review/`:

```
$ git ls-files build | wc -l          # 61, ALL under build/review/
$ chmod -R u+w build/c && rm -rf build/c
$ find . -mindepth 1 | wc -l          # 236,142 physical
                                      # + 138,273 tracked = 374,415 < 400,000
```

The published seed generation is NOT in `build/` — it lives in
`src/compiler_rust/target/bootstrap.generations/` with the
`bootstrap.current.env` marker — so it survives this deletion, verified by
running the seed before and after (`Simple Language v1.0.0-beta.14` both times).

This is a workaround with a short half-life: the next build regenerates
`build/c/` and the tree goes back over the ceiling.

## Proposed fix (owner's call; nothing changed here beyond documentation)

1. **Bound the retained handles, not just the entry count.** Release handles as
   the walk proceeds, or hold them in a windowed set, so a large tree costs time
   rather than memory. This is the change that makes raising `MaxEntries` safe,
   and it should land BEFORE any raise.
2. **Exclude git-ignored cache subtrees from the physical walk.** `build/c/` and
   friends cannot carry smuggled SOURCE, which is what the audit binds. This
   would cut the walk by a third here and make the count stable across builds.
   Needs care: "ignored" must not become a hole for content the audit does rely
   on.
3. **Say which limit was hit and what it means.** `bound.entries` does not
   mention that deleting a regenerable cache is the remedy, and the OOM path
   gives no repo-level message at all.

Recommend 1, then 2. Do **not** raise `MaxEntries` alone — that was tried here
and converted a clear error into a kill.

## Knock-on: an OOM kill leaves the bootstrap wedged

When the OS killed the run, the wrapper died but its child survived:

```
$ cat /proc/154911/cmdline
/bin/sh .../bootstrap-from-scratch.sh --full-bootstrap --stop-after-stage2 ...
```

still holding `.simple/storage/build/.simple-bootstrap-locks/.output-<hash>.lock`.
The next run then failed with:

```
error: timed out waiting for bootstrap output ownership: .../.simple/storage/build/bootstrap
```

The lock's PID-reuse guard behaved correctly — the owner really was alive — so
nothing reclaimed it; it needed `kill -TERM -<pgid>` by hand. Two things worth
considering separately from the memory issue: the ownership-timeout message
should mention that an orphaned holder is the likely cause and name the lock
file, and the bootstrap could reap its own process group when the top-level
wrapper dies.

## Related

- `quarantined_generation_exceeds_max_path_blocks_preflight_2026-09-25.md` —
  another artifact that disables later runs until removed by hand.
- `bootstrap_publish_blocked_windows_native_symlink_privilege_2026-09-07.md`

## The orphan cascade: why retrying after an OOM gets progressively worse

Measured across five consecutive OOM kills on 2026-09-25. This is the most
practically important finding here, and it is easy to misread as "the host is
simply too small".

When the OS kills the bootstrap for low memory, it kills the WRAPPER. The heavy
child survives:

```
$ powershell "Get-CimInstance Win32_Process -Filter \"Name='simple.exe'\" | ..."
ProcessId : 15220
MB        : 3810
CommandLine: .../stage2-runtime-authority/simple.exe native-build ... --low-memory
             --mode dynload --entry src/app/cli/bootstrap_main.spl ...
```

Its parent is gone, so its output can never be admitted — it is pure waste — but
it keeps its working set. Reaping one such orphan took free memory from
**0.5 GB to 9.2 GB**; a later one was holding **8.8 GB**, another **4.4 GB**.

The consequence is a cascade: each retry starts with less memory than the
previous one, dies sooner, and leaves another orphan. Four retries in a row were
attributed to "this box has ~5 GB free" when the box actually had ~9 GB free and
the missing memory was held by the wreckage of earlier attempts.

**Operational rule for anyone hitting this: before re-running, reap the orphan.**

```
powershell -NoProfile -Command "Get-CimInstance Win32_Process -Filter \"Name='simple.exe'\" | Where-Object {$_.CommandLine -like '*native-build*'} | ForEach-Object { Stop-Process -Id $_.ProcessId -Force }"
```

Do NOT blanket-kill `simple.exe`: the deployed MCP servers are also `simple.exe`
(15-21 MB each, command lines containing `run .../src/app/mcp/main.spl` or
`simple_lsp_mcp`/`t32_mcp`). Filter on `native-build`.

Two fixes worth considering, independent of the memory bound itself:

1. **Reap the process group when the top-level wrapper dies.** The bootstrap
   already runs children under a process group
   (`run-process-group-timeout.shs`, `portable-session-exec.pl`); an
   OOM-killed wrapper should not leave a multi-GB compiler running.
2. **Say so in the failure.** The next run reports
   `FAIL — 1 check(s), stage stage2 failed (exit 127) with NO diagnostic text in
   any of 9 log(s)`, which describes the symptom of a killed child and names
   none of it. An exit-127-with-no-diagnostics case should at least suggest
   checking for a surviving child and for memory pressure.

## The actual memory requirement, measured

Sampled at 50-second intervals during a Stage 2 `native-build` (2 threads,
`--low-memory`, `--mode dynload`):

| elapsed | RSS | free |
|---|---|---|
| 0:00 | 34 MB | 5.7 GB |
| 1:00 | 1,712 MB | 4.1 GB |
| 2:00 | 3,306 MB | 2.6 GB |
| 3:00 | 4,824 MB | 1.4 GB |
| 4:00 | 6,441 MB | 0.4 GB |
| 4:20 | 7,625 MB | 0.5 GB |
| later | 8,830 MB | (killed) |

It was still climbing at 8.8 GB. **Halving the thread count did not lower the
peak** — a 4-thread run was killed at 3.8 GB only because it died earlier, while
the 2-thread run reached 8.8 GB. So this is the compiler's whole-program working
set for `src/compiler` + `src/app` + `src/lib` in dynload mode, not thread
parallelism, and `SIMPLE_NATIVE_BUILD_THREADS` is not a lever for it.

A host needs on the order of **9-10 GB free** for Stage 2, over and above
whatever else it is running. That number belongs in the Windows bootstrap
prerequisites; the disk-space preflight checks 20 GiB of disk and nothing checks
available memory, so the failure arrives as an opaque kill rather than as a
stated requirement. A memory preflight comparable to `PASS —
disk-space(72GiB>=20)` would have turned five hours of retries into one clear
refusal.
