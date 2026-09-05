# Bootstrap builds from the LIVE shared working copy, so a parallel session's half-second of conflict markers aborts a 2-hour lane

**Status:** OPEN
**Filed:** 2026-09-05
**Host:** aarch64-unknown-linux-gnu
**Severity:** medium-high — costs a full bootstrap lane, and the failure it
prints is a *plausible-looking source defect*, which is how it steals
investigation time rather than merely wasting wall clock.

## Symptom

A Stage-3 bootstrap launched at 12:03:40 died 2 minutes later:

```
stage: stage2
exit:  1
  diagnosis: 1 diagnostic line(s) found. First 5:
    | Build failed: failed to parse /home/yoon/dev/simple/src/lib/nogc_sync_mut/io_runtime.spl
      at 64:1 during discovery: Unexpected token: expected expression, found TripleLt
PASS — 1 check(s), stage stage2 failed (exit 1) and said why
  warning: stage2 native-build failed (exit 1); Stage 3/full CLI unavailable
```

`TripleLt` is `<<<` — the lexer's rendering of a **conflict marker**.

## The file was never broken in any commit

| probe | result |
|---|---|
| `git status --short src/lib/nogc_sync_mut/io_runtime.spl` | clean |
| `md5sum` working copy vs `git show HEAD:<path>` | identical (`3ae61cc8…`) |
| `grep -n '<<<' <path>` | no hits |
| last commit touching it | `c8afd8a631c`, **2026-09-04 14:04** — 22 hours earlier |
| **file mtime** | **2026-09-05 12:04:31** |

The mtime is the whole story: it is **51 seconds after the run started**. For
part of that minute the file on disk carried conflict markers, and a parallel
session restored it to its HEAD content at 12:04:31. Nothing was ever committed
broken; the bootstrap simply read the tree during another session's write.

## Why no existing guard catches this

Every conflict-marker guard in the repo is **range-based on committed content**
— `check-no-conflict-markers-push.shs` reads `git show <rev>:<path>` over
`main@origin..@-`, by design, because
`conflict_markers_reported_at_origin_were_working_copy_only_2026-08-11.md`
established that working-copy markers are not origin's problem. That reasoning
is right for *push* gating and wrong for *building*: the bootstrap does not
build a commit, it builds `$PWD`. So the marker guards are structurally unable
to see this, and the bootstrap has no pre-flight of its own.

The nearest existing record,
`full_bootstrap_blocked_rust_inputs_changed_concurrent_sessions_2026-08-15.md`,
is a **different** failure: there the wrapper's own guard *did* fire
("Rust inputs changed during full bootstrap; refusing to publish a stale seed").
That guard covers `src/compiler_rust/**` only. There is no equivalent on the
`.spl` side, so a `src/lib/**` edit races silently.

Note also that the diagnosis gate reported `PASS — 1 check(s), stage stage2
failed (exit 1) and said why`. It is satisfied by the *presence* of a
diagnostic, and cannot tell a real source defect from a torn read. That is
correct behaviour for that gate and exactly why it gives false comfort here.

## Second mechanism, same root: state the run depends on keeps moving

The relaunch 4 minutes later died instantly with a different policy error:

```
bootstrap-policy-error: planner-admission-v2-unbound
bootstrap-policy-error: malformed-or-untrusted-planner-admission-v2
```

The `--bootstrap-receipt` still validated (`receipt-valid target=//bootstrap:stage3
reason=seed-missing`); it is the **planner admission** that is bound to git
state, and HEAD had moved between the 11:20 validation and the 12:07 launch.
In a repo where several sessions commit continuously, an admission is only
valid for as long as nobody commits — and
`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs` requires a
*verified Stage-2 compiler* as parent authority ("never the Rust seed"), so
regenerating it is not cheap either. The practical consequence is a narrow
produce-then-launch window that no tooling currently enforces or documents.

Worse, this extends into the run: `bootstrap-from-scratch.sh` re-binds git
HEAD/dirty state at the end (`error: could not re-bind Stage 3 git HEAD/dirty
state`, `error: bootstrap tool authority changed during Stage 2/3`), so a commit
landing *during* a two-hour Stage-3 run can invalidate it after the work is done.

## Three distinct failures in 70 minutes, same root

Retrying the Stage-3 lane produced a different concurrency failure each time.
They are worth listing together because each has its own error string, and any
one of them read alone looks like a defect in the thing it names:

| time | error | what actually happened |
|---|---|---|
| 12:03 | `failed to parse ... at 64:1 ... found TripleLt` | conflict markers on disk for part of a minute |
| 12:44 | `bootstrap-admission-error: parent-stage2-sanity-candidate-mismatch` | the Stage-2 binary was being rewritten while the admission producer hashed it; its receipts were from 06:59, the binary from 12:43, and moments later the binary was gone |
| 12:58 | `error: refused incomplete Stage 2 admission provenance` | two source files appeared mid-build |

The third is the sharpest, because the guard that caught it is *correct* and its
evidence is exact. `bootstrap-from-scratch.sh:2699-2703` refuses when the source
snapshot taken before Stage 2 differs from the one taken after. Decoding the two
`file-hex` rows that differ:

```
src/compiler/10.frontend/structural_adapter/core_lexer_adapter.spl   created 13:04:41
src/compiler/10.frontend/structural_adapter/__init__.spl             created 13:06:06
```

The build ran 12:57:56 - 13:11:41. Another session created a new module inside
that window. Tool authority was byte-identical and both sanity and receiver
evidence said `status=pass`; the *only* thing wrong was that the tree moved.

This is the measurement that settles the design question: a bootstrap that reads
`$PWD` cannot complete on a machine where other sessions are actively developing,
because the window it needs (~14 minutes for Stage 2, ~2 hours for Stage 3)
is longer than the interval between their edits. Fix 3 below is therefore not a
nice-to-have; retrying is not a workaround, it is a coin flip that gets worse the
longer the stage runs.

## Impact

- A Stage-3 lane (~1h45m to the point of interest) aborted at 2 minutes.
- The printed cause names a real, load-bearing stdlib file and a real line
  number. Taken at face value it reads as a parser or source regression, and
  the natural next step — inspecting the file — shows nothing wrong, because by
  then it has been repaired. That is a false trail an investigation can spend
  a long time on.

## Fixes, cheapest first

1. **Pre-flight in the bootstrap wrapper** (smallest useful change): before
   Stage 1, refuse to start when any tracked `*.spl` under `src/` contains a
   line-initial conflict marker, with a typed reason. Cheap (one `grep -rl`),
   and it converts a two-minute mystery into an immediate, accurate message.
   A session-local version of exactly this is running in
   `stage3_chain.sh` today and is what this record recommends promoting.
2. **Classify a torn read as retryable, not as a result.** A stage failure whose
   only diagnostic is a parse error at a path that is clean in git is
   overwhelmingly a race; retry once rather than reporting a compile failure.
3. **The real fix: build from a snapshot, not from `$PWD`.** `git archive` (or a
   detached worktree, which `check-seed-builds-push.shs` already does for the
   seed — "never the shared, contested working copy") makes the whole class
   impossible, and would also stabilise the git state the admission and the
   end-of-run re-bind depend on. Larger change; the right destination.

## Cross-references

- `full_bootstrap_blocked_rust_inputs_changed_concurrent_sessions_2026-08-15.md`
  — same theme, Rust-side, guard present.
- `conflict_markers_reported_at_origin_were_working_copy_only_2026-08-11.md`
  — why the marker guards are deliberately commit-scoped.
- `stage3_worker_reaped_silently_in_hir_typecheck_2026-09-05.md` — the run this
  aborted; that investigation is unaffected, only delayed.

## UPDATE (2026-09-05, 15:11): a fourth contention mode — cross-session SIGTERM

The snapshot worktree fixed the *source* races (Stage 2 and the admission both
succeeded first try, after four consecutive failures in the shared tree). It
cannot fix process-level contention, and that is what now blocks Stage 3.

Five Stage-3 attempts died identically. `strace -f -e trace=kill,tgkill` on the
worker names the sender outright:

```
1983604 15:11:49.192746 --- SIGTERM {si_signo=SIGTERM, si_code=SI_USER,
                                     si_pid=1986862, si_uid=1000} ---
1983604 15:11:52.454450 +++ killed by SIGTERM +++
1983603 ... si_status=SIGTERM, si_utime=41723 /* 417.23 s */ ...
1983602 15:11:54.790439 exit_group(-143)
```

`si_code=SI_USER` is an explicit `kill()` from another process, and **si_pid
1986862 is not in the traced tree** (ours: 1983602 parent, 1983603 sh, 1983604
worker; its own children are 1986877-1986884, allocated *after* the kill). So
the worker is killed from outside — another session on this shared box. This
host runs several concurrent agent sessions, at least one of which
(`/tmp/claude-1000/-home-yoon-dev-simple/<other-session>/scratchpad/run_wt.sh`)
is driving its own bootstrap out of `/home/yoon/dev/simple-bs`. No repo script
carries a matching `pkill`, so the likely source is an ad-hoc `pkill -f` typed
by another session — the same foot-gun that killed this session's own shell
earlier today when a `pkill -f` pattern matched its own command line.

### Corrections this trace forced, recorded because both were reported as fact

1. **The death is at ~428 s, not 13.5 s.** The earlier figure came from reading
   the last `[BOOTSTRAP-PHASE]` line, but `phase2:parse` emits no further phase
   lines while it works, so that timestamp marks when parse *started*. Measured:
   429 s / 428 s / 427 s across three runs, and `si_utime` confirms 417 s of CPU
   in the worker — it was doing real work the whole time, not hung.
2. **`_process_kill_group` is exonerated.** With `SIMPLE_PROC_DEBUG=1` actually
   reaching the process (an earlier probe silently did not — the bootstrap
   builds the stage3 child env from an explicit list and dropped the variable,
   so its "NONE" result proved nothing), the line reads
   `kill-group pgid=1980659 term_code=1`. `term_code=1` means `pkill` matched
   nothing: the worker was already dead. It runs only on the failure path, so it
   is cleanup, not cause.

Also excluded by measurement, not argument: phase-isolated scheduling (identical
death under `--strategy=adhoc`), parse/HIR shard children (`SIMPLE_FRONTEND_CACHE=0`
⇒ both counts 0), the strategy qualifier (no `qualification.log`), a worker
`--timeout` (absent from argv; `DEFAULT_TIMEOUT_MS` is 6 h), phase-verification
budgets (1800/120/600 s), the wrapper's timeout and relay-error paths (zero
`[TIMEOUT:` / `[ERROR:` markers), and OOM — RSS watched through the death point
read 22.9 → 23.1 → 23.4 GB with **89 GB free**.

### What this means for the Stage-3 SIGSEGV hunt

The crash of interest is ~1 h 45 m into the run; no attempt has survived past
7 minutes. The blocker is no longer a compiler defect or a source race but
uncoordinated process management between sessions sharing one machine.

Options, in order of cost:
1. **Coordinate.** Ask the other session to stop broad `pkill -f`, or hold the
   box for one 2-hour window. Cheapest and unblocks immediately.
2. **Make the worker unmatchable.** A `pkill -f` matches on argv text; running
   the worker via a copied binary under a neutral name in a private session
   would dodge pattern kills, but it is a workaround that hides the coupling.
3. **Isolate properly** — a container or a second UID — which is what a shared
   build host actually wants, and the natural extension of the snapshot fix.

## Caveat on fix 3: "build from committed content" assumes the tip is buildable

`bootstrap-in-snapshot.shs` makes a build immune to concurrent edits by reading
only committed content. That is the right trade for the bootstrap, whose inputs
are committed. It is worth stating the assumption it rests on, because a
parallel session measured a live counterexample the same day:

**`spipe-docgen` does not run from committed content at all, on any spec.** The
committed `generator.spl`, `parser.spl` and `analyzer.spl` all reference an
unlanded half of a feature that exists only as uncommitted work in the main
working copy — measured at 105 insertions across four files, three of them
dirty. Resolving the first missing symbol (`spec_kw_line`) just moves the error
to the next one (`scenario_at_is_unconditional_pending` at `parser.spl:1802`),
so it reads as "one small fix away" for several rounds before the real shape
shows. Credit: measured and reverted by the parser-sharing lane, which correctly
declined to port someone else's in-progress feature under its own name.

Consequences to keep straight:

- A snapshot build is only as good as the tip. Where a tool is half-landed, the
  snapshot faithfully reproduces the breakage instead of hiding it behind a
  developer's working copy — which is the honest behaviour, and occasionally a
  surprise to whoever expected `$PWD` semantics.
- The failure mode is specifically deceptive: a *different* missing symbol each
  round. Anyone chasing it symbol-by-symbol should stop and run
  `git diff --stat` over the tool's directory first; if the diff is a coherent
  feature rather than a stray helper, the fix is to land that lane, not to port
  it.
- This does not weaken the case for fix 3. The four contention modes above are
  caused by reading a *moving* tree; a half-landed tip is a separate defect that
  is equally present in `$PWD` builds the moment the working copy is clean.

## CORRECTION (2026-09-05, 16:50): the SIGTERMs were a repo-owned RSS guard, not a peer

The cross-session-SIGTERM section above is **wrong about the cause** and is
retained only as history. The killer is
`scripts/resource/kill_simple_monitor.shs`, a daemon in this repo that kills any
`bin/simple run|test` exceeding **24 GB RSS**. Its own log, `/tmp/kill_simple_monitor.log`,
names the exact pids I traced:

```
2026-09-05T15:11:49 KILL pid=1983604 reason=simple_rss measured=24118 limit=24000
2026-09-05T16:37:30 WARN pid=2011613 rss=42655MB
2026-09-05T16:37:30 KILL pid=2011613 reason=simple_rss measured=42655 limit=24000
```

Both entries carry the full `native_build_worker.spl` argv. The `si_pid 2074427`
my strace recorded is the kill helper of monitor pid 2074271, started 11 s
earlier. 22 kills today, every one `reason=simple_rss` at the 24000 MB limit.

**This explains the determinism that never fit an external killer.** I noted
early that 427/428/429 s across three runs was too tight for coincidence and
could not account for it. It is not a timer at all: the worker's memory growth
is deterministic, so it crosses 24 GB at the same point in the same work every
run. Same mechanism, expressed in seconds.

**The load-bearing consequence: a Stage-3 self-host cannot complete on this host
while that monitor runs with its current ceiling.** A worker legitimately
reaches 42-50 GB — measured 41.7 GB steady at 22 minutes, and 42,655 MB at the
kill. The cap is 24 GB. Every run is killed on the way up, which is why seven
consecutive attempts died and none reached the phase-3 SIGSEGV.

The script protects `simple_mcp_server`, `simple_lsp_mcp_server`, tmux, claude,
codex, node and npm by name. A bootstrap worker is not on that list, which reads
as an oversight rather than intent: a self-host worker is precisely the
"legitimately enormous" case the list exists to spare.

### What this retracts

- "Another session on this shared box killed our worker" — **retracted.** A peer
  did run unanchored `pkill -f` patterns and confirmed it, and that is a real
  practice defect, but the measured deaths at 14:09, 14:21, 14:33, 14:45, 14:54,
  15:02, 15:11 and 16:37 are all `reason=simple_rss` in the monitor's log. I
  accepted a confession that the evidence did not support, and the peer
  volunteered the retraction after finding the log.
- Any run counted toward the phase-3 SIGSEGV population that died by SIGTERM
  needs re-filtering. A SIGTERM whose `si_pid` traces to the monitor is evidence
  of the RSS ceiling, not of the compiler defect. The `signal 11` apport entries
  remain real and remain separate.

### Fix options (not applied — a shared guard, and not mine to change alone)

1. Raise the ceiling for the bootstrap lane only: `KILL_SIMPLE_MEM_MB=65536` in
   the **monitor daemon's** environment, then restart the monitor. The script's
   own error text says `SIMPLE_TIMEOUT_SECONDS` does not affect this limit.
2. Add the `native_build_worker.spl` argv to `is_protected()` (line 191), which
   is the narrower change and matches the existing intent of that list.
3. Leave it and accept that Stage-3 self-host is not reproducible on this host.

Option 2 is the smallest correct change; option 1 is reversible and needs no
edit to a shared script. Either way the decision belongs to whoever owns the
box, not to a single lane mid-run.
