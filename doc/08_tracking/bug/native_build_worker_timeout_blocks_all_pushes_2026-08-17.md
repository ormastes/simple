# `native-build` worker times out, making a mandatory pre-push guard permanently RED

**RESOLVED 2026-08-18** (verified at `ce396605fef`, pristine `origin/main`).
Status was OPEN; it is now closed by `e78c7bf3779` ("fix(desugar): break an
unbounded global-array push loop that OOMed native-build", landed 2026-08-18
08:56 -- three commits before the verification tip). This record was filed
BEFORE that commit, so its OPEN status was simply stale, not wrong.

The control fixture was never the defect and neither was the guard: plain
`native-build` genuinely could not build ANY program, the trivial control
included. The underlying fault is an interpreter defect -- on a MODULE-GLOBAL
array, `.push()` grows a live copy while `.len()` in a `while` condition still
reads the stale global, so
`transform_placeholder_call_args_after_interpolation`
(`src/compiler/10.frontend/desugar/placeholder_lambda.spl:342`) never
terminates and pushes until the worker is killed. That single loop explains
BOTH recorded shapes: the 7200s `worker timed out` in this record and the
rc=143/134 >24 GB SIGKILL in
`prepush_hook_unpassable_native_build_oom_2026-08-17.md`.

Evidence at `ce396605fef`, `bin/simple` = the shared Rust seed
(`/mnt/data/worktrees/simple-main/bin/release/x86_64-unknown-linux-gnu/simple`,
59546088 bytes, mtime 2026-08-18 07:53:39):

- The guard's own control invocation, run by hand, exit status captured on its
  own line (never through a pipe): `CTRL_RC=0`, binary produced, and it runs
  `stdout=[ctrl-ok] exit=7` -- exactly what the guard asserts. ~4 min wall,
  worker peak ~2.88 GB RSS, CPU/elapsed ~1:1 (compute-bound, not blocked).
- `sh scripts/check/check-native-extern-fabrication.shs --selftest` ->
  `PASS — selftest: 19 fixture assertion(s) checked, 0 failed` (exit 0).
- Full guard run -> exit 0, verdict line:
  `PASS — native-build extern fabrication: control unaffected, known-open gap unchanged`
  with no `FAIL — control fixture` line anywhere in the output.

Nothing in the guard was weakened, relaxed, or deleted to reach green; the
control fixture is untouched and still fails the gate if native-build breaks
again. The extern-fabrication gap the guard actually fences is still OPEN and
still reported as KNOWN-OPEN (nm class `T`, 3-byte defined symbol
`lane_definitely_absent_probe`, program runs to completion printing `r=0`) on
BOTH the `[default]` and `SIMPLE_NO_STUB_FALLBACK=1` `[strict]` lanes -- so
this closure is about the infrastructure outage only, not about that gap.

---


**Filed** 2026-08-17. **Status** RESOLVED 2026-08-18 (see note above). **Impact** blocks EVERY guarded push on
this host, for every lane.

## Symptom

`sh scripts/check/check-native-extern-fabrication.shs` fails immediately with:

```
FAIL — control fixture (no extern) no longer builds under native-build
```

It is wired into `pre-push-conflict-tree-guard.shs`, so `git push` is blocked
for all lanes with:

```
pre-push: BLOCKED by check-native-extern-fabrication.shs (status 1) for range
          native-build extern-fabrication probe (full scan, not range-bound)
```

## Root cause — NOT extern fabrication

The guard discards the compiler's actual error, so the verdict is misleading.
Reproduced directly with the guard's own arguments:

```
env -u SIMPLE_BOOTSTRAP bin/simple native-build --source test/fixtures \
  --entry-closure --entry test/fixtures/native_extern_fabrication_probe/control.spl -o /tmp/ctrl.bin
CTRL_RC=255
error: native-build worker timed out after 7200s before producing a binary.
  The interpreted worker loads the whole compiler + LLVM import graph before any
  codegen; a large --source set (e.g. src/os + src/lib) exceeds the budget.
  Raise --timeout, shrink --source, or use the in-process backend for
  cross-target builds.
```

So `native-build` cannot complete at all here. The guard is behaving correctly —
its header states the control fixture exists precisely so the gate "cannot be
vacuously green because native-build itself is broken". It is reporting real
infrastructure breakage, not a fabrication finding. **Do not "fix" this by
deleting or relaxing the control.**

## Why the verdict line is still a defect

`check-native-extern-fabrication.shs:71-75` runs the control build inside an
`if !`, discards its log, and prints only "no longer builds". The 255 and the
timeout text are captured to `$ctrl_log` but never surfaced on failure, so the
operator sees a fabrication-shaped verdict for a timeout. Suggested minimal
fix: echo the last few lines of `$ctrl_log` on that failure path, the way the
`[default]`/`[strict]` branches already do for their own logs.

## Scope note

This is host/toolchain territory, not a product-code defect in any one lane. It
was found by the unstable_test_mode lane while trying to land two files (a
check script and a tracking doc) that cannot possibly affect `native-build`.
Handing it off rather than working around it: the correct resolutions are to
raise the worker timeout, shrink the guard's `--source` set, or use the
in-process backend as the error text itself suggests — all decisions for
whoever owns the native-build lane.

**Never** resolve this with `git push --no-verify`. Nine mandatory guards exist
because two unbuildable trees reached `main` on 2026-08-11 exactly that way.

## Diagnostics follow-up completed 2026-08-18 (lane GUARD2)

The diagnostics half of this is now finished in
`scripts/check/check-native-extern-fabrication.shs`. The reporter added on
2026-08-17 (`report_ctrl_failure`) was wired into the control branch only; the
two absent-case branches (`[default]`, `[strict]`) still did `sed -n '1,20p'`
on logs of the same ~1180-line shape, where the head is nothing but the
bootstrap-seed banner and an `export use *` lint warning and the real error is
in the last four lines — so a genuine failure in either of those branches was
undiagnosable.

Changes (diagnostics only — the gate still checks exactly what it did):

- `report_ctrl_failure` renamed to `report_build_failure` and given a third
  argument naming which build the log belongs to, so an operator is not told
  "control" about a `[strict]` failure. Still tail-based (`tail -n 25`), still
  prints rc, log path and line count, still emits the explicit
  `DIAGNOSIS: ... WORKER TIMEOUT, not extern fabrication` line on a match.
- All three remaining `sed -n '1,20p'` call sites (the unrelated-build-failure
  branch and the unexpected-third-outcome branch inside `check_absent_case`,
  for both env combinations) now route through it. Build rc is still captured
  on its own line via `|| rc=$?`, never through a pipe.
- `--selftest` extended from 4 to **10** fixture assertions, still fatal:
  the two original control fixtures plus a `[default]` long-log fixture
  (tail surfaced / branch named / fixture proven head-hostile so the first two
  assertions cannot pass vacuously) and a `[strict]` long-log fixture carrying
  a NON-timeout error (surfaced / not falsely diagnosed as a timeout / branch
  named). Verdict: `PASS — selftest: 10 fixture assertion(s) checked, 0 failed`.
  Fail-closedness re-proven by mutating the reporter back to a head-print in a
  scratch copy: 3 assertions fire and the run exits 1.

**The push blocker is unchanged and still in place.** The control fixture was
not deleted, relaxed, or made conditional, and the FAIL/exit-1 path is
untouched — a broken `native-build` still blocks the push. Only the message an
operator reads got better.

## Related

- `doc/08_tracking/bug/origin_main_unbuildable_rust_seed_2026-08-11.md`
- Guard-integrity note: these native-build guards read `src/` from the
  *invoking* tree, so the same commits can pass from one checkout and fail from
  another. Confirmed here that the FAIL reproduces from BOTH the main tree and a
  clean `git worktree` at the origin tip, so this one is not worktree-specific.

---

# Update 2026-08-18 (lane NATIVEBUILD): root cause is an UNBOUNDED RSS LEAK, not a timeout

## Verdict: SLOW-with-a-leak, not HUNG — and the kill is earlyoom, not the timer

The worker makes continuous forward progress and never wedges. It is killed
because it exhausts memory, long before any timeout fires. Both remedies named
in the compiler's own error message (`raise --timeout`, `shrink --source`) are
therefore not merely dead, they are **diagnosing the wrong resource**.

## /proc evidence (attach-based profiling is blocked here; this is sampling only)

Probe: a **2-line** hello-world, its own 1-file `--source` dir.

```
fun main():
    print("hello")
```

Process tree (`bin/simple native-build` -> `timeout` -> the real worker):

```
1360710 S  rss=33076KB    bin/simple native-build ...          <- parent poller
1360898 S  rss=2132KB     timeout --kill-after=10s 900s stdbuf -oL -eL ...
1360905 S  rss=3965564KB  simple run src/app/cli/native_build_worker.spl  <- WORKER
```

Worker RSS trajectory, sampled every 10s — monotonic, no plateau, no GC:

| t | RSS | CPU ticks (utime/stime) | state |
|---|---|---|---|
| 0s  | 4.77 GB | 7637 / 6592 | S |
| 20s | 4.89 GB | 8236 / 6627 | S |
| 40s | 4.95 GB | 8527 / 6645 | S |
| 60s | 5.09 GB | 9159 / 6682 | S |
| 80s | 5.18 GB | 9624 / 6706 | S |
| **8m47s (final)** | **6.22 GB** | 13233 / 7165 | S |

**6.2 GB and still climbing, for a two-line program.** Growth ~5-11 MB/s,
utime climbing throughout: it is *executing*, not blocked. State is `S`/`R`,
never `D`, and it never sits on one wchan.

## Why this presents as rc=255 "timeout"

`earlyoom` on this host is configured to **prefer killing `simple`**:

```
/usr/bin/earlyoom -r 3600 --prefer ^(simple|rustc|cc1|cc1plus|lto1|collect2|qemu-system|ld) ...
```

At probe time the box had 125 GB total / 107 GB used / **1 GB free**. A worker
growing 5-11 MB/s reaches the ceiling in tens of minutes and is SIGTERMed.
Per the evidence rule, note that **no `[TIMEOUT: Process killed after Ns]` line
was ever emitted** by native-build in these runs — so the earlier rc=255 results
attributed to the timer are more likely earlyoom kills. The 2-hour budget was
never the binding constraint.

## Secondary defect found in the parent: O(n^2) log relay

The parent poller (`src/app/io/process_ops.spl`, `process_run_timeout_live`,
~line 148 onward) polls on a sleep and **re-reads the whole stdout/stderr temp
file on every poll** to relay newly-appended bytes. Sampled: main thread in
`futex_wait_queue`, worker thread `simple-main` in `hrtimer_nanosleep`, with
`syscr` +160 and `rchar` +1.08 MB per 20s while its own RSS stayed pinned at
exactly 33076 KB. Harmless at small log sizes, quadratic on a long run. Not the
blocker, but it is real and worth fixing separately.

## Code path

- Dispatch: `src/compiler_rust/driver/src/main.rs:168-178` — `native-build`
  goes to the Rust in-process handler **only** if `SIMPLE_NATIVE_BUILD_RUST`
  is set (`:168`) or the build is cross-target (`:176`). Otherwise it falls
  through to the pure-Simple path.
- Interpreted worker: `src/app/cli/native_build_worker.spl`, spawned as
  `simple run <worker>.spl` — i.e. the **seed interpreter** interpreting a
  program that imports the entire compiler + LLVM graph. That import graph, not
  the user's input, is what allocates; this is why a 2-file `--source` behaves
  identically to the full tree.
- Misleading diagnostic text: `src/app/cli/native_build_main.spl:314-320`.
  Note `:314` already anticipates the memory ceiling ("The interpreted worker's
  RSS grows through parse/lowering; it hit the process ...") — the memory
  branch exists, but the message that actually fires blames the timeout.
- In-process backend: `src/compiler_rust/driver/src/cli/native_build.rs`
  (`NativeProjectBuilder`, ~line 620) — runs in the current process, no
  interpreted worker, no `simple run`.

## The in-process route is VIABLE — proven

The remedy needs **no code change**: the env-var route already exists at
`main.rs:168`. Same probe, same flags:

```
env -u SIMPLE_BOOTSTRAP SIMPLE_NATIVE_BUILD_RUST=1 bin/simple native-build \
  --source <probe> --entry-closure --entry <probe>/main.spl -o <out> --timeout 900
RC=0  ELAPSED=50s
  Time: 0.2s compile + 47.7s link = 47.9s total
  Binary: probe2.bin (28 KB)
Build complete: 1 compiled, 0 cached, 0 failed
```

**RC=0 in 50 seconds**, versus the interpreted worker never completing and
reaching 6.2 GB. Compile is 0.2s; the 47.7s is all linker. Memory stays flat.

## Recommendation

Route host-target `native-build` through the in-process backend by default,
inverting the condition at `main.rs:168` so the interpreted worker is opt-in
rather than the default. For the immediate push blocker, exporting
`SIMPLE_NATIVE_BUILD_RUST=1` around the control build in
`scripts/check/check-native-extern-fabrication.shs` is sufficient (that script
is owned by lane GUARD2 — not changed here).

## Caveats — two separate pre-existing defects, NOT part of this bug

1. The produced binary **segfaults**. The build emits
   `error: runtime archive is STALE: build/simple-core/libsimple_runtime.a ...
   refusing to link a stale archive`, then links anyway after
   `Generating 3 stub functions for unresolved symbols` (`__cpu_indicator_init`,
   `__cpu_model`, `fun`). A stale-archive error that does not stop the link, and
   a stub named `fun`, are both independently suspicious. So the in-process
   route makes the guard's control fixture *build*; whether the guard also needs
   it to *run* must be checked before declaring the blocker cleared.
2. At the time of writing **15 other `native_build_worker.spl` processes** from
   other lanes were live on this host, all leaking on the same path. This is a
   host-wide memory drain, not one lane's problem.

## Status

Push blocker: **still BLOCKED** as filed, but the cause is now identified and a
proven, zero-code-change workaround exists. No code changed by this lane —
the fix belongs in the dispatch default (`main.rs:168`) and/or the guard script,
and the leak itself in the interpreted worker remains OPEN and unfixed.

## 2026-08-18 — the execution-mode theory is dead; both engines hit the same ~12.5 GB ceiling

A recurring proposal for this blocker is "stop forcing the tree-walking
interpreter" (`src/app/cli/native_build_main.spl:272-273` sets
`SIMPLE_EXECUTION_MODE=interpret` when unset, with no justification at the call
site). **Measured, and it does not help.** Identical 3-line fixture, identical
command except the mode (`SIMPLE_NATIVE_BUILD_WORKER=1 ... bin/simple run
src/app/cli/native_build_worker.spl --entry tiny.spl`, `ulimit -v 27000000`,
`timeout 600`, `/usr/bin/time -v`):

| mode | peak RSS | wall | outcome |
|---|---|---|---|
| interpret | 12,577,548 KB (12.58 GB) | 4:45.49 | RC=134 abort, no binary |
| jit | 12,523,856 KB (12.52 GB) | 6:54.43 | RC=134 abort, no binary |

Both die at `[build] parse 0/1 step 1/6`. Same ceiling within 0.5%; JIT is ~45%
SLOWER. The failure is therefore **not** an interpreter defect and **not** a JIT
defect — it is retention during module loading (737 modules loaded once each,
~17 MB retained per module, ~400x on-disk size). The default was deliberately
left unchanged: switching it would trade nothing for worse wall time.

Corroborating datapoint at full scale, same day: the direct-seed
`--entry-closure` build of `bootstrap_main.spl` was SIGTERMed (RC=143) at
10:46 wall with earlyoom naming it explicitly (`"simple": badness 1014,
VmRSS 9164 MiB`), well inside a 1800s bound — memory, not time. Detail:
`doc/08_tracking/bug/native_build_direct_seed_jit_hang_2026-07-30.md`
(2026-08-18 section).
