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
