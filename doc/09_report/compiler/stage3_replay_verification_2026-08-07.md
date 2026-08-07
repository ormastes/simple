# Stage-3 combined-fix replay verification (2026-08-07)

## Purpose

`doc/09_report/compiler/stage3_blocker_tractability_2026-08-07.md` (commit
`6ac02f5d8a93`) identified seven sequential Stage-3 self-host blockers, all
pure-Simple, all individually fixed and landed — but never verified together
in one run. This is that run.

## Setup (isolated, non-destructive)

- **Worktree used**: `/home/ormastes/dev/simple-s3bisect` — a pre-existing
  linked `git worktree` of this repo (`git worktree list` shows
  `.git/worktrees/simple-s3bisect`), already used by prior lanes for the same
  replay technique, with its own `build/cyc/` scratch area and a reusable
  pinned stage2-runtime-authority seed at
  `/home/ormastes/dev/simple-t3-final-20260806/build/bootstrap-t3-final-20260806/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority/simple`.
  Nothing under `/home/ormastes/dev/pub/simple/bin/` or
  `/home/ormastes/dev/pub/simple/bin/release/**` (the shared binary five
  concurrent sessions depend on) was touched.
- **Pinned to** `origin/main` at fetch time, `git checkout -f origin/main` →
  `6ac02f5d8a93cbbac3838726fe2dc65195f341ad`. Verified all four fix commits
  named in the tractability report are ancestors:
  `b9e23914a0e`, `976c44a28f6`, `f7cf6c87b02`, `39a2c7c2040` — all
  `ANCESTOR`.
- Discarded one pre-existing uncommitted local change in that worktree before
  running (not mine, not requested to preserve, recorded here for the prior
  lane's benefit): `src/compiler/80.driver/driver_bootstrap.spl` had two
  lines changed from `var translator = MirToLlvm.create(...)` to
  `var translator: MirToLlvm = MirToLlvm.create(...)` (an explicit-type-
  annotation experiment, not on origin/main, not committed anywhere).
- Remaining `git status` noise after checkout: only CRLF/LF line-ending diffs
  on Windows `.cmd`/`.bat` files — irrelevant to compilation, left as-is.

## Commands run

```sh
cd /home/ormastes/dev/simple-s3bisect
sh build/cyc/build_stage2.sh VER8   # Stage 2 only: seed rebuilds stage2 from current tree
```

`build_stage2.sh` runs the **pinned seed** (not the shared `bin/simple`)
against `--source src/compiler --source src/app --source src/lib`, output to
`build/cyc/VER8/stage2-simple` (isolated scratch dir inside the worktree,
outside the main repo entirely).

`run_stage3.sh` (which would replay Stage 3 against the resulting stage2
binary) was never reached — Stage 2 itself did not produce a binary.

## Result: Stage 2 fails before Stage 3 can even start

```
STAGE2_EXIT=1
Build failed: ambiguous package export `Mailbox` in
  /home/ormastes/dev/simple-s3bisect/src/lib/nogc_async_mut/__init__.spl:
  /home/ormastes/dev/simple-s3bisect/src/lib/nogc_async_mut/mailbox.spl,
  /home/ormastes/dev/simple-s3bisect/src/lib/nogc_async_mut/mailbox_actor.spl
NO STAGE2 BINARY
```

Reproduced twice (`VER8`, and again as `VER9` after an ineffective local
patch attempt described below) — deterministic, not flaky.

### Root cause (verified, pure-Simple)

Two genuinely distinct types are both named `Mailbox` and both explicitly
exported under that bare name from sibling files in the same package:

- `struct Mailbox` — `src/lib/nogc_async_mut/mailbox.spl:18`, exported at
  `mailbox.spl:74` (`export Mailbox, mailbox_new, ...`)
- `class Mailbox` — `src/lib/nogc_async_mut/mailbox_actor.spl:103`, exported
  at `mailbox_actor.spl:305` (`export MailboxConfig, Mailbox, MailboxStats, ...`)

The facade `src/lib/nogc_async_mut/__init__.spl` re-exports both (`export
Mailbox` at line 135 *and* line 145) — but the ambiguity is not merely a
duplicated re-export line; it is the two leaf files independently exporting
the same bare name. Confirmed by attempting the obvious fix: deleting the
`export Mailbox` at `__init__.spl:145` and rerunning (`VER9`) reproduced the
**identical** error — the ambiguity is at the source-definition level, not
the facade-re-export level, so this experiment-only patch was reverted
without landing it (`git checkout -- src/lib/nogc_async_mut/__init__.spl` in
the isolated worktree only; no effect outside it).

### Checker location (Rust seed, but the defect it flags is pure-Simple)

The hard error is raised by
`src/compiler_rust/compiler/src/pipeline/native_project/discovery.rs:1031`
(package-export discovery). There is a documented escape hatch —
`SIMPLE_AMBIGUOUS_EXPORT_ALL=1` demotes it to a warning
(`discovery.rs:1016`) and includes all candidate providers — but
`build_stage2.sh` does not set it (its `env -i` allowlist does not include
this var), and setting it was out of scope for this experiment since it
changes resolution semantics, not just diagnostics.

### Why prior lanes' Stage 2 builds didn't hit this

Both `struct Mailbox` (mailbox.spl) and `class Mailbox` (mailbox_actor.spl)
already existed at the older pinned commit this worktree was previously on
(`9393117a5fe`, 2026-08-06), where prior lanes' `build_stage2.sh` runs
reportedly succeeded (per `t3_full_bootstrap_stage3_..._2026-08-06.md`'s
GRN2RUN/FIX1RUN/SAB3RUN table). The discovery-time ambiguity check only
fires when something in the actual `--entry-closure` walk *requests* the
bare name `Mailbox`; it is dormant otherwise. Something in the 8 commits
between `9393117a5fe` and `6ac02f5d8a93` (touching
`src/lib/nogc_async_mut/`, e.g. `ab9044219a0` "Mailbox.select ignored
high-priority queues") changed what gets pulled into the requested set.
**Not fully root-caused here** — no direct unqualified `Mailbox` consumer
was found by grep — but the mechanism (demand-driven discovery) explains why
a long-dormant name collision only now became a hard build failure. This is
an eighth blocker, newer than and independent of the seven traced in the
tractability report.

## Verdict

**The seven-fix chain could not be exercised together at Stage 3** — not
because Stage 3 itself regressed, but because **Stage 2 no longer builds at
current `origin/main`** due to this newly-hard-failing ambiguous-export
collision. Stage 3 was never reached. The tractability report's seven
blockers remain correctly characterized as fixed and landed (nothing here
contradicts that), but the "decisive experiment" it called for is now
gated behind an eighth, distinct, pure-Simple blocker at Stage 2:

- **File**: `src/lib/nogc_async_mut/__init__.spl:135,145` (facade) and the
  two source definitions `src/lib/nogc_async_mut/mailbox.spl:18` /
  `src/lib/nogc_async_mut/mailbox_actor.spl:103`
- **Nature**: pure-Simple source defect (name collision), not a Rust-seed
  defect — the seed's discovery checker is correctly flagging a real
  ambiguity in `src/lib`.
- **Fix shape** (not attempted here — out of scope, would need to land on
  `origin/main`, not just this isolated worktree): rename one of the two
  types, or make the facade export only one of them under a distinct alias
  and require the other's qualified/aliased form at call sites.

## Evidence caveats

- `build_stage2.sh` / `run_stage3.sh` both set `SIMPLE_BOOTSTRAP=1`
  internally (visible in both scripts' `env -i ... SIMPLE_BOOTSTRAP=1 ...`
  line) — this is the same technique multiple prior bug docs used and is
  **not** disqualifying here: the known masking risk is SEGV silently
  reported as bare `rc=1` with no diagnostic. This run's `rc=1` carries an
  explicit, specific `Build failed: ambiguous package export ...` message,
  so the masking risk named in the task brief does not apply to this
  particular result — the error text is real and specific, not a masked
  crash.
- Because Stage 2 never produced a binary, `run_stage3.sh` was never
  invoked and no Stage-3-specific evidence (clean completion or an eighth
  Stage-3-internal blocker) exists from this run.

## Disk space

| | Free on `/` |
|---|---|
| Before | 239G |
| After `build_stage2.sh` (VER8, failed fast) | 239G |
| After `build_stage2.sh` (VER9, failed fast) | 239G |

Never approached the 100G abort threshold — both runs failed in seconds,
before any significant compilation output was written.

## What was NOT touched

- `/home/ormastes/dev/pub/simple/bin/simple`, `bin/release/**` — untouched.
- No `cargo build`, no `--full-bootstrap`.
- The isolated worktree's local ineffective patch was reverted before
  finishing; the worktree is left at clean `origin/main` (`6ac02f5d8a93`)
  plus the pre-existing CRLF-only noise that was already there.
