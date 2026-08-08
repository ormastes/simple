# Stage-2 build fails: incomplete `Mailbox` -> `PriorityMailbox` rename leaves a dangling symbol (2026-08-08)

## RESOLVED (2026-08-08)

Landed the exact fix shape validated by this doc's own "Auxiliary finding"
scratch probe:

- `src/lib/nogc_async_mut/actor_scheduler.spl`: `use mailbox_actor.{Mailbox,
  ...}` -> `{PriorityMailbox, ...}` (line 7); `mailbox: Mailbox` field type
  -> `mailbox: PriorityMailbox` (line 209); `Mailbox.new(MailboxConfig.default())`
  constructor -> `PriorityMailbox.new(MailboxConfig.default())` (line 290).
  Three references, matching the doc's root-cause enumeration exactly.
- `src/lib/nogc_async_mut/__init__.spl`: removed the resurrected
  `# Re-exported from mailbox.spl` block (`export Mailbox` +
  `export mailbox_new, mailbox_send, mailbox_receive, mailbox_try_receive`
  + `export mailbox_is_empty, mailbox_is_full, mailbox_size, mailbox_drain`)
  that `a019ba19aa6` had re-added after `983058c5ff39` deleted it. No
  importer of a root-level `Mailbox`/`mailbox_*` re-export was found
  (`983058c5ff39` had already established this file/these functions no
  longer exist), so removal — not correction — was the right call.

Verified with a fresh worktree (`/home/ormastes/dev/simple-mbxfix-v1`,
`git worktree add --detach origin/main`, distinct from the prior agent's
`/home/ormastes/dev/simple-s3rv2` scratch probe) and the same
`build_stage2.sh` invocation this doc used, re-pointed at the new worktree:

```
STAGE2_EXIT=0
Linked: /home/ormastes/dev/simple-mbxfix-v1/build/cyc/MBX1/stage2-simple (125109 KB) via clang++
Build complete: 794 compiled, 0 cached, 0 failed
  Time: 189.5s compile + 100.4s link = 289.9s total
```

Family sweep: `git grep -n '\bMailbox\b' -- src/lib/nogc_async_mut` at the
pre-fix tree showed no other bare `Mailbox` reference tied to
`mailbox_actor.spl`'s `PriorityMailbox`. The other `Mailbox` declarations
(`actors/actor.spl` `struct Mailbox`, `actors/__init__.spl`'s
`use std.actors.mailbox.{Mailbox, ...}`) are a distinct, still-live
`actors/` package with its own `struct Mailbox` — unrelated to this rename
and correctly left untouched, matching this doc's own "Scope check"
section.

Out of scope, left open as filed: the Stage-3 `method=len` monomorphize
SIGSEGV documented below under "Auxiliary finding" is a separate,
unresolved bug and was not chased here.

## Task context

Re-verify the Stage-2/Stage-3 self-host replay against current `origin/main`
after two pure-Simple compiler changes landed since the last full replay:
`a399483d` (span-kernel array-return registration,
`src/compiler/50.mir/_MirLoweringExpr/switch_operators_calls.spl` + LLVM
declares in `src/compiler/70.backend/backend/_MirToLlvm/asm_constraints_helpers.spl`)
and `796d8484` (same pattern for the two blend-span kernels).

## Verdict: Stage 2 FAILS at current `origin/main` — the two in-scope commits
were never reached, and are neither implicated nor exonerated by this run

The build breaks in `src/lib/nogc_async_mut/**`, nowhere near either
in-scope commit's files. **`a399483d` and `796d8484` remain unverified by
this replay, not "broken by".**

## Setup

- Fresh worktree `/home/ormastes/dev/simple-s3rv2`, `git worktree add
  --detach origin/main` (no reuse of any other session's dirty worktree —
  `/home/ormastes/dev/simple-s3bisect`, the previously-used replay worktree,
  was found mid-flight with another session's uncommitted changes to
  `src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl` and
  `src/compiler/35.semantics/layer_dag_checker.spl` and was left untouched).
- Pinned at `origin/main` `be775aa04fdbaa6b9548c74aec17413543698f12` (moved
  from `3e56ef9cb634` mid-session; re-fetched and re-pinned before running).
  Confirmed ancestors: `a399483dea7`, `796d8484b7c`.
- Replay scripts copied from `simple-s3bisect/build/cyc/{build_stage2,run_stage3}.sh`
  (per `doc/09_report/compiler/stage3_replay_verification_2026-08-07.md`'s
  documented technique), `R=` re-pointed at the new worktree, reused pinned
  seed-authority runtime at
  `/home/ormastes/dev/simple-t3-final-20260806/build/bootstrap-t3-final-20260806/stage3/x86_64-unknown-linux-gnu/stage2-runtime-authority`.
  `bin/simple` / `bin/release/**` in the shared repo untouched throughout.

## Command and result

```sh
cd /home/ormastes/dev/simple-s3rv2 && sh build/cyc/build_stage2.sh RV1
```

```
STAGE2_EXIT=1
FAILED FILES (1):
  - src/lib/nogc_async_mut/actor_scheduler.spl => ... llvm codegen: semantic:
    llvm global load referenced undeclared symbol `Mailbox`
```

Deterministic (single run, explicit specific diagnostic — not a masked
SIGSEGV; `SIMPLE_BOOTSTRAP=1`'s known rc=1-masks-SEGV risk does not apply
here since the message is a concrete codegen diagnostic, same reasoning the
prior replay doc used for its own rc=1).

## Root cause: `a019ba19aa6` resurrected a re-export the immediately-prior
commit had just deleted, and missed one of two consumers of the renamed symbol

Two commits landed back-to-back on 2026-08-07, both touching
`src/lib/nogc_async_mut/`:

1. **`983058c5ff39`** "delete dead struct Mailbox, unblock Stage-2
   ambiguous-export build" — deleted `mailbox.spl` (dead `struct Mailbox`),
   removed `__init__.spl`'s "Re-exported from mailbox.spl" block (blob
   `d1cd7d88f6d` -> `b05fc1d9c86`), and repointed
   `actor_scheduler.spl`'s import from `mailbox.{Mailbox,...}` to
   `mailbox_actor.{Mailbox,...}` (the surviving `class Mailbox`).
2. **`a019ba19aa6`** "rename mailbox_actor.Mailbox to PriorityMailbox" —
   renamed `mailbox_actor.spl`'s `class Mailbox` to `class PriorityMailbox`
   and updated its `__init__.spl` export line
   (`export Mailbox` -> `export PriorityMailbox`) and its **one** known
   importer, `test/.../mailbox_actor_select_spec.spl`. But its own diff to
   `__init__.spl` is based on blob `b05fc1d9c86` (983058c5ff39's post-state)
   and **re-adds** the exact five lines 983058c5ff39 had just deleted
   (`# Re-exported from mailbox.spl` / `export Mailbox` / the four
   `mailbox_*` function exports) — resurrecting a re-export block for a file
   that no longer exists. It also did **not** update
   `actor_scheduler.spl`'s `use mailbox_actor.{Mailbox, MailboxConfig, ...}`
   import (line 7) or its two usages (`mailbox: Mailbox` field type at line
   209, `Mailbox.new(MailboxConfig.default())` constructor at line 290) —
   the second real consumer 983058c5ff39 had just repointed at
   `mailbox_actor.Mailbox`.

Net effect at `origin/main`: `mailbox_actor.spl` defines only
`PriorityMailbox`, not `Mailbox` (confirmed —
`grep -n '^class \|^struct ' src/lib/nogc_async_mut/mailbox_actor.spl`
lists `MailboxConfig`, `MessageRef`, `MailboxStats`, `PriorityMailbox`, no
`Mailbox`). `actor_scheduler.spl`'s explicit
`use mailbox_actor.{Mailbox, ...}` therefore cannot resolve to any real
declaration. This slips past whatever check would normally catch an
unresolved type/import under this Stage-2 build's flags and is only caught
at LLVM codegen time as an "undeclared symbol" global load — a diagnostic
class distinct from the two previously-documented Stage-2/3 blocker
families (ambiguous-export hard-fail; field-index-collision SIGSEGV).

Scope check: other `Mailbox` declarations exist
(`src/lib/nogc_async_mut/actors/actor.spl:254` `struct Mailbox`,
`src/app/interpreter/async_runtime/mailbox.spl:271` `struct Mailbox`,
`src/app/llm_caret/claude_full/utils/mailbox.spl:17` `class Mailbox`) but
none are `mailbox_actor.spl`, so they are irrelevant to this
module-qualified `use mailbox_actor.{Mailbox,...}` failure.

## Auxiliary finding (not root-caused, filed for the record): a second,
distinct Stage-3 SIGSEGV appears once the Stage-2 blocker above is patched

To determine whether Stage 3 (and therefore the two in-scope commits) would
complete once Stage 2 is unblocked, an **unlanded, worktree-only** probe was
applied in `/home/ormastes/dev/simple-s3rv2` (never committed, never
pushed, matches the precedent in
`stage3_replay_verification_2026-08-07.md` of using scratch-only
experimental patches): `actor_scheduler.spl`'s three `Mailbox` references
changed to `PriorityMailbox`, and `__init__.spl`'s resurrected
mailbox.spl re-export block removed.

```sh
sh build/cyc/build_stage2.sh RV2
# STAGE2_EXIT=0 — Linked build/cyc/RV2/stage2-simple (125109 KB), 794
# compiled, 0 cached, 0 failed, 401.7s total

sh build/cyc/run_stage3.sh RV2 RV2S3 900
# STAGE3_EXIT=139 (SIGSEGV, not the 900s SIGKILL budget)
# WALL=513s  PEAK_RSS_KB=9368600
# PROGRESS: phase=monomorphize tasks_done=4 tasks_total=6 tasks_remaining=2
# stage3.log tail: [mir-lower-expr] method-dispatch-before method=len
#                  [mir-method-call] start method=len argc=0
#                  timeout: the monitored command dumped core
#                  Segmentation fault
```

No `^error:` line preceded the crash (checked: `grep -n '^error:'
stage3.log` — zero hits), so this is a raw SIGSEGV, not a diagnosed
compiler error. No core file was captured (`ulimit -c` = 0, `core_pattern`
routes to apport) so no backtrace was obtained. This crash is **not
root-caused here** — it is a new, previously-undocumented Stage-3 blocker,
distinct from the `LayerDagRegistry.edges` field-collision family (already
fixed) and from the seven-blocker chain in
`stage3_blocker_tractability_2026-08-07.md`. It occurs during monomorphize
at a `method=len` dispatch; whether it involves the two in-scope span-kernel
commits' code paths was not established — both files
(`switch_operators_calls.spl`, `asm_constraints_helpers.spl`) make heavy,
generic use of `.len()` throughout the compiler itself, so the method name
alone is not diagnostic.

**This Mailbox-rename fix was NOT landed** — it exists only in the scratch
worktree `/home/ormastes/dev/simple-s3rv2`, per the task's explicit
instruction not to modify compiler/lib source beyond restoring
`origin/main` content, and per the standing rule against touching files
another session may be mid-flight on.

## Conclusion for the task's original question

Whether `a399483d` and `796d8484` keep the self-host chain intact **could
not be determined**: `origin/main` at `be775aa04fd` does not build past
Stage 2 (blocked by the Mailbox/PriorityMailbox rename gap above, unrelated
to either in-scope commit), and even with that gap patched in an unlanded
scratch probe, Stage 3 hits a second, different, undiagnosed SIGSEGV before
reaching the two in-scope commits' span-kernel code paths with any
certainty. Both failures are reported here as open blockers; neither commit
in scope is implicated by direct evidence, but neither is exonerated
either — the chain simply never got there.

## What would close this

1. Land the real fix for the rename gap: `actor_scheduler.spl`'s three
   `Mailbox` -> `PriorityMailbox` references, and drop `__init__.spl`'s
   resurrected mailbox.spl re-export block (exact patch shape reproduced in
   this doc's "Auxiliary finding" section, applied and verified as
   sufficient to reach Stage 2 GREEN).
2. Re-run `run_stage3.sh` against a properly-landed Stage 2 and get a
   backtrace on the `method=len` monomorphize SIGSEGV (e.g. raise
   `ulimit -c unlimited` before the replay, or attach `gdb` proactively once
   the process is observed to reach the monomorphize phase).

## Evidence / artifacts

- `/home/ormastes/dev/simple-s3rv2/build/cyc/RV1/stage2.log` — Stage-2
  failure, real (unpatched) `origin/main` content.
- `/home/ormastes/dev/simple-s3rv2/build/cyc/RV2/stage2.log` — Stage-2
  success with the unlanded scratch probe.
- `/home/ormastes/dev/simple-s3rv2/build/cyc/RV2S3/stage3.log`,
  `progress.events`, `mem.log` — Stage-3 SIGSEGV with the unlanded scratch
  probe.
- Blob-hash chain proving resurrection:
  `git show 983058c5ff39 -- src/lib/nogc_async_mut/__init__.spl` (blob
  `d1cd7d88f6d` -> `b05fc1d9c86`, drops the mailbox.spl block) then
  `git show a019ba19aa6 -- src/lib/nogc_async_mut/__init__.spl` (diff base
  `b05fc1d9c86` -> `55b89a2c0ce`, re-adds the identical block).

## Disk

`df -h /` before and during: 215G free on `/`, well above the 100G abort
threshold; both replay runs together used well under 1G of scratch space.
