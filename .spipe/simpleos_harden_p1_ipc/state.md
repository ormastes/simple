# Lane P1 — Kernel IPC (SimpleOS Production Harden)

**Feature:** SimpleOS kernel IPC hardening — ABI v1 capability-transfer contract.
**Plan:** `doc/03_plan/agent_tasks/simpleos_production_harden_parallel.md` (lane P1)
**Research:** `doc/01_research/domain/simpleos_production_host_master_plan.md` (§5.1, §21)
**Date:** 2026-07-27
**Status:** first increment DONE (transfer algebra); runtime QEMU gate NOT started.

## Refined Goal

Lane P1's full charter is "endpoint call/reply/notification + atomic handle
transfer + single-use ReplyObject on the real syscall path; retire
`l4_fast_ipc.spl` to compat", gated by two isolated processes doing call/reply
and transferring a restricted handle under QEMU.

This increment deliberately scoped down to the **transfer algebra contract**,
because that is the part that can be proven with real assertions against
shipping code today, and it is the precondition for the runtime gate: there is
no point proving two processes exchanged a handle until "what a transferred
handle may carry" is pinned down and enforced.

Refined goal delivered: **pin the two ABI v1 transfer invariants as executable
contract, and close the one place where a one-shot authority was advertised but
not enforced.**

## What changed

### 1. `src/os/kernel/ipc/cspace_spawn.spl` — single-use guard implemented (NEW behavior)

`AttenuationSpec.single_use` already existed but its own doc comment called it
*"advisory single-shot flag for the transfer runtime (P5)"* — i.e. it was
**documentation only**. Nothing read the flag, so a capability minted as
"one-shot" could be replayed without limit. That is a real hole, not a
cosmetic one.

Added, all additive (no existing signature or struct changed, so `abi_v1.spl`
is untouched and no ABI RFC is required):

- `class SingleUseLedger` — `arm` / `consume` / `is_armed` / `is_consumed` /
  `armed_count`. `consume()` returns true on the FIRST call for an armed token
  and false on every later call; it also returns false for a token that was
  never armed (fail closed, so routing a normal token through `consume()` gets
  a deny rather than an accidental allow). `arm()` refuses to re-arm an
  already-armed token, so a spent one-shot can never be refunded.
- `fn spawn_with_cspace_tracked(parent, spec, child_owner, gen_base, tid_base, ledger)`
  — the real mint body; arms the ledger with the minted `token_id` for every
  accepted grant whose attenuation sets `single_use`. A **rejected** single_use
  grant arms nothing (no one-shot for authority never delegated).
- `fn spawn_with_cspace(...)` — kept at its original 5-arg signature, now a thin
  wrapper delegating to `_tracked` with a throwaway ledger. All existing callers
  (`llm_session.spl`, `fs_exec_spawn.spl`, `syscall_process.spl`, `abi_v1.spl`,
  4 security specs) are source-compatible and were re-run green.
- `fn atten_single_use()` — the missing constructor alongside `atten_identity` /
  `atten_rights`.

### 2. `src/os/kernel/ipc/l4_fast_ipc.spl` — honest status header (comment only)

Marked explicitly as **BENCHMARK MODEL — NOT the syscall path, NOT production
IPC**, naming the real owners (`ipc.spl` + `syscall_ipc.spl` for messages,
`cspace_spawn.spl` + `capability.spl` for transfer) and stating that it performs
no permission check, no capability transfer, no blocking and no address-space
crossing — `L4BufferPool.transfer_4096` moves a checksum, not a message. Numbers
from this file must never be quoted as SimpleOS IPC latency. File was NOT
deleted; a deletion condition is recorded in the header (delete when the syscall
path grows its own register-message fastpath + benchmark).

### 3. `test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl` — NEW contract spec

12 examples across two groups, asserting against the shipping code:

*Invariant A — rights only attenuate (master plan §21):* narrowing mask yields a
strict subset; a widening request is REJECTED not clamped (`rejected == 1`,
empty **pledged** pouch); the rights mask cannot be a back door to a bit the
sender never held (AND-only); the subset invariant holds for **every** cap of a
multi-grant recipe and every child is linked to its authorizing parent token;
delegation depth decrements per hop and a depth-0 token delegates nothing;
`CapabilityManager.grant` denies a spent token.

*Invariant B — one-shot used at most once:* the new `SingleUseLedger` (first use
succeeds, second and all later uses denied; rejected grant arms nothing; no
re-arm refund; unarmed token denied) **and** the pre-existing `EscrowCap` /
`consume_escrow` path in `capability.spl` (redeemed exactly once, only by the
intended receiver; a wrong receiver is denied before and after; an escrow never
exceeds the sender's current authority).

## Verdict

Runner: `timeout 240 /tmp/p1lane/bin/p1job run test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl`
(`p1job` = `bin/release/x86_64-unknown-linux-gnu/simple`; the deployed
`bin/simple` is a stale seed and `simple test` hangs on it.)

```
ABI v1 transfer: rights only attenuate, never widen
6 examples, 0 failures
ABI v1 transfer: single-use authority is consumable exactly once
6 examples, 0 failures
```

**Reproduce-first (spec proven able to fail), both halves:**

- Removed the `if self.used[i]: return false` replay check in
  `SingleUseLedger.consume` → `6 examples, 2 failures` ("denies the second use
  of a single_use capability…", "refuses to re-arm a spent one-shot…").
- Changed `r = rights & atten.rights_mask` to `|` in `_apply_attenuation` →
  `6 examples, 1 failure` ("narrows the receiver to a strict subset…").

Both breaks reverted; final re-run is the green above.

**Regression runs (consumers of the edited file), all green:**

| Spec | Result |
|---|---|
| `test/01_unit/os/security/spawn_with_cspace_spec.spl` | 7/3/4/2 examples, 0 failures |
| `test/01_unit/os/security/llm_role_session_spec.spl` | 10/3/5/2 examples, 0 failures |
| `test/01_unit/os/security/adversarial_escalation_attenuation_spec.spl` | 5/3/12 examples, 0 failures |
| `test/01_unit/os/kernel/ipc/l4_fast_ipc_spec.spl` | 3 examples, 0 failures |
| `test/01_unit/os/arch/duplicate_owner_spec.spl` | 4 examples, 0 failures |

## Honest blockers / NOT done

1. **The lane's real gate is NOT met.** Nothing here proves two isolated
   processes did a call/reply and transferred a restricted handle under QEMU.
   This increment is transfer *algebra* only, in-process, single address space.
   The spec's own docstring says so; do not quote it as the P1 gate.
   Resume: build the two-process QEMU x86_64 harness for endpoint call/reply,
   then extend this file (or a sibling `*_qemu_spec.spl`) with the receipt.

2. **No ReplyObject exists on the syscall path.** Grepped the whole of
   `src/os/kernel/ipc/` — the only `reply` token is a comment in
   `syscall_ipc.spl:57` ("arg1: authenticated source/reply port ID"). There is
   no reply-capability object, so "reply cap cannot be used twice" could not be
   spec'd as such; the one-shot invariant was proven on the two mechanisms that
   DO exist (`SingleUseLedger`, `EscrowCap`). A real single-use ReplyObject on
   the call/reply path is still owed by this lane.
   Resume: `grep -n "reply" src/os/kernel/ipc/syscall_ipc.spl` then design the
   ReplyObject over `SingleUseLedger` (the ledger is the intended substrate).

3. **`single_use` is enforced only where a caller threads a ledger.** The 5-arg
   `spawn_with_cspace()` still accepts a `single_use` recipe and discards the
   ledger. Existing call sites do not use `single_use` today, so nothing regressed,
   but the flag is only as strong as the caller. A stronger design (ledger owned
   by the kernel's cspace table rather than passed in) needs the P2 process/CSpace
   manager to exist first — that is lane P2's file.
   Resume after P2 lands: `grep -rn "spawn_with_cspace" src/os/kernel/` and move
   the ledger into the per-process CSpace owner.

4. **`l4_fast_ipc.spl` is marked, not retired.** The plan says "retire to compat";
   this increment only made its status honest in-file. Actual retirement waits on
   a real fastpath to retire it *in favour of*.

5. **Pre-existing linter defect (NOT caused by this lane).**
   `p1job lint <any file containing a class>` dies with
   `error: semantic: method `get` not found on type `str` (receiver value: <ClassName>)`.
   Reproduced on **untouched** `src/os/kernel/ipc/capability.spl` (receiver
   `CapabilityManager`) and on untouched `l4_fast_ipc.spl` (`L4BufferPool`), so it
   is not my change. Trace points into
   `src/compiler/90.tools/lint/_LintMain/traceability_and_assertions.spl:495,535`.
   Lint could therefore not be used as a gate for this lane. Worth filing against
   the lint tool owner (outside P1's exclusive paths, so not filed here).
   Resume/repro: `/tmp/p1lane/bin/p1job lint src/os/kernel/ipc/capability.spl`

6. **Board-runnable rule not yet discharged** — no QEMU and no board evidence in
   this increment, so no board claim is made. It falls out of blocker 1.

## Files touched (working copy only — NOT committed, per lane instructions)

- `src/os/kernel/ipc/cspace_spawn.spl` (modified — additive)
- `src/os/kernel/ipc/l4_fast_ipc.spl` (modified — header comment only)
- `test/01_unit/os/kernel/ipc/abi_v1_transfer_contract_spec.spl` (new)
- `.spipe/simpleos_harden_p1_ipc/state.md` (this file)

No file outside the lane's exclusive paths was edited; `src/os/kernel/abi/abi_v1.spl`
was read only.
