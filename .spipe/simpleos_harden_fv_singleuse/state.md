# Lane FV — Formal invariant: single-use capability consumption

Master plan §21.3. Status: **DONE — sorry-free proof landed in working copy (not committed).**

## Goal
Add a MANUAL, sorry-free Lean proof of the single-use-capability-consumption
invariant (from lane P1's `SingleUseLedger`) as a NEW module inside the EXISTING
`kernel_capabilities` lake project — reuse its toolchain, do not create a new
project.

## Source of truth
`src/os/kernel/ipc/cspace_spawn.spl` — `class SingleUseLedger` (lines 62-128):
- `arm(token_id)`: returns `false` and leaves the ledger UNCHANGED when the id is
  already in `token_ids` (no re-arm — re-arming would refund a spent one-shot);
  otherwise pushes it with `used=false` and returns `true`.
- `consume(token_id)`: `true` on the FIRST call for an armed, unused id (sets
  `used=true`); `false` on every replay (armed + already used); `false` for a
  never-armed id (fail closed). A consumed id is never removed from `token_ids`.

## Model (Lean, pure core Lean 4 — NO Mathlib)
File: `src/verification/kernel_capabilities/KernelCapabilities/SingleUse.lean`
(namespace `KernelCapabilities`, matches Basic.lean / Theorems.lean style).

`structure Ledger where armed : List Nat; consumed : List Nat`
- `armed`    mirrors `token_ids` (an id present here = ARMED).
- `consumed` mirrors the subset with `used[i]=true` (= CONSUMED).
- `Ledger.arm l id`     : `if l.armed.contains id then (false, l)` else add to armed.
- `Ledger.consume l id` : `if armed.contains id && !consumed.contains id then
  (true, add-to-consumed)` else `(false, l)`.
A consumed id stays in `armed` (as in the real parallel arrays), so `arm` on it
is a no-op and does NOT clear `consumed` — the "no re-arm refund" property, proved
faithfully rather than assumed.

## Theorems proved (all sorry-free)
- **SU1 `single_use_consume_once`** — after a successful `consume id`, a second
  `consume id` on the resulting ledger returns `false`.
- **SU2 `unarmed_consume_denied`** — `consume id` on a never-armed id returns
  `false` (fail closed).
- **SU3 `no_reuse_after_consume`** — after a successful `consume id`, an
  intervening `arm id` (which the real code refuses) is a no-op that leaves the
  consumed flag set, so a follow-up `consume id` is still `false`. Models "no
  re-arm refund" exactly.
- Supporting: `Ledger.consume_fst`, `Ledger.consume_snd_of_ok`,
  `Ledger.consume_false_of_consumed`, `Ledger.arm_noop_of_armed`,
  `empty_ledger_consume_denied` (corollary from `Ledger.empty`).

## Manual proof entry point (SPipe manual layer)
The three headline theorems, in the MANUAL file
`KernelCapabilities/SingleUse.lean` (separate from any generated layer):
`KernelCapabilities.single_use_consume_once`,
`KernelCapabilities.unarmed_consume_denied`,
`KernelCapabilities.no_reuse_after_consume`.
Wired into the project via `import KernelCapabilities.SingleUse` in the root
`KernelCapabilities.lean` (one line added).

## HARD GATE — command run and result (verbatim)
Command:
```
cd src/verification/kernel_capabilities && lake build
```
Result (final status lines):
```
✔ [4/6] Built KernelCapabilities.SingleUse (486ms)
✔ [5/6] Built KernelCapabilities (359ms)
Build completed successfully (6 jobs).
EXIT=0
```
Toolchain: `leanprover/lean4:v4.30.0`, Lake 5.0.0. Offline — the project manifest
(`lake-manifest.json`) has `"packages": []`, so NO Mathlib fetch is required; the
model uses only core Lean 4 `List`, matching the existing sorry-free files.

Sorry/admit audit: `grep -nE 'sorry|admit' SingleUse.lean` → only match is the
word "sorry-free" in the header doc comment; zero `sorry`/`admit` tactics.
Axiom audit: `#print axioms` for all three headline theorems reports
`[propext, Quot.sound]` only — no `sorryAx`.

Post-regeneration gate (per doc/07_guide/compiler/lean_verification_workflow.md):
`simple verify check` / `simple gen-lean verify` run Lean/Lake and fail on
errors or `sorry`; the module-level `lake build` above is the equivalent direct
Lake gate and is the exact command this lane ran.

## Files changed (working copy only — NOT committed)
- NEW `src/verification/kernel_capabilities/KernelCapabilities/SingleUse.lean`
- `src/verification/kernel_capabilities/KernelCapabilities.lean` — added
  `import KernelCapabilities.SingleUse` (one line).
- `.spipe/simpleos_harden_fv_singleuse/state.md` (this file).

## Resume / re-verify command
```
cd /home/ormastes/dev/pub/simple/src/verification/kernel_capabilities && lake build
```
