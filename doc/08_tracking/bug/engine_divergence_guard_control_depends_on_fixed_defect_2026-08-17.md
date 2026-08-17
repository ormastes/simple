# The engine-divergence guard's positive control is a defect that has been FIXED

- **Filed:** 2026-08-17
- **Severity:** P1 — a green guard will turn RED for a *good* reason, and will
  read as a regression to whoever sees it first
- **Status:** OPEN — needs the owning lane (W5) to re-base its control

## The collision

`test/01_unit/engine_divergence/check-engine-divergence-probes.shs:154` declares:

```
# CONTROL — must diverge (61-bit boxed-int truncation under JIT).
```

and `:120` reports

```
CONTROL BROKEN — engines agree, so the mode switch is [not live]
```

when the two engines AGREE. That is a correct and well-designed guard: it proves
the interpreter-vs-JIT mode switch is actually live before trusting any
divergence result. Its problem is the choice of control.

The control's divergence IS the 61-bit boxed-int truncation — the inline form is
`v<<3` plus a 3-bit tag, so any `|v| >= 2^60` loses its top bits. That defect was
**fixed** on 2026-08-17 by `610ce80229e` ("route i64 through the raw-to-string
bypass at all four render sites").

So: **when a seed built from that fix is deployed, the engines will agree, the
control will stop diverging, and this guard will start reporting CONTROL BROKEN.**
The guard is not wrong; its premise expired.

## Why this matters beyond one file

A guard that uses a live defect as its positive control has a hidden dependency
on that defect NOT being fixed. The failure is maximally confusing: the guard
goes red at the moment the codebase gets better, and the red text says the
harness is broken rather than "your control was fixed". Anyone triaging it
without this note will hunt a phantom regression in the mode switch.

Note also that the control value is not a literal in the `.shs` — it lives in the
probe it invokes — so grepping this file for `1152921504606846976` finds nothing
and gives a false all-clear. Verified: 0 hits in the `.shs`, while the CONTROL
comment is plainly at `:154`.

## What the owning lane should do

Pick a control that is **stable by construction**, not one that is a bug waiting
to be fixed. Candidates, in order of preference:

1. A documented, intentional engine difference that is not scheduled for repair.
2. A synthetic divergence the harness itself creates (e.g. a probe that reads
   `SIMPLE_EXECUTION_MODE` and prints it), so the control tests the mode switch
   directly rather than by proxy through a defect.
3. If a real defect must be used, assert the control by **name and bug-doc id**,
   and make the guard say "control X was fixed at <sha> — pick a new control"
   instead of "CONTROL BROKEN".

Option 2 is the honest one: the guard's actual claim is "the mode switch is
live", and that can be tested without any defect at all.

## Provenance

Found by the bootstrap-critical triage lane while working an unrelated row; the
W5 file itself was never edited by that lane. Cross-checked here before filing:
`610ce80229e` exists and is the i64 render fix; `:154` and `:120` read as quoted.
