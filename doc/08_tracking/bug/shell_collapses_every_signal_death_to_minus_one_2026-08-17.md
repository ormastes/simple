# `shell()` collapses every signal death to -1, so CRASHED and TERMINATED are indistinguishable

Date: 2026-08-17
Status: OPEN
Site: `src/lib/nogc_sync_mut/io/process_ops.spl` — `shell()`
Found by: the poisoned-fixture lane while building
`test/01_unit/compiler/driver/build_supervisor_poisoned_fixture_spec.spl`

## The defect

`shell()` returns **-1 for every signal death**. SIGSEGV (11), SIGKILL (9) and
SIGTERM (15) are all indistinguishable through that channel. Measured, not
inferred: children killed with `kill -SEGV $$` and `kill -KILL $$` both surface
as -1, as does a SIGTERM.

## Why this is load-bearing, not cosmetic

This destroys exactly the distinction the supervised-build work exists to make.
`src/compiler/80.driver/driver_build/build_outcome.spl` classifies a unit's fate
into six disjoint categories, and the single most important boundary in it is:

- **CRASHED** (139 SIGSEGV / 137 SIGKILL) — a real compiler defect, a FAILURE.
- **TERMINATED** (143 SIGTERM) — **UNVERIFIED, never a failure.**

That boundary is not theoretical on this host. `earlyoom` runs
`--prefer ^(simple|rustc|cc1|...) --avoid ^(claude|codex|...)` and is actively
SIGTERMing `simple` (confirmed firing at 08:37: "sending SIGTERM to process ...
simple: badness 984, VmRSS 3488 MiB"; host 125 GB total, ~108 used, **zero
swap**). The agent always survives and its evidence-gathering child dies. That
is why infrastructure failure on this box presents as a compiler-shaped bug —
and three separate wrong root causes were reached that way today.

A supervisor that reads its child's status through `shell()` therefore **cannot
tell a compiler segfault from an earlyoom kill**. It will either call every
earlyoom SIGTERM a compiler crash (manufacturing phantom compiler bugs, the
exact failure mode `build_outcome.spl` was written to prevent) or call every
real segfault unverified (silently losing genuine defects). Both directions are
wrong, and `-1` gives the caller no way to choose correctly.

## Current workaround (in the specs, not a fix)

Both supervised-build specs wrap the command so POSIX 128+N is restored:

```
sh -c '<cmd>'; rc=$?; exit $rc
```

`test/01_unit/compiler/driver/build_supervisor_status_channel_fidelity_spec.spl`
pins this with a discriminating control: the WRAPPED channel passes the
fidelity contract, and the RAW `shell()` channel is asserted to FAIL it. So the
defect is currently fenced by a test, not repaired.

## Fix direction

`shell()` should preserve the child's wait status so callers can decode
128+N — either by returning the raw status, or by exposing a sibling that does.
`build_outcome_classify_status(status, timed_out)` already decodes it correctly
and needs no change; the only thing missing is a channel that does not throw the
information away.

Note the adjacent rule this shares a root with: **never read an exit status
through a pipe** — `cmd | tail` yields `tail`'s status. Both are cases of the
real status being replaced by something that merely looks like one. A supervisor
must read the child's wait status DIRECTLY into a variable on the line after the
invocation.

## Related

- `doc/02_requirements/compiler/supervised_builder.md` — R2 (disjoint
  categories), R5 (death attribution)
- `src/compiler/80.driver/driver_build/build_outcome.spl` — the vocabulary this
  defect undermines
- `.spipe/supervised-crash-safe-build/state.md` — feature state
