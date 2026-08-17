# `native_compile` fails with ERROR=1 and ZERO diagnostic, and the truncator drops the middle of the output

Status: **OPEN** — measured, unfixed. Blocks attribution of any native-build failure.
Date: 2026-08-17

## Symptom

`native_compile` failed the entry
`...trailing_default_param.main` reporting `ERROR=1` and emitting **zero bytes
of diagnostic output**. No error text, no source location, no phase name,
nothing that names what went wrong.

Compounding it: the output truncator dropped **55884 of 67884 bytes** — and it
dropped them **from the MIDDLE**, keeping a head and a tail. Whatever
attribution existed was in the discarded 82%.

## REPRODUCED 2026-08-17, independently and twice

Re-measured on a fresh unwrapped run of
`scripts/check/check-native-trailing-default-param.shs` (no `timeout` wrapper;
rc read into a variable, not through a pipe). rc=1, verdict verbatim:

```
FAIL — native-build failed to compile the fixture (exit 1, log saved to /tmp/check-native-trailing-default-param.last.log)
```

The saved log carries the defect verbatim at line 1795:

```
!!!!!! NATIVE-BUILD STDERR TRUNCATED !!!!!!
[native-build] TRUNCATED: 55780 of 67780 bytes of worker stderr were dropped from the MIDDLE.
```

and again at line 2002 as
`[stderr truncated by native-build entry: 55780 bytes omitted from the middle]`.
The bare `ERROR=1` sits at line 1782 with no accompanying diagnostic; the only
attribution reaching the reader is the unit-level
`error: build failed: 1 failed, 0 unverified, 0 not run, 1 ok of 2 unit(s) — ERROR: test.fixtures.native_trailing_default_param.main`,
which names the failing unit but not the reason.

Two things this pins down:

- **It is deterministic, not load noise.** A second lane running the same guard
  concurrently from a different worktree
  (`/mnt/data/tmp/claude-1000/wt-llvmcodegen`) produced the byte-identical
  verdict line and rc=1 — an unplanned independent replication.
- **The byte counts drift slightly** (55780/67780 here vs 55884/67884 when first
  seen). The dropped fraction is stable at ~82%. The drift is consistent with
  the discarded region containing run-varying text, which is exactly the text
  worth keeping.

Note the second truncation defect visible in the same log: the head that IS
retained is spent on repeated
`compiler_cross_module_private_symbol_collision` warnings (lines 1563-1574,
repeated again at 1798-1809 in the tail). So the surviving 18% is largely
duplicated warning noise, making the effective attribution yield lower still
than the byte ratio suggests.

## Why the truncation half is the worse defect

A build that fails is a bug. A build that fails **unattributably** is a bug
that costs days, because every lane that hits it must re-derive the cause from
scratch instead of reading it. This is the exact defect class that cost three
lanes a full day on stage 3.

Middle-truncation is specifically the wrong policy for compiler output. A
compiler's head is banner/config noise and its tail is a summary line; the
diagnostics — the only part with attribution value — are in the middle. This
truncator preserves precisely the two regions that carry no information and
discards the one that does. A head-only or tail-only truncator would have been
strictly better by accident.

Note the interaction with the empty-diagnostic half: because the failure
printed nothing, it is currently **impossible to tell** whether

1. `native_compile` genuinely produced no diagnostic, or
2. it produced one and the truncator ate it.

Those are different bugs with different fixes, and the current tooling cannot
distinguish them. That ambiguity is itself the finding.

## What is measured vs inferred

- **Measured:** `ERROR=1`; zero diagnostic bytes surfaced; 55884 of 67884 bytes
  dropped from the middle.
- **NOT verified:** the underlying compile failure's actual cause. It has never
  been observed.
- **NOT verified:** which component owns the truncator (the `native_compile`
  driver, the guard script's own capture, or a shared log helper). Locating it
  is step one of any fix.
- **NOT verified:** whether this is deterministic or load-dependent.

## Blocking impact

Any run of `scripts/check/check-native-trailing-default-param.shs` that trips
this cannot be scored. It is **not** a FAIL of the thing under test and it is
**not** a PASS — it is an unattributable build failure, and reporting it as
either would be a false claim. Report it as blocking.

This defeats the guard's own verdict contract in practice: the contract
distinguishes PASS / FAIL / ERROR precisely so an unverified run cannot be
mistaken for a real one, but a silent `ERROR=1` with no text gives the reader
nothing to act on beyond "something, somewhere".

## Fix direction (not attempted)

1. Never truncate from the middle. If output must be capped, cap the head and
   keep the tail, or write the full output to a file and print its path.
2. A nonzero exit with zero diagnostic bytes should itself be reported as an
   anomaly by whatever invokes the compiler — "the compiler failed and said
   nothing" is a statement worth printing, and is strictly more useful than
   silence.
