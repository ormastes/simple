# core-C capsule gate is opted out of guard wiring on a false rationale

- **Date:** 2026-08-06
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Component:** `scripts/check/guard_wiring_optout.txt`, `scripts/check/build-core-c-bootstrap-runtime-capsule.shs`

## Symptom

`scripts/check/build-core-c-bootstrap-runtime-capsule.shs` sat RED at
`origin/main` in a clean tree with no automated lane reporting it. It failed at
the contract-symbol assertion and never reached the four selfchecks after it
(transient-heap, and three mem-guard selfchecks), which therefore reported
nothing and were indistinguishable from passing. The gate bug itself is fixed
in `13bd6f7ce596de4f9cdec2f716b1a84cf1a47270`; this entry is about why the RED
persisted unnoticed.

## Root cause

`scripts/check/guard_wiring_optout.txt:22` reads:

```
build-core-c-bootstrap-runtime-capsule.shs  hardware/emulator lane; needs QEMU, an FPGA or a physical dev board
```

`scripts/check/check-guard-wiring.shs` consumes this file (lines 158-164) to
suppress the requirement that a guard be wired into an automated lane. So the
gate is exempt from wiring, and nothing runs it.

The stated rationale is factually wrong. The producer invokes only the host
`cc`, `ar`, `nm` and links C selfchecks — its own header says it "intentionally
invokes only the host C compiler, archiver, nm, and the C self-check". It was
run four times to completion on a plain `x86_64` Linux host with no QEMU, no
FPGA and no dev board, each run finishing in roughly two minutes and reporting
`core_c_runtime_capsule_checks_executed=28`.

## Fix

Remove the `build-core-c-bootstrap-runtime-capsule.shs` line from
`guard_wiring_optout.txt` and wire the gate into a general-purpose CI lane. Note
`check-guard-wiring.shs` also fails on a stale entry, so the removal and the
wiring must land together.

Not done here: rewiring belongs to the owner of the guard-wiring lane, and is
outside the minimal diff of the gate fix.

## Lane J re-verification 2026-08-17 (classified by CONTENT, not SHA ancestry)

**Verdict: STILL-OPEN (reproduced by content).** `scripts/check/guard_wiring_optout.txt:22`
still reads `build-core-c-bootstrap-runtime-capsule.shs  hardware/emulator lane; needs QEMU,
an FPGA or a physical dev board`. Deliberately NOT edited: removing the entry makes
`check-guard-wiring.shs` FAIL (the guard is genuinely unwired), so the correct fix is to wire
the capsule gate into a caller first and then drop the line — an ordering this lane could not
complete without touching guard-wiring files owned by the wiring backlog.
