# BUG-BOOTSTRAP-REPEATED-RUNTIME-PIN-PREFLIGHT-20261010

Status: OPEN. Authoritative bug DB reconciliation: PENDING. No workaround or
performance change has been applied. This report concerns diagnostic bootstrap
orchestration, not a measured pure-Simple compiler hot path.

## Observed evidence

The repaired 160-entry Phase 3 request is
`709f0c4346375c68c17ac44edda91933db968b739ecdb799aa922fe1849a7afd` at
`build/native_probe/phase3-original1220-80030-20261010/chunk03/request.json`.
Each projection pins the same 382 runtime input files through hardlinks.
`run_batch.py` hashes every task's pins during coordinator preflight and hashes
them again immediately before its task launch. The preflight therefore visits
61,120 runtime paths before any compiler dispatch, in addition to source and
global pins. Git cleanliness checks are separate operations.

Before any `attempt.json` existed, Windows process counters for the live owning
controller PID 18020 showed ReadTransferCount 1,798,530,949 bytes,
KernelModeTime 764,218,750 and UserModeTime 126,562,500 (100 ns units).
These are cumulative controller counters, not a phase timer or child compiler
profile. A subsequent observation confirmed 24 task attempts had started; the
existing build was allowed to continue unchanged.

The evidence establishes repeated runtime verification in this runner and
substantial pre-dispatch I/O. It does not attribute every byte or second to
runtime hashing, establish a regression against a matched baseline, or prove
the compiler's requested 0.1-second target.

## Repair and acceptance requirements

Share verification of immutable runtime content across entries without
weakening producer, source, runtime, tool or closure identities. A digest or
mtime alone must not allow a mutable donor, replaced alias, changed dependency
or partial manifest to reuse a stale verification result. Specify identity and
lifetime guarantees before reducing reads; retain per-entry source checks and
real compile failures.

Use matched fixtures to measure preparation time, bytes read, verification
counts and peak memory. Reproduce this repeated-runtime case, and test changed
bytes, replaced hardlinks, concurrent mutation, descriptor cleanup, incomplete
manifests and cancellation. Compare memory and logic results as well as speed.
Require Astra review and verified evidence before activating or publishing an
optimization. Preserve all successful objects and original attempt records.
