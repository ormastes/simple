# `shared` Parameter Lowers As Undeclared LLVM Global
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Symptom

During a full pure-Simple bootstrap, Stage 2 native-build failed for the HIP
and OpenCL backend contract modules with:

`llvm global load referenced undeclared symbol Shared`

Both failures used `shared` as a local and parameter name, then read fields
from that parameter. Renaming the binding to `contract` allows compilation to
proceed without changing behavior.

## Expected

Lowercase local and parameter bindings named `shared` must remain local SSA
values during LLVM lowering. They must not be canonicalized into a global or
variant symbol named `Shared`.

## Reproduction

Run the full bootstrap native-build over a module containing a typed parameter
named `shared` followed by a field read such as `shared.source`.

## Follow-up

Add a focused LLVM-lowering regression and fix name classification so local
bindings take precedence over global/variant canonicalization.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
