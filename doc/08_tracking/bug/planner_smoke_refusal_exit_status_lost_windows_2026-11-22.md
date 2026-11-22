# Planner smoke refusal read as acceptance; out-of-band MSVC planner build fell to gnu lane (2026-11-22)

Status: FIXED (producer hardening, this change). The planner binary's exit-status
loss itself remains OPEN: see "Open follow-up".

Ledger: W19 in `C:/dev/simple-release-boot-20261122/build/rboot/WORKAROUNDS.md`
(Windows 11 MSVC lane, release `8dae652711e`).

## Symptom

1. In-run Stage 2 -> Stage 3 receipt step
   (`bootstrap-from-scratch.sh --produce-stage3-receipt=...`, invoking
   `scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`): the negative
   smoke transcript (46 bytes, CRLF) was exactly
   `bootstrap-policy-error: typed-reason-required`, yet the producer failed with
   `bootstrap-admission-error: planner-smoke-accepted-untyped-reason`, i.e. it
   read exit 0. A later run of the same source exited 2
   (`planner-smoke.txt`: `untyped-reason-exit: 2`).
2. Out of band with only `LIB`/`INCLUDE` exported the producer failed
   `planner-build-failed` (rc=64); with the full
   `scripts/setup/windows-msvc-bootstrap-env.shs` sourced it produced the receipt.

## Root cause

1. The status read is direct: `produce-bootstrap-planner-admission-v2.shs`
   smoke exec ends `>"$stage/smoke.out" 2>&1 || smoke_rc=$?` (no pipe, tee or
   subshell), and the caller `bootstrap-from-scratch.sh:5791` is
   `if ! env ... sh producer`. So the 0 came from the planner process as built
   in that run, not from the wrapper. The producer then trusted status alone,
   so a refusal printed in words was reported as acceptance, the opposite of
   what the planner said. The failing run's `planner-smoke-accepted.out` and
   binary were removed by the out-of-band rerun (`rm -rf -- "$adm_dir"`), so the
   exact binary cannot be inspected now.
2. The planner build picks the Windows ABI from `SIMPLE_LINKER_FLAVOR` /
   `SIMPLE_WINDOWS_ABI` and defaults to llvm-mingw (gnu) when both are unset
   (`src/compiler/70.backend/backend/llvm_target.spl:37-42`,
   `runtime_compiler.spl:120-125`). `LIB`/`INCLUDE` carry neither, so the
   out-of-band build ran on the gnu lane against an MSVC Stage 2 runtime
   authority. `windows-msvc-bootstrap-env.shs:288-312` already documents the
   same class (2026-09-03). Taken from the code and that earlier measurement;
   it was not re-measured today because the resource rule forbids native
   builds while the Stage 3 lane runs.

## Fix

- Producer smoke: the refusal text is authoritative too. An anchored match of
  `^bootstrap-policy-error: typed-reason-required[[:space:]]*$` (the
  `[[:space:]]` covers CRLF) counts as refused whatever the status. A note goes
  to stderr when the two disagree. `planner-smoke.txt` records the real exit
  status plus `untyped-reason-refusal-text: yes|no`. The
  `planner-smoke-wrote-receipt-on-refusal` check stays unconditional, so a text
  refusal that still wrote a receipt is never admitted.
- Producer MSVC lane: for a parent under `stage2/*-windows-msvc/`, if either
  selector is not `msvc`, the producer sources
  `<root>/scripts/setup/windows-msvc-bootstrap-env.shs` (stdout sent to stderr)
  and then requires both. Failures name the cause:
  `msvc-lane-env-script-missing`, `msvc-lane-env-unavailable`,
  `msvc-lane-env-missing-SIMPLE_WINDOWS_ABI`,
  `msvc-lane-env-missing-SIMPLE_LINKER_FLAVOR`. When both are already set (the
  in-run path) nothing is sourced.

## Specs

`sh scripts/check/check-bootstrap-planner-admission-producer.shs --windows-smoke-env-only`
(also part of the full run):

- reproducing: a `refuse-exit0` planner shim prints the refusal (CRLF), exits 0
  and writes no receipt. The old producer reported
  `planner-smoke-accepted-untyped-reason`; the new one admits the planner and
  records `untyped-reason-exit: 0`.
- generalization: the `refuse-exit0-receipt` shim must still FAIL with
  `planner-smoke-wrote-receipt-on-refusal`. Three MSVC-triple fixtures with the
  selectors unset: no env script -> `msvc-lane-env-script-missing`; a script
  that sets only the ABI -> `msvc-lane-env-missing-SIMPLE_LINKER_FLAVOR`; a
  complete script -> PASS, and the fixture compiler records `msvc:msvc`. The
  existing `permissive` shim stays refused.

## Open follow-up

Why the in-run planner binary exited 0 after printing a refusal is unexplained.
`main() -> i64` returns 2 on that path (`src/app/cli/bootstrap_reason_planner.spl:75-76`).
Rebuild the planner in-run with the full lane env and compare its exit status
under `env -i` once the running Stage 3 lane has finished.
