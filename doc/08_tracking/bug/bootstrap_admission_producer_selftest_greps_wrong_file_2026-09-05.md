# Bootstrap admission producer `--selftest` greps the wrong file and always FAILs
## Closed 2026-09-16 — ...own selftest is red on every host. ## Fix Point the entry-closure grep at the producer scr

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Date:** 2026-09-05
**Status:** open
**Area:** scripts/check (bootstrap admission gate)

## Symptom

```
$ sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs --selftest
FAIL — producer does not constrain the planner build to its entry closure
```

The producer script does pass `--entry-closure --entry "$planner_source"`
(`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs:210`), so the
verdict is false.

## Root cause

`scripts/check/check-bootstrap-planner-admission-producer.shs:26` sets

```sh
producer="$root/scripts/bootstrap/bootstrap-from-scratch.sh"
```

but the entry-closure assertion at `:46-50` greps `$producer` for the
`--entry-closure` / `--entry "$planner_source"` strings, which live only in
`scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs`. The check
reads the wrong script and fails unconditionally, before any of the fixture
cases run — so the fixture cases (typed-reason refusal, permissive shim, etc.)
have not executed on this path either.

`produce-bootstrap-planner-admission-v2.shs --selftest` delegates to this
check (`:71-74`), so the producer's own selftest is red on every host.

## Fix

Point the entry-closure grep at the producer script (or introduce a separate
`admission_producer` variable) and keep `$producer` for the gate script if
other assertions need it. Verify with the selftest going PASS and with a
mutation (drop `--entry-closure` from the producer) going FAIL.

## Evidence

Observed on macOS arm64, HEAD `7c292922592`, while running the adhoc
bootstrap chain (stage2 trust root -> admission producer -> stage4 relink).

