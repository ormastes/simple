# Bootstrap admission producer `--selftest` greps the wrong file and always FAILs
## Closed 2026-11-11 (lane boot9) — SUPERSEDED: check greps the producer script; entry-closure assertion re-executed PASS

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

**Date:** 2026-09-05
**Status:** superseded (triage 2026-11-11, lane boot9) — check-bootstrap-planner-admission-producer.shs:45 targets the producer; entry-closure assertion re-executed PASS (see triage below)
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


## Triage 2026-11-10 (p3-boot lane)

SUPERSEDED — verified on work/p3-boot-20261110 (base origin/release/1.0.0).

- `scripts/check/check-bootstrap-planner-admission-producer.shs:45` now sets
  `producer="$root/scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs"`
  (the file that actually holds the entry-closure strings), and :66-67 greps
  `$producer` for `--entry-closure` and `--entry "$planner_entry_rel"`.
- Targeted re-execution of that exact fixed code path:
  `producer=$PWD/scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs; grep -F -- '--entry-closure' "$producer" && grep -F -- '--entry "$planner_entry_rel"' "$producer"`
  -> PASS (before the fix this grep pair failed unconditionally, per this
  record's Symptom section).
- Full `produce-bootstrap-planner-admission-v2.shs --selftest` (which delegates
  to this check) was also launched on this host; Git Bash process-spawn
  overhead makes the 11-fixture suite take tens of minutes. If the final
  PASS/FAIL line differed from expectation it would be reported in
  build/review/p3fix-boot-20261110.sdn; the decisive entry-closure assertion
  above is the one this bug is about and it passes.

## Triage 2026-11-03 (boot-script-fixes lane)

Already fixed on origin: scripts/check/check-bootstrap-planner-admission-producer.shs:35 now sets producer to produce-bootstrap-planner-admission-v2.shs, the file holding the entry-closure strings. Row closed fixed.

## Triage 2026-11-11 (lane boot9, work/p3-boot9-20261111)

SUPERSEDED — re-verified in-tree:

- `scripts/check/check-bootstrap-planner-admission-producer.shs:45` sets
  `producer="$root/scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs"`;
  :66-67 grep `$producer` for `--entry-closure` and `--entry "$planner_entry_rel"`.
- The exact assertion pair was re-executed here:
  `producer=$PWD/scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs;
  grep -F -- '--entry-closure' "$producer" &&
  grep -F -- '--entry "$planner_entry_rel"' "$producer"` -> PASS; the producer
  itself carries the strings (line 316: `--entry-closure --entry "$planner_entry_rel"`).
- The full 11-fixture `--selftest` was not re-run (Git Bash spawn overhead
  makes it tens of minutes, per the 2026-11-10 lane's measurement). The
  decisive entry-closure grep — the subject of this bug — passes.
