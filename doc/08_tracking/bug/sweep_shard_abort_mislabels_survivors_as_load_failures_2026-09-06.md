# Sweep shard abort mislabels its surviving specs as load failures

**Status:** OPEN
**Filed:** 2026-09-06
**Component:** `scripts/check/check-plan-acceptance-swept.shs`

## Symptom

Measured full run (jobs=8, `PLAN_ACCEPTANCE_RUNNER` = fresh debug seed,
`SIMPLE_MCDC_MODE=off`), wall **1029s**:

```
FAIL — 36 spec(s) executed, 44 failed to load/run or neutralise cleanly
plan_acceptance_specs_attempted=36
plan_acceptance_specs_loaded_and_ran=32
plan_acceptance_in_development_tagged=36
```

The 44 offenders split as:

| class | n | real? |
|---|---|---|
| `crashed rc=124` (300s timeout) | 4 | yes |
| `load-failure-neutralised:<spec>` | 15 | yes — SKIP marker fired but the file's own verdict shows `executed=0` |
| `load-failure-neutralised:<spec>(no-marker)` | 21 | **no — collateral** |

## Defect

Three of the eight neutralisation-sweep shards aborted mid-sweep:

```
plan_acceptance_neutralisation_sweep_shard=1 rc=124 specs=5
plan_acceptance_neutralisation_sweep_shard=5 rc=42  specs=4
plan_acceptance_neutralisation_sweep_shard=7 rc=3   specs=4
```

A shard that dies emits no `IN-DEVELOPMENT SKIP` / `UNEXPECTED PASS` marker for
the specs it had not reached yet. The per-spec classifier
(`check-plan-acceptance-swept.shs:948`) sees neither marker and files each one
as `load-failure-neutralised:<spec>(no-marker)`. Those specs were never run at
all — several of them load and run fine in the per-spec pass above
(`plan_acceptance_specs_loaded_and_ran=32`), so the label contradicts evidence
the same run already produced.

Fail-closed is the right default here: a tagged spec with no marker must not be
counted as a clean skip. The defect is the **label**, not the verdict — the
offender list names 21 specs as if each had its own load failure, which sends a
reader chasing 21 nonexistent bugs instead of 3 shard aborts.

## Fix

Read `$WORK/shard.$_sk/rc` before classifying. When the owning shard's rc is
non-zero, report the survivors under a distinct label
(`shard-aborted:<shard>:<spec>`) and report the shard abort itself once, as its
own offender. Still FAIL — the sweep did not complete — but say what actually
happened.

Not fixed in the change that found it: the timing run was the last measurement
of this arc, and re-running the gate to validate a classifier change costs
another ~17 min.

## Related

- `doc/08_tracking/bug/mcdc_default_on_diverts_interpreter_runs_to_native_2026-09-05.md`
- `doc/08_tracking/bug/three_simple_binary_env_var_names_silent_wrong_verdict_2026-09-06.md`
