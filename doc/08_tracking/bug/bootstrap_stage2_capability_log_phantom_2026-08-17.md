# Bootstrap: warning references stage2-capability.log that was never written

- **Date:** 2026-08-17
- Status: OPEN (P3)
- Status re-verified 2026-08-17 by source inspection (triage shard 00).
- **Component:** `scripts/bootstrap/bootstrap-from-scratch.sh` (stage2 capability probe)

## Symptom
When stage2 itself failed (`stage2_status != 0` or `stage2_bin` not executable),
the capability probe block was skipped entirely — the `>"${log_dir}/stage2-capability.log"`
redirect never ran — yet the failure branch still printed:

```
warning: Stage 2 native-build capability failed; using seed for stage 4
warning: see .../stage2-capability.log
```

pointing at a file that either does not exist or is stale from a previous run.
Observed in tonight's `/mnt/data/worktrees/simple-boot-snap` bootstrap run where
stage2 exited 1 (see bootstrap_stage2_silent_exit1_empty_log_2026-08-17.md).

## Fix
1. `rm -f` the capability log before the probe so a stale log from a prior run
   can never be mistaken for current evidence.
2. In the failure branch, if the log does not exist, write a one-line
   `capability build not attempted: stage2 unusable (stage2_status=N)` into it,
   so the warned-about path always exists and states why.
