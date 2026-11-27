# push-private-import-baseline overruns the 900 s push budget under load

- id: push_private_import_baseline_gate_overruns_budget_2026_11_07
- severity: P2 (perf)
- status: fix-implemented-verification-pending (fix #7695)
- gate: `push-private-import-baseline` (`config/check/must_check_gates.sdn:74`,
  dispatch `scripts/check/check-push-must-pass.shs:698-701`,
  script `scripts/check/check-private-import-baseline.shs --base <range base>`)

## Symptom

On a loaded Windows host this blocking push gate does not finish within the
900 s budget (`MUST_CHECK_PUSH_BUDGET_S=900`). The dispatcher then reports the
verdict as unknown (exit 2) and refuses the push. Every push is blocked,
including ones that touch no import (here: a 3-file MIR change).

## Evidence (2026-11-07, branch work/mir-tuple-binder-followup, 1 commit, 3 files)

Two consecutive pushes, same result:

```
push-must-check: gate push-text-encoding exit=0 923825ms (parallel batch, budget 900000ms)
push-must-check: ERROR — blocking gate push-private-import-baseline overran the 900s push budget; 11 blocking gate(s) ran in 928710ms, verdict unknown (exit 2)

push-must-check: gate push-text-encoding exit=0 921738ms (parallel batch, budget 900000ms)
push-must-check: ERROR — blocking gate push-private-import-baseline overran the 900s push budget; 11 blocking gate(s) ran in 930887ms, verdict unknown (exit 2)
```

Gates that finished in the same batch, for comparison: push-conflict-tree
24-38 s, push-tree-size 290 s, push-conflict-markers 300 s,
push-lib-common-no-os-import 283-410 s, push-runtime-api-regression 289-417 s.
The host default budget is 60 s (dispatcher NOTE), so this gate is more than
15x over the default.

Third push with the coordinator-approved `MUST_CHECK_PUSH_BUDGET_S=1800 MUST_CHECK_REMOTE_QUERY_TIMEOUT_S=60`:

```
push-must-check: ERROR — blocking gate push-private-import-baseline overran the 1800s push budget; 11 blocking gate(s) ran in 1818320ms, verdict unknown (exit 2)
```

Every other gate in that batch finished in 173-175 s, so this gate most likely hangs rather than scaling with load. The 1800 s workaround does not work either.

## Expected

The gate is diff-scoped like the other push-tier rows: a push that changes no
`use`/import line finishes in seconds (content-keyed cache or early exit on
an import-free diff).

## Workaround

None known: `MUST_CHECK_PUSH_BUDGET_S=1800 MUST_CHECK_REMOTE_QUERY_TIMEOUT_S=60` (the
stage2 lane setting) also overran.

## Fix

Fixed by #7695 (87f8292417f): the gate now takes about 8 s.
