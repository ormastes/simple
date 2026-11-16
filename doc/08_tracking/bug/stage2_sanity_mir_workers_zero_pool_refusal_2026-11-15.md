# Stage2 sanity smoke: mir_workers=0 makes the per-file worker pool refuse every build (2026-11-15)

**Status:** OPEN (worked around via SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1; root cause in the
shard-count forwarding for smoke builds)
**Area:** src/app/cli/file_worker_pool_refusal.spl + stage2 candidate_frontend_smoke harness

## Symptom

At pin 70d542b8ab3 (carries 9cfdcb0c195 shard-count forwarding + 5f80235594b serial
low-memory MIR sharding), every stage2 lane's sanity smoke
(`candidate_frontend_smoke: p2_add-build`) fails:

```
error: per-file worker pool refused (hir_workers=4 mir_workers=0, need >= 2):
not enough free memory for 2 workers. Free memory=69534052 kB, per-worker budget=9000000 kB
```

The memory figure is a red herring (69 GB free, needs 30 GB). The real trigger is
`mir_workers=0`: file_worker_pool_refusal_v1 refuses whenever
`min(hir_count, mir_parallel) <= 1`, and the smoke build's MIR shard count resolves to
0. Setting SIMPLE_MIR_SHARD_COUNT=8 in the lane env did NOT reach the smoke build
(harness resets or does not forward it).

## Workaround (used by the K3 lane, works)

`SIMPLE_BOOTSTRAP_WHOLE_PROGRAM=1` -- the error text's own sanctioned escape hatch;
routes the smoke build single-process, bypassing the pool admission. Stage2 then
completes and admits normally.

## Proper fix direction

Forward the MIR shard count (or default it to >= 2) inside the candidate_frontend_smoke
build invocation, or make the pool refusal treat mir_workers=0 as "no MIR sharding
requested" and admit on the HIR lane alone when memory allows.
