# Bootstrap frontend worker admission uses measured reservations

Status: source fix; next Stage 2 launch/runtime qualification pending.

## Evidence and scope

The Stage 2 cold CLI workload parses a 2,914-module closure in about nine
minutes, then reached HIR 1,526/2,914 at the 1,800-second timeout with HIR
fanout falling back to one worker. An explicit 5,000,000 KiB (about 4.8 GiB)
frontend/tree budget on that launch is below the measured worker reservation and correctly
fits zero workers. A separate prior 48 GiB run admitted six HIR workers and hit
the tree cap. Read-only process samples on the current larger closure measured
HIR workers around 8–12 GiB and parse workers around 5.9 GB; those samples are
not a controlled benchmark cohort.

PR #4650 raised the exec CLI defaults for a different measured 2,937-module
workload, but bootstrap explicitly supplied 1,650,000/3,000,000 KiB and thus
overrode those defaults. The bootstrap policy also priced fanout jobs at the
old 3,000,000 KiB HIR estimate. These are two separate reasons its prior
admission was not using the newer estimate.

## Source policy

Fanout hosts now use an 8,000,000 KiB (about 7.6 GiB) parse reservation and
12,000,000 KiB (about 11.4 GiB) HIR reservation. The existing clamp keeps 40%
of a declared tree budget for the parent and tools. At a 48 GiB cap, remaining
admission space fits at most two HIR workers or three parse workers. A
5,000,000 KiB explicit budget still fits zero HIR workers; it remains a valid
safety hint. The final compiler
worker remains separately guarded, and caller `--threads` is unchanged for
backend/codegen work.

The fanout tree RSS model is priced at 19,532 MiB per job, the rounded-up
equivalent of one 12,000,000 KiB HIR worker at 60% admission. Windows keeps its
separate one-frontend policy and existing worker/share values. The CLI uses the
measured values as fallback defaults, while the bootstrap command transcript
exports matching values explicitly and rejects competing inherited worker
estimates. The 48 GiB tree cap, host-fraction cap, explicit smaller inherited
tree cap, and process-tree watchdog remain authoritative.

## Validation boundary

Added pure clamp assertions for the 48 GiB two-HIR/three-parse fit, the 5,000,000 KiB
zero-fit case, a large-parent reserve, and the tighter cgroup cap. Shell policy
fixtures cover fanout exports, explicit smaller budgets, the unchanged Windows
policy, and preservation of ten backend threads. These source-level checks do
not establish runtime memory or speed. The next immutable candidate must rerun
the cold Stage 2 workload with the enforced 48 GiB cap and record per-phase
worker count, elapsed time, and process-tree peak RSS. No live candidate was
modified or restarted for this source change.
