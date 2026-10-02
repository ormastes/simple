# Canonical managed failure continuation

Status: source fix implemented; native qualification pending.

`bootstrap-phase4-grouped.shs` previously wrapped each phase in one subshell.
Its helpers called `die` for every nonzero manager result, skipping independent
binaries, indexes and the other backend after the first failed compile. The
grouped native manager itself already traversed eligible independent groups.

The wrapper now retains an outcome for each independently scheduled task and
continues only typed ordinary compiler failures. Index failure blocks its own
module group. Infrastructure failure stops the owner; no incomplete execution
can reach the completion publisher. The scheduler regression exercises mixed
binary/index/group failures, all twenty-eight outcomes including six suites, signals, owner markers and
success. It passed once on Git Bash on 2026-10-02.

The old generic manager also returned 1 for launch rejection and collapsed
worker timeout/cancellation/resource failures. The compiled fix reserves 1 for
an actual reaped `ERROR/1` result and checks retained failure receipts on resume.
Generic and grouped deterministic failures no longer retry unchanged inputs;
the managed default is one attempt. New policy and state-replay unit specs are
authored but UNRUN until an admitted runtime is available. This is not a native
manager PASS or release verification PASS.

Deployment requires new admitted source. `prepare-phase2-build-manager.shs`
compares the entire manager source snapshot with the Stage 2 admission source;
the frozen 7734 candidate cannot authorize these changed manager source bytes.
The existing frozen checkout, cache and receipts are preserved.
