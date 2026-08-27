# Deployed Simple Runtime Missing Blocks MC/DC/RT-HAL Implementation

Date: 2026-08-25
Status: partially resolved / Stage 4 still unavailable
Owner: bootstrap/runtime deployment

## Reproduction

From `/mnt/data/worktrees/codex-01a0272f`:

```text
bin/release/simple check src/lib/common/mcdc/model.spl
```

The wrapper reports:

```text
error: deployed Simple runtime failed its bounded identity probe:
/mnt/data/worktrees/codex-01a0272f/release/x86_64-unknown-linux-gnu/simple
```

The referenced executable does not exist. No admitted Stage 2 binary and paired
sanity/provenance receipts exist under `build/bootstrap/stage2/` either.

## Impact

The new Pure Simple contract slice cannot be parsed, checked, tested, optimized,
or benchmarked. Continuing compiler/runtime implementation without this feedback
would risk invalid Simple syntax and prevent the required same-runtime performance
evidence. The Rust bootstrap seed is explicitly not an authorized fallback.

## Unblock condition

Deploy a Pure Simple runtime at the wrapper's canonical target, or provide an
admitted Stage 2/3 binary whose exact hash, stage, provenance receipts, and
supported `check`/`test` commands satisfy the minimal-bootstrap guide. Then run
the focused contract checks once and continue the serialized implementation plan.

## Recovery attempt evidence

The canonical receipt-free recovery was attempted once with one job:

```text
sh scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap \
  --stop-after-stage2 --jobs=min --output=build/bootstrap \
  --progress=build/bootstrap/mcdc-rt-hal-stage2-progress.log
```

An initial seed compile exposed a missing private module export for the existing
dormant `dispatch_profile`; that bootstrap-only wiring defect was repaired. The
next run completed the seed and entered Pure Simple Stage 2 native compilation.
It remained CPU-active with zero stall streak and bounded tree RSS (about 268 MiB
at the final sample), but the enclosing execution session terminated it with
exit 143 after roughly 55 minutes. No Stage 2 artifact or admission receipt was
published. Preserve the incremental bootstrap cache; do not restart this exact
command in the same session.

## Resolution update

After a linear rebase onto current `origin/main`, upstream's HIR repair removed
the undeclared partial signature projection. A 16-worker continuation built and
admitted Pure Simple Stage 2:

```text
candidate_sha256=b9d252e3f9bdc6ca5a3f70360ce9e2f65f75e982350087c85474ebfd4c23cbed
stage2-sanity: pass
stage2-provenance: pure-simple
```

Stage 2 supports `native-build` but not general `check`/`test`. A focused
contract smoke compiled five modules with zero failures and executed
`mcdc-rt-hal-contracts-ok`. The admitted Stage 3 continuation reached
`hir-complete` near 2.7 GiB RSS but published no artifact or terminal receipt.
General verification still needs Stage 3/4 recovery; explicitly stage-scoped
native smokes can continue feature development.

## Current impact update

The working tree now contains the broader MIR probe expansion, dynamic aspect,
runner transport/gate, exact RT/HAL process arena, typed environment executor,
RT criticality, recoverable unwind, system specs, manuals, and performance
harness. None has been accepted as verified. Stage 2's limited `native-build`
smokes cannot establish compiler/lib checks, SPipe behavior, cross-backend
unwind, static-off binary absence, or same-fixture timing/peak-RSS/allocation
thresholds. The unblock condition remains an admitted self-hosted Stage 3/4
executable with `check` and `test`; source completeness cannot close this bug.
