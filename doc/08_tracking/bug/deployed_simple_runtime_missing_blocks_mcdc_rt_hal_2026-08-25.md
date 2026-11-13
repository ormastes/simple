# Deployed Simple Runtime Missing Blocks MC/DC/RT-HAL Implementation

Date: 2026-08-25
Status: LIVE (triaged 2026-11-11, lane work/p3-rt2-20261111 — bootstrap-deployment admission state, not a `src/runtime` defect)
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

## 2026-11-10 status — P3 runtime-lane triage (worktree simple-p3-rt-20261110)

**Verdict: LIVE, but not a `src/runtime` defect — out of this lane's reach.**
Re-confirmed still registered open (`bug_db.sdn` row; triage_20261027
residual: `keep_open` / `needs_more_evidence`). The unblock condition is
bootstrap-deployment admission state — an admitted self-hosted Stage 3/4
binary with general `check`/`test` — and nothing in the doc names a defective
runtime source. This session's lane is `src/runtime` + runtime bug docs +
evidence; there is no runtime source change that would close this, and a
≈55-minute bootstrap admission run is neither in scope nor verifiable inside
this session.

The live continuation of this blocker is owned by later, still-open
compiler/bootstrap-lane bugs: `stage3_hir_segv_compiler_driver_unit2of833_2026-09-14`,
`stage3_driver_hir_lowering_spins_after_parse_fix_2026-09-21`, and the
Stage-4 tracker `stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01`.
Flag for bookkeeping: when Stage 3/4 admission lands, this entry's acceptance
(unblock condition above) can be re-run from this doc's reproduction. No
change made; label: host-independent-source bookkeeping.

## 2026-11-11 status — P3 rt2 lane triage (worktree simple-p3-rt2-20261111)

**Verdict: LIVE — corroborated-by-prior-lane; not a `src/runtime` defect.**
Spot-check agrees with the 2026-11-10 p3-rt addendum: the unblock condition
is bootstrap-deployment admission state (an admitted self-hosted Stage 3/4
binary with general `check`/`test`), and nothing in this doc names a
defective runtime source, so there is no runtime-source change this lane
could land. No deep triage redone.

Spot-check at this lane's base (790b54f7c4fc, refreshed seed 0791c2b7f4a7):

- seed-smoke (repro): `bin/simple.exe check src/lib/common/mcdc/model.spl
  --mode=interpreter --no-cache` exit 0 (only W-STR-BRACE-001 lint noise) —
  the MC/DC contract slice parses and checks clean against current source on
  the refreshed seed. This is source-side readiness only; per the doc the
  Rust seed is not an authorized fallback for the acceptance.
- `bug_db.sdn` row still `open` (P3); triage_20261027 residual
  `keep_open` / `needs_more_evidence` unchanged.
- No admitted Stage 2/3 binary or sanity/provenance receipts under
  `build/bootstrap/` in this worktree (directory absent). The unblock
  condition remains unmet here.

Bookkeeping flag carried forward: when Stage 3/4 admission lands (tracked
by `stage3_hir_segv_compiler_driver_unit2of833_2026-09-14`,
`stage3_driver_hir_lowering_spins_after_parse_fix_2026-09-21`, and
`stage4_full_cli_unlinkable_579_unresolved_runtime_symbols_2026-09-01`),
re-run this doc's reproduction from the admitted binary. No change made;
label: host-independent-source bookkeeping.

## 2026-11-11 status — P3 rt2 lane triage (worktree simple-p3-rt2-20261111), second pass

**Verdict: LIVE — corroborated again at this lane's base (1f47eda674f1,
tracked seed 46fe8f6b6def); not a `src/runtime` defect. Status header
flipped from "partially resolved" to LIVE.** The two prior addenda
(2026-11-10 p3-rt, 2026-11-11 rt2 first pass) agree, and this lane's fresh
spot-check re-confirms their evidence rather than relying on them:

- `bug_db.sdn` (sharded DB at `doc/08_tracking/bug/bug_db.sdn:3393`) still
  registers this row `P3, open`.
- No admitted Stage 2/3/4 binary or sanity/provenance receipts: `build/bootstrap/`
  does not exist in this worktree. The unblock condition (admitted self-hosted
  Stage 3/4 with general `check`/`test`) remains unmet.
- Correction to the first-pass addendum's seed-smoke: at THIS base/seed,
  `bin/simple.exe check src/lib/common/mcdc/model.spl` does **not** pass — it
  fails HIR lowering with `missing module surface for std.common.hash.djb2` /
  `unresolved name: djb2_hash_text` (model.spl:16), even though
  `src/lib/common/hash/djb2.spl:11,25` defines and exports that symbol. This
  is a seed-side module-surface resolution gap on a single-file check, not a
  runtime-source defect; and per this doc the Rust seed is not an authorized
  fallback for the acceptance anyway. Recorded for honesty; the disposition
  is unchanged: no runtime-source change can close this row.
- Bookkeeping flag carried forward unchanged (Stage 3/4 admission tracked by
  the three named rows).

## 2026-11-13 triage (P3 misc-a lane, work/p3-misc-a-20261113)

**LIVE (confirmed)** — rt2 corroborated twice: no admitted stage2/3/4 binary or receipts in-tree; unblock condition unmet. Honest correction recorded: single-file seed check of mcdc/model.spl fails on a module-surface gap (djb2), noted as seed-side, not a runtime-source defect.
