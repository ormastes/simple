# Bootstrap Parallel Handoff

This is the operator contract for handing a bootstrap candidate from the x86_64
Linux lane to platform owners. Parallel work is allowed, but evidence is
lineage-bound and platform claims remain fail-closed.

## Canonical readiness checker

Run the canonical checker for the exact target triple:

```bash
sh scripts/check/check-bootstrap-platform-handoff-readiness.shs
```

The checker reads receipts; it does not manufacture evidence. It rejects stale
artifacts, seed or cross-build substitutions, missing logs, missing rollback
output, mismatched source/candidate hashes, and partial marker output. It emits
`PASS` only after all required gates and the selected platform handoff are
complete. An unavailable host is `OPEN` or `BLOCKED`, never `PASS`.

## Ownership and permitted parallel work

The Stage 3 owner may be another agent. That owner supplies the admitted Stage 3
path, SHA-256, authority/compiler identity, rejection-probe result, frontend
admission, and source revision. Stage 4 and platform agents may prepare
diagnostics, preserve caches, review receipts, and arrange external native hosts
without waiting for the Stage 3 process to finish. This is independent
preparation, not admission: no agent may claim a later gate until it has consumed
the Stage 3 receipt for the same source lineage.

The merge owner freezes the candidate and is the only agent that publishes the
combined readiness result. A final reviewer checks the frozen receipts before a
release or platform claim.

## Current x86 transaction status (2026-08-14)

Historical cycle 3 repaired two source frontiers and published Stage 2,
binary SHA-256
`e383d2c6ea86e63ba6805cf3478f723cecd673c2e141be86b3cf1150d14e9378`,
log SHA-256
`db7907064858b472ffadf3cc9527f73acfaf4e80a5f3156d203ba84b924fb167`.
At 09:52:45 host `earlyoom` sent Stage 3 SIGTERM at 41,394 MiB RSS with less
than 10% free memory and no swap; exit 143 followed 5.4 seconds later. The
empty log hashes to
`e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
That parent predates the complete `d99deb3` memory-snapshot runtime provider;
41,394 MiB is an interrupted high-water mark, not a proved completion budget.
The current authority is
`doc/08_tracking/bug/stage3_current_source_hir_rss_termination_2026-08-14.md`:
Phase 2 parser versus Phase 3 HIR retention is unresolved. TODO666 is
open/actionable: the incompatible M0 draft was reverted; existing resume-only
durable sinks remain, while safe phase publication, full-bootstrap wiring,
process/RSS/signal supervision, and provenance migration. After M0 acceptance,
build a fresh current-HEAD Stage 2 and run one instrumented Stage 3 in a fresh session. No fourth run is permitted in
this session. TODO667 remains gated.

## Exact Gate 1-7 sequence

Run and record these in order. Do not skip a gate or restart with a different
candidate between gates.

1. **Gate 1, Stage 3 admission:** after M0 acceptance, run a fresh unique-output
   current-HEAD Stage 2 plus one instrumented Stage 3; retain phase, memory,
   process-group, RSS, exact identity, rejection probe, frontend admission,
   path, manifests, and SHA-256.
2. **Gate 2, x86_64 Linux Stage 4:** build the non-stub pure-Simple candidate
   from the Gate 1 lineage and retain build/progress/RSS receipts.
3. **Gate 3, candidate sanity/hash:** freeze the candidate path and SHA-256;
   record identity, provenance, no-stub/no-failure scan, sanity output, and
   unsupported-command behavior.
4. **Gate 4, essential-tools smoke:** the canonical transaction invokes
   `check-bootstrap-essential-tools-smoke.shs` internally exactly once. Retain
   `stage4-essential-tools-smoke.log` and all four markers; do not repeat a
   standalone smoke against the same candidate.
5. **Gate 5, deployment:** deploy only that candidate and retain the pre/post
   identities. Keep this source-matched authority deployed through Gate 6
   unless TODO667 publishes an isolated immutable bundle that downstream rows
   execute directly.
6. **Gate 6, platform acceptance/handoff:** the platform owner runs the exact
   native, QEMU, target, or scoped matrix command for the selected row and
   returns host identity, toolchain, source/compiler hashes, artifact hashes,
   logs, sanity, and essential-marker receipts.
7. **Gate 7, rollback:** only after all selected Gate 6 evidence, run
   `sh scripts/bootstrap/rollback-bootstrap-deploy.shs <canonical-triple>`.
   Retain the command, exit status, receipt path, restored hash, and
   post-rollback arithmetic smoke. An earlier rollback is valid only when
   Gate 6 ran from TODO667's isolated immutable bundle. Publication of that
   bundle binding candidate, deploy receipt, pre-deploy binary, rollback
   script/receipt, downstream receipts, and hashes remains the TODO667 gap.

After Gate 7, invoke the helper step named exactly
`step_bootstrap_platform_handoff_readiness`. It invokes the canonical checker,
selects the Gate 6 row, and records the handoff status. It cannot waive or
reorder Gates 1--7.

## External native-host handoffs

Linux AArch64, macOS, Windows, and hosted RISC-V rows require their stated
native host or explicitly scoped environment. The handoff package must name the
owner, reviewer, host identity, toolchain versions, exact command, source and
compiler hashes, artifact paths and hashes, logs, sanity output, and markers.
Cross-compilation, x86 QEMU, a stale artifact, or a host that was not available
is not native-host PASS. The row remains open with its unblock condition.

## No false PASS and the three-cycle cap

`PASS` means the evidence exists for the exact candidate and every required
receipt is internally consistent. Executable existence, zero failed files,
static checks, frontier review, preparation work, or a successful unrelated
platform cannot be promoted to PASS. Missing or empty guest/native logs fail the
claim.

For a failing live run, stop at the first trustworthy boundary, preserve the
receipt, fix the pure-Simple owner, and verify a distinct root-cause cycle. The
lane has a maximum of three distinct fix/verify cycles. Do not rerun an identical
failed command; after the third cycle, stop and report the remaining blocker.
