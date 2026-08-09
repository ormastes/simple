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

## Exact Gate 1-6 sequence

Run and record these in order. Do not skip a gate or restart with a different
candidate between gates.

1. **Gate 1, Stage 3 admission:** the Stage 3 owner records the canonical pure-
   Simple build, exact identity, rejection probe, frontend admission, path, and
   SHA-256.
2. **Gate 2, x86_64 Linux Stage 4:** build the non-stub pure-Simple candidate
   from the Gate 1 lineage and retain build/progress/RSS receipts.
3. **Gate 3, candidate sanity/hash:** freeze the candidate path and SHA-256;
   record identity, provenance, no-stub/no-failure scan, sanity output, and
   unsupported-command behavior.
4. **Gate 4, essential-tools smoke:** run
   `sh scripts/check/check-bootstrap-essential-tools-smoke.shs /absolute/path/to/stage4/simple`
   and retain all four markers: test runner, lint, duplicate checker, and
   aggregate bootstrap smoke.
5. **Gate 5, deployment and rollback:** deploy only that candidate, retain the
   pre/post identities, then run the manual rollback procedure (no
   `rollback-bootstrap-deploy.shs` script exists yet: redeploy the retained
   `bin/release/<canonical-triple>/simple.pre_deploy` over the newly-deployed
   binary). Retain the rollback command, exit status, receipt path, restored
   hash, and post-rollback arithmetic smoke.
6. **Gate 6, platform acceptance/handoff:** the platform owner runs the exact
   native, QEMU, target, or scoped matrix command for the selected row and
   returns host identity, toolchain, source/compiler hashes, artifact hashes,
   logs, sanity, and essential-marker receipts.

After Gate 5, invoke the helper step named exactly
`step_bootstrap_platform_handoff_readiness`. It invokes the canonical checker,
selects the Gate 6 row, and records the handoff status. It cannot waive Gate 1-5.

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
