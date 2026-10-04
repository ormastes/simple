# Provisional bootstrap omitted OS dependencies from native source snapshots

Status: orchestration repair; focused routing check provided. Full bootstrap validation pending.

The Windows LLVM Phase 2 producer built and ran hello successfully, then failed
while compiling the Phase 3 provisional authority image. Its HIR worker reported
unresolved `os.crypto.sha256`, imported by `src/lib/scv/store.spl` inside the frozen
SCV source snapshot. The native-build command supplied explicit compiler, app,
and lib roots, so the snapshot correctly excluded `src/os`.

Add `--source src/os` to provisional manager-image compilation, its argv digest
and recorded command template, and the Phase 3/4 compiler task manifests. Keep
the hello command unchanged: its restricted fixture does not use OS imports and
its existing command-receipt schema has a fixed argument layout.

The focused `scripts/bootstrap/tests/provisional-source-roots-test.shs` checks
all four production argument sites, including identity recording. This is an
orchestration regression check, not a successful compiler build or admission.
Existing sealed image receipts with the old argv identity must not be rewritten
to claim the new roots; preserve failed attempts and use normal replay rules.

Evidence: `windows-restart-20261004/pr2385-validation-managed/provisional-v1/authority-images/logs/provisional-authority.attempt1.stderr.log`.
