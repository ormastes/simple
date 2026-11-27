# BuildRunner drops earlier recovered attempts after a later recovery failure

Status: fixed in source; focused Phase 1 interpreter diagnostic only.
Baseline: macOS staging `3e69ba212c5`.

The manager restores RUNNING journal entries in manifest order. After one or
more successful transport recoveries, a later recovery error returned exit 2
without cancelling the attempts already attached to this manager. Their
journal reservations survived, but the manager omitted its normal bounded
cleanup request before dropping the recovered handles. This could leave those
workers running after an infrastructure-abort exit.

The error branch now invokes the existing cancellation owner for every earlier
recovered attempt and reports whether cleanup was confirmed. It preserves the
original journal, does not retry any task, does not release a slot and does not
claim the unknown worker retired. A failed cancellation therefore retains the
same recovery authority as before. Cancellation uses the existing per-attempt
bounds; no new aggregate cleanup deadline is introduced.

## Regression and evidence

`test/01_unit/app/buildrunner/partial_recovery_cleanup_spec.spl` invokes the
production locked manager loop with a counting process port. Its three reserved
attempts have distinct outputs. The first two are recoverable through exact
terminal receipts and capacity settlement; the last has no receipt or fresh
ownership challenge. The test requires exit 2, no dispatch, an identity-bound
cancel request for each recovered attempt, byte-identical retained journal and
all three reservations still RUNNING on decode. The existing locked-loop
function is exported as a direct test seam; its behavior and arguments are
otherwise unchanged.

The first two fixture attempts are already terminal: this proves the recovery
error path requests cleanup for every recovered handle, not that real live
workers or descendants are contained or retired. The fixture's existing
`windows-job-settled` disposition is synthetic transport evidence in this pure
manager test; it does not claim a Windows or Darwin native job was created.

Producer: retained Phase 1 generation
`aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b`
under `/Users/ormastes/wt/release-bootstrap-integration-20261025/src/compiler_rust/target/bootstrap.generations/`.
Run from the staging source with `SIMPLE_LIB=src <producer>/simple test
test/01_unit/app/buildrunner/partial_recovery_cleanup_spec.spl
--mode=interpreter --assert-ran --no-cache --no-db --no-session-daemon
--sequential`.

- Before the cleanup change: 1 total, 0 passed, 1 failed at the missing control
  request assertion; `/tmp/buildrunner-partial-recovery-focused-red.log`.
- After: 1 total, 1 passed, 0 failed; the diagnostic reports
  `recovered cleanup=true`; `/tmp/buildrunner-partial-recovery-green.log`.
- Working direct-environment guard and whitespace validation passed.

The initial investigation tried the existing failure-dispatch suite, but its
compatibility import no longer exports the locked loop and its three tasks
share one output, now rejected by run validation. A temporary correction to
those fixture problems reached four macOS launch cases, which then failed
before the counting spawn operation with `cannot make staged producer
executable`. The new recovery case also failed at the expected missing cleanup
assertion. Evidence is `/tmp/buildrunner-partial-recovery-red.log`. Those
unrelated fixture edits were reverted; the old suite remains unqualified and
needs a separate repair of its import, output declarations and restored
UNRESOLVED status expectation, plus investigation of the chmod process path.

No Phase 2 compiler was rebuilt. Native BuildRunner Hello, Darwin V4 process
group admission and full compiler/lib/MCP runtime checks remain unverified.
No process capability or containment guard was changed.
