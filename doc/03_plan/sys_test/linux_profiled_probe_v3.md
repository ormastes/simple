# System test plan: Linux CPU profiled probe V3

## Acceptance target

Exercise one installed Linux workspace through the actual common owner: exact
profile selection, bounded Create/Start, provider CLI output capture, combined
evidence, once-only Wait/Logs guards, native cleanup, cohort absence, and
same-writer settlement.

## Registered spec

`test/03_system/lib/container/linux_profiled_probe_v3_spec.spl`

Fixture inputs are explicit administrator-installed template/request files
and an actual provider name. Missing prerequisites fail immediately. Each
returned common owner is retained before inspecting result fields. The spec
does not fabricate native owners, grants, output, or evidence.

Every poll loop has one absolute monotonic deadline per operation, at most
65,536 turns, and a `sleep_ms(1)` yield between pending turns. The collector's
original deadline remains unchanged, and its returned cursor is retained
before diagnostics. Expiry or clock failure leaves both actual owners retained
for explicit continuation/cancellation; it never auto-closes or settles.

## Evidence boundary

The test and mirrored manual are `AUTHORED_NOT_RUN`. The fixture is CPU-only
and does not claim GPU, mount, or grant behavior. The public receipt has no
direct primary-session mode field, so a separate no-session assertion is not
claimed. Cancellation after a partial prefix and injected native errors are
`NOT_COVERED` until a genuine controllable native fixture exists.

## Manual evidence

`doc/06_spec/03_system/lib/container/linux_profiled_probe_v3_spec.md` records
the fixture contract, step flow, and unrun status. It is hand-authored, not
generated SPipe evidence. No compiler, test runner, runtime, native process,
or provisioning action was run in this authoring task.
