# BuildRunner collection omitted immutable task identity

Status: fixed in source; diagnostic red/green verified; native runner qualification OPEN.

`builder_transport_collect_v1` validates task name, attempt number and host,
but omitted the receipt's `identity_digest`. A receipt from a different
immutable task could therefore pass collection when those three fields and
output hashes matched. The manager's later task validation prevents final
admission, but collection must reject before output transfer or inspection.

The defect is in the pure-Simple transport owner. No runtime change is needed.
The focused `transport_identity_spec.spl` includes a stale receipt with valid
output bytes, a stale receipt whose output is missing (identity rejection must
precede output inspection), a stale failed receipt with no outputs, and a
matching positive control. Native SSH transfer
is not exercised by these local fixtures.

## Verification

The unchanged four-case fixture ran against the explicit Rust diagnostic runner
(`SIMPLE_TEST_RUNNER_RUST=1`), bounded to 90 seconds plus 5 seconds cleanup.
Before the fix: 1 passed, 3 failed, exit 1. After the fix: 4 passed, 0 failed,
exit 0. The missing-output case checked the identity error rather than merely
any failure. Seed SHA-256:
`59de8c475ac8e364ebbd082d080e435a7aaffb4606d8fbc276a5372dcb3f87e6`.
Local logs: `/private/tmp/lunar-buildrunner-transport-identity-red-seed.log`
and `/private/tmp/lunar-buildrunner-transport-identity-green-seed.log`.

The deployed pure-Simple interpreter route crashed with exit 139 before these
examples (invalid array handle / probable compiler-FFI ABI mismatch). Its log
is `/private/tmp/lunar-buildrunner-transport-identity-red.log`. This diagnostic
seed result does not qualify that deployed executable or strict Darwin V4.
Native qualification owner: bootstrap/runtime lane; unblock with a source-matched
qualified runner and rerun this fixture. Generated manual verification remains
blocked on that runtime; the checked-in manual is explicitly authored.

Reproduction command from the isolated worktree (both red and green):

```sh
TMPDIR=/private/tmp/lunar-transport-identity-tmp SIMPLE_LIB=src \
SIMPLE_TEST_RUNNER_RUST=1 SIMPLE_NO_BOOTSTRAP_DELEGATE=1 \
sh scripts/bootstrap/run-process-group-timeout.shs 90 5 \
/Users/ormastes/simple/bin/simple test \
  test/01_unit/app/bootstrap_builder/transport_identity_spec.spl \
  --no-session-daemon --mode=interpreter --no-db --no-cache --assert-ran
```
