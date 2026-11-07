# Canonical private credential owner

Status: **AUTHORED_UNRUN**. No compilation, native prevention selfcheck, Simple test or platform qualification has run.

Simple source: `test/01_unit/lib/retained_private_credential_v1_spec.spl`.
Native prevention source: `test/01_unit/runtime/retained_private_credential_v1_test.c`.

The pure scenario rejects unknown lifecycle codes and distinguishes unsupported, stale generation and consumed-close diagnostics. The ownership scenario requires an actual fresh mode-0600/current-UID regular initial credential selected by `RETAINED_PRIVATE_CREDENTIAL_TEST_PATH`, beneath a mode-0700/current-UID final directory with trusted non-writable ancestry (root-owned sticky ancestor exception). Initial bytes must be exactly a 32-character lowercase-hex nonce, one space, an ASCII token of 1–128 characters, and optionally one LF. No ready sibling may already exist. Missing capability or provisioning fails, never skips.

The scenario opens and reads through the canonical native owner, publishes an immutable five-field sibling with one LF, refuses duplicate publication, closes, then obtains a fresh actual generation. A copied old token must not close the successor. The successor's read must still match the initial bytes, and a second native publisher must refuse the retained ready winner. All acquired tokens are retained globally before failures; failed acquisition with a token is closed once. No raw descriptor is exposed or restored from serialized data.

The test's loopback port 1 is protocol validation data only. No listening socket, readiness, attachment, process identity, grant or server acceptance is claimed. Ready records remain immutable after close; external fixture administration owns eventual fixture directory removal.

The native prevention selfcheck uses real Linux private files and kernel no-replace publication. It checks copied generations, duplicate publication, fork rejection, mode and actual foreign-UID rejection, symlink, unwritten FIFO and writable-ancestor refusal, directory rename anchoring, final content/permissions, and separate exec-process competing publishers. FIFO acquisition must return without a writer; a blocking-open regression hits the failing watchdog. It requires an isolated privileged Linux fixture for the actual foreign-UID case and fails its precondition otherwise. A 20-second watchdog bounds the selfcheck.

Its close fault injection performs the real OS close, then reports EINTR once. This tests consumed-descriptor error handling and proves a later copied close cannot affect an unrelated reused descriptor. It is not a simulated successful native operation or evidence that a particular kernel close failure occurred naturally. The uncertain token remains queryable; descriptor effects are never retried.

The native selfcheck's default mode and explicit `--privileged` require an
isolated UID-0 Linux fixture and retain the actual foreign-UID ownership test.
Without that fixture they fail precondition with exit 1; no elevation is
attempted. Explicit `--unprivileged` runs all other assertions unchanged,
including real filesystem/mode, copied generation, fork, FIFO, consumed-close,
anchored rename, private final content and competing exec-process publication.
Its successful output says `unprivileged subset PASS` and separately
`foreign-UID BLOCKED: requires isolated privileged fixture`. That subset's
exit 0 never qualifies the missing UID case or the privileged full fixture.
Unknown mode arguments fail usage. Both modes retain the watchdog.

Both modes remain **AUTHORED_UNRUN** in this source checkpoint; no new runtime
PASS is recorded here.
