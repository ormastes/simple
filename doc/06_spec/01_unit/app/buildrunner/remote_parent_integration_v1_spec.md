# Remote parent signed completion and journal integration V1

Status: **AWAITING_VERIFICATION** — source-authored specifications and manual.
No compiler, seed, test runner, filesystem fixture, journal, or process was
executed to qualify this artifact. No PASS or coverage claim is made.

Source: `test/01_unit/app/buildrunner/remote_parent_integration_v1_spec.spl`.
Owner under test: `src/app/buildrunner/remote_session_v1.spl`.

When executed, each scenario creates a unique secure temporary root, real source,
toolchain, policy, and task-context files; opens the existing task database and
distributed operation WAL; and releases their owner locks before deleting the
root. Reopen scenarios use journal replay rather than replacement in-memory maps.

The fixture binds the declared toolchain inventory and policy bytes into a valid
task, derives the actual environment and task request digests, independently
signs a new grant and human approval with separate deterministic fixture keys,
and signs a host completion over digests of frozen output/log/process bytes.
The fixture signature message helpers are test fixtures, not other executable
spec modules. Assertions compare independently built request/grant wire digests
with production codecs and require authority-context admission.

| Scenario | Intended executable evidence |
| --- | --- |
| Parent acceptance and replay | Accept the signed bundle, read exact binary output bytes from private parent staging, require one validated passed task row and completed operation, release and reopen both journals, then reject the same completion with `REMOTE_COMPLETION_REPLAY` without adding a row. |
| Cancellation before acceptance | Commit cancellation, release and reopen owners, reject the late signed bundle with `REMOTE_EXECUTION_CANCELLED`, retain cancelled operation state, and require an empty task history. |
| Foreign cancellation | Register a separate executing operation in the same real operation journal, reject cancelling it through this session with `REMOTE_OPERATION_NOT_OWNED`, and require both operations unchanged and no task record. |
| Inter-journal recovery | Directly perform the same validated task append that precedes the operation terminal commit, release and reopen owners, reject cancellation with `REMOTE_COMPLETION_ALREADY_COMMITTING`, accept the exact original evidence, read exact parent output bytes, retain one original task row, complete the operation, and reject another replay. |

The inter-journal scenario simulates the durable boundary with orderly lock
release and replay. It does not kill a live process or demonstrate power-loss
durability. Process identity, successful exit, and tree-reap fields are signed
fixture observations; these specs do not start a compiler, SSH host, or remote
execution owner. Real host execution and fault injection require separate
runtime qualification.
