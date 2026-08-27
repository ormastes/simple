# Structured Owner/Task Lifecycle

Requirements: REQ-PAR-005, REQ-PAR-006, REQ-PAR-008, REQ-PAR-009.

Executable source:
`test/03_system/feature/usage/structured_owner_task_lifecycle_spec.spl`.

## Operator flow

The owner copies a snapshot and creates a capacity-limited task group. A
capacity+1 map rejects before reserving or spawning anything. An accepted child
uses a reviewed `StructuredScalarWorker` operation; arbitrary functions and
closures are not accepted. The child constructs an eleven-word scalar result
record containing status, error, revision, task, sequence, region, result kind,
payload, and deterministic-key token.

Hosted task delivery uses only typed `i64` channel calls. Allocation failure is
checked. After each child terminates, the owner reads a complete record only
when the child reported successful transport, validates the live lease, then
closes and frees the channel. The slot-reuse scenario repeats this flow eighty
times, exceeding the native fixed registry size of sixty-four.

The canonical result format is the fixed eleven-word signed-scalar record.
Actor delivery is an adapter: it serializes each canonical word into one
decimal `ActorMessage` argument and safely rejects malformed text on decode.
A capacity-one `ActorMailbox` demonstrates backpressure, but the adapter does
not claim that generic `ActorSend` is integrated with the lifecycle internally.

Process delivery uses the same canonical record in a bounded `STP1` frame.
The decoder requires the version tag and exactly eleven signed-scalar fields,
caps the full frame and each scalar field, and rejects partial, extra,
oversized, or non-numeric input before the owner checks task, revision, and
live publication lease. The scenario commits one decoded result, rejects its
replay, and turns a malformed frame into a typed transport failure.

Cancellation revokes publication but still joins/frees hosted resources. A
cooperative `WorkerReportedFailure` record becomes an owner-visible
`StructuredTaskFailureV1`. Reverse completion is ordered canonically. Conflict,
stale replay, snapshot mismatch, and invalid staged regions reject without
publishing any owner value.

## Claim boundary

Cancellation is logical revocation, not physical worker preemption. The hosted
pool has no trap-catching boundary, so aborts/panics are not converted into
failure notifications. The actor adapter is same-runtime mailbox evidence. The
process adapter proves only bounded codec and owner validation; process spawn,
pipe/socket lifecycle, supervision, and trapped exits remain external work.

## Verification status (2026-08-12)

The one permitted correction run was:

`bin/simple test test/03_system/feature/usage/structured_owner_task_lifecycle_spec.spl --mode=interpreter`

It did not load this scenario. The wrapper identified its binary as the Rust
bootstrap seed, then failed while parsing the pre-existing
`src/compiler/50.mir/verification_ir.spl` (`expected Fn, found Var`). Therefore
neither the interpreter behavior nor the native shape is claimed as executed;
the implementation remains held on that external compiler prerequisite.

The final-cycle source check,
`bin/simple check src/lib/common/structural/parallel_commit/structured_lifecycle.spl`,
was also inconclusive: the repository checker was killed by its 60-second CPU
guard while compiling shared infrastructure and emitted no lifecycle-file
diagnostic. It was not rerun with a raised timeout.

## Process-codec verification status (2026-08-16)

The focused scenario was invoked from the isolated implementation worktree,
but both discovered repository runtimes identified themselves as Rust-built
bootstrap seeds. Each run was stopped and is inadmissible evidence. Static
diff/stub checks are clean; execution and lint remain blocked until an admitted
pure-Simple runtime is deployed.
