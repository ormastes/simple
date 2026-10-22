# Distributed graph parallel wave

Status: pure wave planner and focused specs drafted. The remote attempt now has callable prepare, transport and commit phases while the production graph runner remains sequential. Astra's static reviews found no remaining concrete P0/P1 in the planner or phase split. Runtime qualification remains pending under this session's exhausted self-hosted runner cap. No runtime PASS. Merge owner: Codex root.

## Owner and boundary

The durable scheduler journal remains the only mutable authority. A pure wave planner receives an immutable graph, ledger snapshot, ordered protected worker configs and one fresh attempt ID per worker. It returns value-only slots. The future process orchestrator must reopen the owner and recheck every slot before persisting admission, then run independent worker children with encoded immutable inputs. A proposed slot is not an issued attempt or accepted result.

New module: `src/app/build/scheduler/parent_graph_wave_plan_v1.spl`. Public types: `ParentGraphWaveSlotV1(worker_index, action_digest, attempt_id, retry_number)` and `ParentGraphWavePlanV1(status, reason, slots)`. Function: `plan_parent_graph_wave_v1(graph: ParentGraphRequestV1, ledger: SchedulerLedgerV1, workers: [DistBuildConfigV1], attempt_ids: [text], now_tick: i64) -> ParentGraphWavePlanV1`. Statuses are `DISPATCH`, `WAIT_ACTIVE`, `COMPLETE`, `BLOCKED`.

Validate graph, workers, ledger, attempt-ID count/uniqueness and clock before choosing. Because `graph.valid` is only a copied flag, re-admit each request/action pair and compare identity, dependencies, priority and CPU/memory/FD claims before planning. Each round calls the existing worker-specific `select_next_parent_graph_request_v1` against an evolving copied ledger, picks the globally highest effective priority with action-digest and worker-index ties, and applies `admit_attempt_v1` to the copied ledger to reserve shared CPU, memory and FD tokens. Stop at one slot per worker, 16 workers maximum for this entrypoint, or no ready action. Only accepted publications satisfy dependencies; active work does not. Existing active attempts consume tokens and busy workers. Return `WAIT_ACTIVE` if no new slot is ready while graph work is active, `COMPLETE` only if every graph action is accepted, otherwise `BLOCKED` with a reason. Never mutate the caller's ledger or publish a result.

Focused spec: `test/01_unit/app/build/scheduler/parent_graph_wave_plan_v1_spec.spl` covers two independent workers selected in one wave, dependency held until accepted, shared CPU/memory/FD capacity limiting a wave, active worker exclusion, deterministic priority and duplicate ID rejection, input-ledger immutability, historical attempt-ID reuse, unrelated active capacity, tampered request/action pairing and partial waves. An active graph attempt whose worker differs from the approved request returns `BLOCKED` rather than waiting without a recovery route. The future owner must persist each admission against the ledger containing prior wave admissions and dispatch only actual fenced attempts. `WAIT_ACTIVE` requires resume, cancellation and cleanup handling, never passive polling. This session's self-hosted Simple verification cap is exhausted, so source/spec remain unrun. Do not edit the staged `parent_graph_runner.spl` or production CLI until a qualified process launch and owner replay path is designed and tested.

## Production integration sequence

Astra's static review confirmed that `run_parent_graph_v1` still waits for each
remote attempt; the wave planner alone creates no overlap. Split the current
whole-attempt operation into serial durable preparation, bounded remote
transport, and serial parent publication. The parent must open a fresh owner
for every proposed slot, recheck capacity/retry/dependencies against all prior
admissions, persist its fence and exact request, and close the owner before
launch. A child receives an immutable bounded envelope containing only the
issued request and pinned transport identities. It may upload, invoke, confirm
status and fetch candidate bytes, but never mutate the owner journal or publish
an accepted result. The parent collects every child, then uses the existing
fenced `commit_parallel_fetched_result_v1` path in deterministic slot order.

The existing `run_parallel_remote_build_attempt_v1` cannot be called after
preparation because it would admit the same action again. Its current
owner-open timeout is 1 ms, so concurrent whole-attempt calls are also not a
safe substitute for serial preparation. A launch failure leaves a durable
active attempt that needs acknowledged cancellation or later reconciliation;
the parent must collect all launched siblings before returning. Retain each
prepared upload until its child has finished transfer and give every fetched
result an exclusive attempt directory. Refresh dependency readiness only after
accepted publication. The Simple thread API carries `Any` arguments and
returns an `i64`; it is not yet qualified to transfer candidate result graphs,
so a process/encoded-result boundary or separately verified transport is
required before the runner switches to concurrent execution.

The source-level phase split now binds the full approved SSH/SFTP node and
canonical request, upload plan and dispatch identity in the prepared value.
Transport does not delete a root supplied through that value; the parent
releases its independently retained prepared root after transport returns.
The rejection-path marker spec and other phase-boundary specs are unrun.

`parallel_transport_wire_v1.spl` now defines a separate, bounded canonical
NBAV handoff and observation codec for a future process child. The handoff
binds the request, full approved node digest, prepared batch manifests,
disjoint assigned roots and limits. An observation binds the handoff and
worker result claim, but it grants no `verified` authority. The parent still
needs an independently retained-file verifier, actual process launch/collection
and serial owner commit before the runner can use the codec. The focused codec
spec is source only and does not establish execution overlap.

The pure `parallel_retained_result_plan_v1.spl` now derives the exact sorted
result inventory from the admitted request and claimed outcome. It rejects
missing or extra files, reserved or duplicate output names, incomplete
observations, nonempty failure manifests and aggregate byte overrun before any
file read. The codec permits
131 result files: three metadata files plus the existing limit of 128 action
outputs. This is still a claim check, not trusted retention. The next Mac-side
step needs a parent-exclusive result stage, qualified child termination, and
descriptor-pinned reads of every file beneath the assigned root. Only after
byte counts and SHA-256 digests match, and the parent copy passes the existing
worker reply/output or failure-proof checks, may the parent construct a
verified fetch. On 2026-09-27, the focused native Mac
`check-runtime-file-view.shs` selfcheck passed for the beneath-root reader;
the new Simple planner/spec remain unrun under the exhausted self-hosted
verification cap.

Astra's 2026-09-27 launcher review found no currently qualified macOS
process-owner receipt that proves all writers to the child result directory
have stopped. The existing V3/V4 observation paths are Linux or leader-only
for this purpose; the repaired `posix_spawnp` path proves only direct-child
launch/reap. A Mac wave must remain unavailable until a restricted transport
child or stronger supervisor proves bounded launch, cancellation, complete
stream collection, descendant writer cessation and leader reaping. A process
group or a successful wait for one PID alone is insufficient. The process
owner should expose separate `leader_reaped`, `streams_complete`,
`writers_stopped` and `observation_decoded` facts; the verifier requires all
relevant completion facts before reading child files. Preparation must not
issue a durable production wave when that host capability is unsupported.

The handoff budget now permits the worker's 1 GiB declared-output aggregate
plus bounded result, manifest and diagnostic metadata. It still enforces
256 MiB for each retained binary file. The conditional parent verifier reads
every child file through the descriptor-pinned beneath-root view, compares
its count and SHA-256 digest, copies it into a fresh parent stage, verifies
the copy, then reuses the current success or failure proof checks before
constructing a verified fetch. This source path has no production caller and
its Simple spec remains unrun until a source-matched runtime is available.
The copy reads at most 1 MiB per chunk so a 256 MiB binary output does not
materialize as one large Simple byte array. A focused Mac native selfcheck
passed after the file-view opener was changed to reject FIFOs without blocking.

`parallel_transport_child_input_v1.spl` now validates a bounded handoff
before any network work. It requires the independently supplied parent
handoff digest, reads the prepared request, ready marker and both SFTP batches
through pinned beneath-root file views, reconstructs the canonical upload
plan and control commands, and hashes every declared prepared input in
1 MiB chunks with no-follow ancestor traversal. This rejects substituted
batches and symlinked input ancestors. A source-only child runner now uses
this validator, obtains its own fetch stage, and publishes a Mac result root,
outputs directory, and final observation with no-replace operations. The
Mac directory publication native selfcheck passed; the Simple runner is
unwired and its only focused spec checks malformed input before network work.
Existing SFTP later reopens paths, so the prepared bundle must stay frozen
through transfer or use a pinned transfer mechanism. The downloader now has
limited success/failure entry points and checks handoff output budgets before
object transfer; the pure budget spec remains unrun. The child now uses one
bounded physical `/usr/bin/find` to claim an exact flat result inventory and
rejects extra entries before pinned file hashing. The Mac command fixtures
passed, but the Simple inventory spec is unrun and the command path's cost
remains unmeasured. Before a production caller exists, define deadline ticks
and prove child writer cessation. These conditions and a positive fixture
remain in Linux TODO 346.

Merge owner: Codex root. Sidecar: Astra architecture review. Final reviewer:
highest-capability independent review after the bounded transport and replay
path exist. Gate: a source-matched self-hosted runtime and two scoped Linux
workers must show overlapping attempts, failure recovery, dependency bytes,
and serial publication before any speedup or production PASS is claimed.
