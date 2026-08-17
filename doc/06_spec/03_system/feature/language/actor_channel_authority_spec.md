# Scheduler-owned actor channel authority

> Status: authored manual mirror. The executable and typed oracle are source
> complete, but native execution, pure-Simple doc generation, and maintenance
> remain blocked because the admitted Stage-2 compiler has no qualified
> self-hosted test/docgen/maintenance surface.

## At a glance

| Item | Value |
|---|---|
| Executable source | `test/03_system/feature/language/actor_channel_authority_spec.spl` |
| Audience | Actor-runtime maintainers and verification operators |
| Boundary | Copied `ActorRef` operations and fail-closed owner-domain guards through one scheduler-owned registry |
| Evidence schema | Closed `actor-channel-authority/v1` and `actor-owner-domain-rejection/v1` typed evidence |
| Requirements | REQ-PAR-002, REQ-PAR-006, NFR-PAR-002, NFR-PAR-003 |
| Current verdict | Source authored; qualified self-hosted execution/docgen/maintenance unavailable |

## Purpose and limitations

This scenario demonstrates the narrow scalar-text compatibility contract that
is implemented today: one `ActorScheduler` owns registry, mailbox admission,
reply reservations, dispatch, and terminal removal. Copies of `ActorRef` retain
that scheduler authority. A supporting scenario deterministically changes the
recorded owner identity after populating scheduler state and proves that every
public query/reply-lifecycle operation fails closed and preserves that state.
This is guard-branch evidence, not a synchronized cross-thread command ingress,
typed heap/graph payload transport, or C/interpreter provider-parity claim.

## Preconditions

1. Run from the repository root with a qualified pure-Simple self-hosted test
   surface and `SIMPLE_LIB=src`.
2. Never substitute `src/compiler_rust/target/bootstrap/simple` as acceptance
   evidence.
3. Preserve the five primary step labels, three owner-domain step labels, and
   both closed evidence schemas.

## Operator workflow

### 1. Create one scheduler-owned bounded actor channel

Create a scheduler with one reply reservation and an actor with a one-message
mailbox. The actor ID and configured reply capacity must be positive and finite.

### 2. Admit copied arguments through one actor reference

Submit an ask using `original`, mutate the caller's argument array, and query
pending work through `copied`. Both references route to the same scheduler; the
admitted message retains `before`, not the later caller mutation `after`.

### 3. Observe finite mailbox and reply backpressure

While the first ask occupies both finite resources, a second send and ask must
fail. The mailbox high-water mark and outstanding reply count must each be one.

### 4. Dispatch and consume the isolated result

Run the scheduler to idle, consume `before`, and verify the reply credit returns
to zero. The copied reference must observe no pending message.

### 5. Stop once through the owning scheduler

The first copied reference removes the actor successfully. A second stop, late
send, late ask, and pending-work query all fail closed without recreating work.

## Supporting error scenario

An `ActorRef` with an ID absent from the scheduler must reject send, ask, query,
and stop while retaining zero reply reservations.

## Owner-domain rejection scenario

### 1. Seed reply actor pending-message and error state in the owner domain

Create one actor, retain one completed reply, leave one message pending, and
record one dispatch error. These non-empty sentinels prevent zero/nil guard
results from passing vacuously.

### 2. Reject every query and reply lifecycle operation outside the owner domain

Inject an owner-identity mismatch. Reply lookup/consume return nil, cancellation
returns false, numeric queries return zero, error text is empty, and stats
returns the explicit unavailable sentinel. No operation may expose or release
the seeded state.

### 3. Restore owner authority and prove rejected access changed no retained state

Restore the captured creator identity and observe the original reply, finite
capacity, actor, pending message, and error record. Then release the reply once.

## Typed observation and oracle

The closed `actor-channel-authority/v1` evidence records mailbox high-water,
reply capacity/value/credit, first and second stop results, and late send/ask
results. An independently declared eight-check `OracleSpec` compares those
fields with fixed expected values. The closed
`actor-owner-domain-rejection/v1` evidence independently compares ten hidden
and restored observations. Direct assertions remain in both scenarios; neither
observation is converted into its own expected string.

## Commands, provenance, and scorecard

Intended execution:

```sh
SIMPLE_LIB=src bin/release/simple test test/03_system/feature/language/actor_channel_authority_spec.spl --mode=native
```

Intended generation and maintenance:

```sh
bin/release/simple spipe-docgen test/03_system/feature/language/actor_channel_authority_spec.spl --output doc/06_spec --no-index
bin/release/simple sspec-maintain scan test/03_system/feature/language/actor_channel_authority_spec.spl
```

The admitted Stage-2 binary supplies compiler/bootstrap commands, not the
qualified self-hosted test/docgen/maintenance surface required here.
Consequently this authored mirror has no accepted generated digest, provenance
manifest, folded executable block, seven-score result, or native verdict. The
Rust seed is forbidden as a substitute.

## Failure diagnostics

| Symptom | Meaning |
|---|---|
| Second send succeeds | Mailbox backpressure or copied-reference routing regressed |
| Reply is `after` | Admission-time argument copying regressed |
| Outstanding replies remain one | Reply consumption did not release scheduler credit |
| Second stop succeeds | Terminal scheduler removal is not unique |
| Unknown reference accepts work | Registry authority failed closed |
| Off-domain query exposes seeded values | Scheduler owner-domain guard regressed |
| Restored reply/message/error is missing | Rejected off-domain access mutated state |

## Related artifacts

- Requirements: `doc/02_requirements/feature/parallel_ownership_memory_layout.md`
- Architecture: `doc/04_architecture/language/parallel_ownership_model.md`
- Detail design: `doc/05_design/language/concurrency/parent_commit_parallel_apps.md`
- Test plan: `doc/03_plan/sys_test/actor_channel_authority.md`
- Developer guide: `doc/07_guide/language/parallel_apps.md`
