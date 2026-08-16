# Scheduler-owned actor channel authority

> Status: authored manual mirror. The executable and typed oracle are source
> complete, but native execution, pure-Simple doc generation, and maintenance
> remain blocked by the deployed Stage-4 test ABI probe.

## At a glance

| Item | Value |
|---|---|
| Executable source | `test/03_system/feature/language/actor_channel_authority_spec.spl` |
| Audience | Actor-runtime maintainers and verification operators |
| Boundary | Same-thread copied `ActorRef` operations through one scheduler-owned registry |
| Evidence schema | Closed `actor-channel-authority/v1` typed evidence |
| Requirements | REQ-PAR-002, REQ-PAR-006, NFR-PAR-002, NFR-PAR-003 |
| Current verdict | Source authored; Stage-4 execution/docgen/maintenance blocked |

## Purpose and limitations

This scenario demonstrates the narrow scalar-text compatibility contract that
is implemented today: one `ActorScheduler` owns registry, mailbox admission,
reply reservations, dispatch, and terminal removal. Copies of `ActorRef` retain
that scheduler authority. It does not claim a synchronized cross-thread command
ingress, typed heap/graph payload transport, or C/interpreter provider parity.

## Preconditions

1. Run from the repository root with an admitted pure-Simple Stage-4 test
   surface and `SIMPLE_LIB=src`.
2. Never substitute `src/compiler_rust/target/bootstrap/simple` as acceptance
   evidence.
3. Preserve the five primary step labels and the closed evidence schema.

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

## Typed observation and oracle

The closed `actor-channel-authority/v1` evidence records mailbox high-water,
reply capacity/value/credit, first and second stop results, and late send/ask
results. An independently declared eight-check `OracleSpec` compares those
fields with fixed expected values. Direct assertions remain in the scenario;
the observation is never converted into its own expected string.

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

The current deployed runtime fails its bounded test ABI probe before either
spec runs. Consequently this authored mirror has no accepted generated digest,
provenance manifest, folded executable block, seven-score result, or native
verdict. The Rust seed is forbidden as a substitute.

## Failure diagnostics

| Symptom | Meaning |
|---|---|
| Second send succeeds | Mailbox backpressure or copied-reference routing regressed |
| Reply is `after` | Admission-time argument copying regressed |
| Outstanding replies remain one | Reply consumption did not release scheduler credit |
| Second stop succeeds | Terminal scheduler removal is not unique |
| Unknown reference accepts work | Registry authority failed closed |

## Related artifacts

- Requirements: `doc/02_requirements/feature/parallel_ownership_memory_layout.md`
- Architecture: `doc/04_architecture/language/parallel_ownership_model.md`
- Detail design: `doc/05_design/language/concurrency/parent_commit_parallel_apps.md`
- Test plan: `doc/03_plan/sys_test/actor_channel_authority.md`
- Developer guide: `doc/07_guide/language/parallel_apps.md`
