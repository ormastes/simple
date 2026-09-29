# Parallel Applications

Simple parallel code follows one default convention: the owner keeps canonical
mutable state; children read immutable input or receive explicit ownership;
children create independent results; the owner validates and commits them.

## Current contract surface

The repository now provides common vocabulary for transfer envelopes, storage
plans, access paths, parent-commit ordering, and assurance policy:

- child-created outputs are the preferred transfer direction;
- parent-owned mutable state is an explicit consuming move;
- process, remote, and device boundaries reject an ordinary owned in-memory
  region; they require an encoded/immutable handle or device lease;
- unknown dynamic ranges overlap until proven otherwise;
- external ABI/wire/MMIO storage remains pinned.

Critical policy denies implicit parent-to-child moves and dynamic transport, and
requires bounded mailboxes, deterministic commits, and frozen layout receipts.

The common commit engine now models a functional owner transition with a
constant-size final snapshot-root assignment. It first validates every result's base revision, identity, deterministic
order, and conflict policy. Only a fully valid non-empty batch advances the
revision and replaces the snapshot token. Failures return the original owner
state, and a shape-validated receipt records input/output roots plus the canonical task,
sequence, and payload-token order. The owning application adapter still builds
and verifies the candidate snapshot before supplying its token. A concurrent
runtime owner must serialize or CAS the transition against the live root; the
common value function alone is not an atomic synchronization primitive.

## Status

The common structured owner/task lifecycle, multicore-green task adapter, and
bounded actor-message adapter are implemented. This is not a claim that every
process, generic channel, or backend layout path already enforces the same
protocol. Process codecs, physical layout lowering, runtime trap catching, and
end-to-end process/device evidence remain work-package gates. Consult the
receipt and matching runtime gate before relying on a path in production.

## Recommended shape

The first concrete parent-authoritative API uses
`StructuredOwnerV1` and `RuntimeStructuredTaskGroupV1`:

```simple
var owner = StructuredOwnerV1.create(1, 0, [10, 20])
var tasks = RuntimeStructuredTaskGroupV1.create(owner.snapshot(), 2, true)
val mapped = tasks.map([11, 22], [1, 2], ParallelResultKind.Patch,
    "partition", StructuredScalarWorker.ReturnInput)
val waited = tasks.join_all()
val receipt = owner.commit(tasks.lifecycle_state(),
    ParallelCommitOrder.TaskIdThenSequence, ParallelConflictPolicy.Reject)
```

Do not use a raw pointer or unclassified dynamic object as a cross-domain
payload. Do not infer that two different index variables are disjoint.

## Current provider status

| Surface | Current status |
|---|---|
| C scalar `rt_channel_*` | fixed capacity; focused direct C evidence only |
| Rust `rt_value_channel_*` | bounded, typed inline admission, close/send locked |
| Compiler Crossbeam provider | bounded; mutable dynamic values reject |
| Object-handle capability registry | pure-Simple bounded model; runtime/process integration pending |
| Actor send/reply | explicit accepted/full/closed/invalid/cancelled result ABI |
| Common structured lifecycle | scalar result codec, bounded leases, failure receipts, deterministic atomic commit |
| Multicore-green task adapter | capability-free named scalar worker; close/free after mandatory join |
| Actor structured adapter | text adapter for the scalar wire; bounded `ActorMessage` transport remains mailbox-owned |

The canonical structured-result transport format is exactly eleven signed
scalar words in the order defined by `structured_task_wire_words`. Every word
must fit Simple's native tagged-integer interval `[-2^60, 2^60-1]`. The hosted
channel adapter carries those words through typed `rt_channel_*_i64` calls.
The actor adapter only serializes each word as one decimal `ActorMessage.args`
entry and safely parses it back; `ActorMailbox`/`ActorSend` remain the transport
owners. This is an adapter boundary, not a claim that the generic actor send
stack internally uses the channel codec or lifecycle.

Owner commit recomputes the expected snapshot and compares owner, revision,
generation, frozen token, capacity, digest, and every copied value. The digest
is diagnostic only: exact value equality prevents a hash collision from
authorizing a commit.

`RuntimeStructuredTaskGroupV1.cancel_task/cancel_all` revoke publication leases.
They do not physically preempt a running pool closure because the hosted pool
does not yet expose `rt_pool_cancel`; `join_all` always drains every handle.
The hosted pool also has no trap-catching boundary. Use the explicit
`ReportFailure` worker result for recoverable failure; an abort/panic is outside
this lifecycle and is not reported as `StructuredTaskFailureV1`.

Blocked resume command with an admitted self-hosted CLI:
`bin/simple test test/01_unit/common/structural/parallel_transport_provider_matrix_spec.spl --mode=interpreter`.
