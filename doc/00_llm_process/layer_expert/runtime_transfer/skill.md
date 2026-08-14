# Runtime Transfer Layer Expert

## Boundary

This layer turns compiler-approved transfer facts into validated runtime
packets and bounded transport. It does not infer sendability, prove graph
disconnection, choose storage layout, or commit canonical application state.

## Canonical contract

`src/lib/common/structural/transfer/transfer_codec.spl` owns the public wire
contract. `src/compiler_rust/runtime/src/value/transfer.rs` is its native
implementation, not a competing schema.

The v1 metadata is exactly 40 bytes:

```text
SPTR | version/reserved | region/generation | domains/mode/payload |
ownership token | source-invalidated/reserved
```

The native inline packet appends eight payload bytes and uses the fixed-size
`Message::TransferPacket([u8; 48])` actor representation. Only known inline
RuntimeValue tags are admitted. Heap addresses and reserved tags are rejected.

`src/compiler_rust/runtime/src/value/process_transfer.rs` owns the native
encoded-copy process frame. It appends a bounded payload length, stable
corruption checksum, and at most 4 MiB of codec bytes to the same 40-byte
metadata. Decoding requires the expected destination domain. It is framing,
not a graph serializer or authenticated remote protocol. V1 admits only
`Parent -> Process` input and `Process -> Parent` result routes.

## Queue and actor rules

- Native compatibility channels and actor inbox/outbox queues have capacity
  256 until typed policy-selected constructors land.
- Channel and common actor-handle full/closed/disconnected sends return an
  error/failure. The legacy native actor send ABI is void and cannot surface
  backpressure yet; do not claim checked actor delivery from that API.
- Actor reply provenance is `Actor -> Parent`; ordinary external send is
  `Parent -> Actor`. The legacy generic channel is temporarily admitted only
  as `Parent -> Thread` because it lacks endpoint-role metadata.
- Heap actor construction context is unsupported and rejected until an owned
  or encoded context packet exists.

## Known blockers

- Common `Message::Value` remains an interpreter string-copy compatibility
  path; native RuntimeValue actor messages use typed packets.
- Raw channel close/free ownership still needs synchronized quiescence before
  concurrent lifecycle safety can be claimed.
- A real forked test proves encoded parent-to-process and process-to-parent
  framing. The Simple runtime now has bounded `SPRF1` piped stdout ingress,
  generation/replay admission, and a one-handle session with idempotent explicit
  close. Stdin request framing, parent-issued freshness, codec/schema
  registration, ObjectRef transport, cancellation revocation, natural-exit
  reap, and critical receipts remain.
- `ActorRef.send()` still bypasses scheduler admission, and native
  `rt_actor_send` discards full/closed failure. Mailbox locking does not make
  the single-threaded scheduler ready/reply state safe across copied refs.
- No graph codec or ownership registry exists yet.
- See `doc/08_tracking/bug/parallel_runtime_raw_value_transport_2026-08-12.md`.
- Session freshness, PID reuse, cancellation revocation, and terminal child
  cleanup are tracked in
  `doc/08_tracking/bug/process_transfer_session_replay_identity_2026-08-12.md`.

Update this page together with the common transfer contract, native packet
schema, actor/channel queue semantics, public concurrency guide, and the active
work-package status.
