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
  error/failure. The Rust native provider exports `rt_actor_try_send`, which
  returns `1` only after bounded admission and returns `0` for invalid,
  heap/reserved, full, or disconnected cases. It also exports cooperative
  `rt_actor_stop`, which closes the retained inbox senders and preserves join
  cleanup. Its first stop removes scheduler mailbox admission, wakes a blocked
  receive, preserves a joinable worker, and makes `rt_actor_is_alive` false;
  later stops return `0`. Stop is cooperative and does not forcibly interrupt
  a handler already executing outside receive. The legacy `rt_actor_send` ABI
  remains as a void compatibility wrapper around try-send, so callers using
  that symbol still cannot observe backpressure.
- Simple `ActorRef.send`, `ask`, `stop`, and pending-work queries now route
  through their admitting `ActorScheduler`. The scheduler has an explicit
  single-OS-thread domain guard: copied references used outside that domain
  fail closed; they are not advertised as cross-thread synchronized handles.
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
  framing. The Simple runtime has bounded `SPRF1` piped stdout ingress,
  generation/replay admission, parent-issued fresh session generation,
  cancellation revocation of retained frames, natural-exit reap receipts, and
  one recorded close attempt across repeated close. Stdin request framing,
  collision-resistant session identity/PID-reuse proof, codec/schema
  registration, ObjectRef transport, and critical receipt identity remain.
- Checked try-send/stop is currently supplied by the hosted Rust provider and
  wired to Simple native `ActorRef.stop`; there is no C actor provider.
  Interpreter/provider parity and checked-send adoption by legacy generated
  callers remain open. The void compatibility send still discards the checked
  result.
- Mailbox locking plus a domain guard does not make the single-threaded
  scheduler ready/reply state a cross-thread synchronization primitive.
- No graph codec or ownership registry exists yet.
- See `doc/08_tracking/bug/parallel_runtime_raw_value_transport_2026-08-12.md`.
- Session-identity collision/PID reuse and provider cleanup parity are tracked
  in
  `doc/08_tracking/bug/process_transfer_session_replay_identity_2026-08-12.md`.

The focused process evidence source and authored manual are
`test/03_system/feature/language/parent_commit_piped_result_spec.spl` and
`doc/06_spec/03_system/feature/language/parent_commit_piped_result_spec.md`.
They remain execution/docgen blocked until an admitted pure-Simple staged
runtime supplies the native, `spipe-docgen`, and `sspec-maintain` verdicts.

Update this page together with the common transfer contract, native packet
schema, actor/channel queue semantics, public concurrency guide, and the active
work-package status.
