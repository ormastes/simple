# P2 todo_db rows falsified: self-binding, QUIC send queue, ALPN extraction

Date: 2026-08-18. Lane: P2 sweep (worktree `p2-sweep`, seed `bin/simple`).

Three distinct P2 TODOs (21 `todo_db.sdn` rows after mirror-tree duplication)
were verified against BEHAVIOUR, not just the cited marker. All three cited
file:line sites carry **no TODO/FIXME marker at all**, and the strings do not
occur anywhere under `src/`.

## Row 19 / 53 / 109 / 168 / 368 / 431 / 500 — "Interpreter loses the `self` binding when a struct"

Cited: `src/lib/gc_async_mut/gpu/engine2d/backend_metal.spl:1304` (no marker).

**Does not reproduce.** Probed seven `self`-propagation shapes on the
interpreter: method-to-method chain, lambda closed over the receiver, `for`
over a self field, `match` arms, `self` passed to a free function, three-level
`me` dispatch, and class-receiver mutation through nested `me` calls. All
produce the correct values.

Evidence pinned as `test/01_unit/language/struct_self_binding_propagation_spec.spl`:

```
Results: 8 total, 8 passed, 0 failed
```

Scanner proven non-vacuous by mutation (`level1()` expectation 12 -> 99):

```
Results: 8 total, 7 passed, 1 failed
```

Verdict: premise wrong; rows closed as `done`. If a real `self`-loss shape
exists it is narrower than anything reachable from the row text, which is
truncated in the db and preserved nowhere else in the tree.

## Row 20 / 54 / 110 / 169 / 369 / 432 / 501 — "wire transport-level send queue"

Cited: `src/lib/nogc_async_mut/io/quic/quic_server.spl:288` (no marker).

**Superseded by design.** `quic_server.spl:137-140` now documents the opposite
decision explicitly: "Outbound packets are not queued here: QuicTransport
.on_udp_data sends each SendPacket action inline via rt_io_udp_send_to as it is
produced, so a datagram is on the wire before poll() returns."
`quic_udp_transport.spl:7,30` states the same for the socket path. There is no
send queue to wire because inline send replaced it. Rows closed as `done`.

## Row 28 / 62 / 118 / 177 / 377 / 440 / 509 — "extract ALPN from handshake state when ALPN is implemented"

Cited: `src/lib/nogc_async_mut/http_server/worker.spl:348` (no marker).

**Precondition satisfied; work done.** ALPN is implemented and extracted:
`worker.spl:349` calls `self.dispatch_by_alpn(state.alpn, client_fd, now)` with
the handshake-negotiated value, and `dispatch_by_alpn` (`worker.spl:1016`)
routes via `protocol_from_alpn` to the H1/H2 paths. Rows closed as `done`.

## Not closed

- Row 556 (native function-local `use` maps last-wins) could NOT be reproduced
  on this host: function-local `use` is not supported on the interpreter path at
  all (`error[E1002]: function 'value' not found`), and the claim is about the
  Rust native-project import map, which needs a seed rebuild this lane is
  forbidden to do. Left open with this note.
- Rows 542 and 547 are architectural migration items with no reproducible RED;
  left open.
