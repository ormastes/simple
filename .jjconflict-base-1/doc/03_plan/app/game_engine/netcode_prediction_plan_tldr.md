# Netcode Plan — TLDR

**Slice:** deterministic virtual-clock + loopback only (no real sockets). Determinism ⇒ exact oracles.

```
P1 wire     common/net/byte_cursor.spl (ByteReader/Writer, MANDATED+missing)
            + game_net/wire.spl: InputFrame / Snapshot(delta) / TxnMsg / Ack, versioned
              │  (also un-breaks bgp/ldap/dtls/ipsec)
P2 core     game_net/{input_buffer,predictor,reconciler,server,interpolator}.spl
            client predicts N ahead ─▶ server correction ─▶ REPLAY buffered inputs (exact)
P3 txn      game_net/txn.spl: optimistic apply ─▶ accept | reject ─▶ byte-identical pre-op restore
P4 harness  game_net/{loopback,virtual_clock}.spl: seeded latency/loss/reorder, reproducible
```

**Top 3 plan items:**
1. Land `src/lib/common/net/byte_cursor.spl` (ByteReader/ByteWriter) — the missing mandated codec.
2. `game_net` core: input buffer + prediction window + **rewind-and-replay** reconciler on the
   proven fixed-step sim.
3. Transactional layer: accept/reject/cancel with byte-identical pre-op snapshot restore.

**BDD oracles (exact):** predict N ahead; correction converges to server pos within K steps
(|err|==0); dropped/reordered packets recover to loss-free baseline; rejected txn rolls back
byte-identical; two clients → identical world hash. Spec:
`test/03_system/game_net/netcode_prediction_spec.spl`.

**Out of slice:** interest management, real UDP sockets (drop-in transport swap later).
