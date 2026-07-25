# Plan: Netcode Prediction, Reconciliation & Transactions

**Status:** Plan | **Domain:** app/game_engine | **Date:** 2026-07-03
**Research:** `doc/01_research/app/game_engine/netcode_prediction.md`
**Principle:** deterministic virtual clock + loopback only — NO real sockets for the production
slice. Determinism (already proven) gives absolute-value oracles; sockets are a later transport swap.

## Smallest Production Slice

### P1 — Wire protocol on the mandated ByteReader/ByteWriter
Land the missing codec surface first (also un-breaks bgp/ldap/dtls/ipsec):
- `src/lib/common/net/byte_cursor.spl` — `ByteWriter`/`ByteReader`: `write_u8/u16/u32/i32/f32`,
  varint, `write_bytes`; symmetric reads. Little-endian, versioned.
- `src/lib/nogc_sync_mut/game_net/wire.spl` — versioned frame codecs:
  `InputFrame{seq, tick, move_x/y/z}`, `Snapshot{tick, ack_input_seq, [EntityState]}` with
  **delta mode** (only `dirty` fields vs last-acked baseline), `TxnMsg{op_seq, kind, payload}`,
  `Ack{last_seq}`. Header: `proto_ver:u16` + `msg_kind:u8`. Round-trip is byte-identical.

### P2 — game_net core: prediction window + rewind-and-replay
`src/lib/nogc_sync_mut/game_net/` (new module; reuse `engine/net` structs where typed):
- `input_buffer.spl` — ring of `InputFrame` keyed by seq/tick; ack trims acknowledged.
- `predictor.spl` — client: apply local input immediately, advance predicted tick N ahead of
  last server tick; keep `[predicted_state]` per tick.
- `reconciler.spl` — on `Snapshot@T`: set owned entity to authoritative state, **replay buffered
  inputs T+1..now** through the same fixed-step sim (`game2d/loop` step fn). Deterministic ⇒ exact.
- `server.spl` — extend `engine/net/GameServer`: per-client input queue, authoritative
  `fixed_update`, broadcast delta snapshots + ack. `interpolator.spl` — remote (non-owned)
  entities: buffer 2 acked snapshots, lerp by `interpolation_factor` (no prediction).

### P3 — Transactional op layer (accept/reject/cancel)
`src/lib/nogc_sync_mut/game_net/txn.spl`:
- Client: `begin(op)` → serialize affected sub-state to a **pre-op snapshot** (ByteWriter),
  apply optimistically, mark `pending(op_seq)`.
- Server: validate vs authoritative state → `accept(op_seq)` (commit) | `reject(op_seq, reason)`.
- Client on accept: drop snapshot. On reject/timeout: `ByteReader`-restore pre-op snapshot —
  **byte-identical** to before the op. Ordering by `op_seq`; atomic per op.

### P4 — Deterministic loopback + latency/loss harness (BDD spine)
`src/lib/nogc_sync_mut/game_net/loopback.spl` + `virtual_clock.spl`:
- In-memory transport: `send(bytes)` enqueues with a scheduled delivery tick; virtual clock
  advances deterministically. Knobs: fixed/variable latency, drop-rate, reorder — all seeded,
  reproducible. No OS sockets. Real UDP (`net/udp.spl`, netstack) is a drop-in transport swap later.

## BDD (SSpec) — absolute oracles

`test/03_system/game_net/netcode_prediction_spec.spl`:
```
describe "Netcode: client prediction + server reconciliation":
  it "client predicts N steps ahead of last server tick"        # local_tick == server_tick + N (exact)
  it "server correction converges to server state within K steps"# after replay: pos == server pos, |err|==0
  it "un-corrected steady state stays byte-identical (no jitter)"# negative control: no snapshot ⇒ no change
describe "Netcode: lossy channel recovery":
  it "dropped input frame recovered via next ack + replay"      # final pos == loss-free baseline
  it "reordered snapshots apply by tick, older ignored"         # state == newest-tick state
describe "Netcode: transactional inventory op":
  it "accepted op commits authoritative state"                  # server + client agree, exact
  it "rejected op rolls client back byte-identical to pre-op"   # ByteWriter(before) == ByteWriter(after reject)
  it "cancel before ack restores pre-op snapshot"               # same byte-identity oracle
describe "Netcode: two-client convergence":
  it "two clients converge to identical world hash"             # hash(worldA) == hash(worldB) after M ticks
```
Oracles are exact (positions, byte-identity, world hash) because the sim is deterministic.
Wire round-trip test: `encode(frame)` then `decode` equals original for every msg kind + delta mode.

## Sequencing & Risk
1. **P1 first** — codec is the floor and repays 4 broken modules. 2. **P2** — needs P1 + the
existing fixed-step `game2d/loop` step fn (verify the step fn is callable standalone for replay).
3. **P3/P4** in parallel after P2. Risk: `f32` snapshot exact-equality across replay — mitigated by
determinism proof (rollball already asserts identical runs); keep snapshot values integer/fixed
where feasible for hash stability. Interest management + real sockets are **out of this slice**
(indie scale: broadcast-all first).
