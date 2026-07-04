# Netcode Prediction — TLDR

**Goal:** Unreal-style netcode = authoritative server + replicated state + client
prediction with server rewind/correction + transactional (inventory) atomics.

**Inventory:**
- `engine/net/` skeleton exists (client/server/sync/rpc) — right shape, but stringly-typed,
  no wire codec, **no rewind/replay/correction, no transactions**.
- `common/net` wire codec (ByteReader/ByteWriter) is **mandated but missing** — imported by
  bgp/ldap/dtls/ipsec yet no file exists; landing it is a shared win.
- **Determinism is proven** (game2d LoopDriver + det_guard, rollball 3D identical across runs) —
  this is the enabler for exact rewind-replay and absolute-value BDD oracles.

**Chosen model:** snapshot + prediction + reconciliation (a) as backbone, GGPO-style
rewind-and-replay (b) as the correction engine (cheap because sim is deterministic), Unreal
authority/RPC tags (c) layered on, server-authoritative transactions (d) as own layer.
Pure P2P lockstep rejected (no authority = cheatable, not Unreal-style).

```
 client input(seq) ──▶ SERVER (authoritative sim) ──▶ snapshot(tick,ack) ──▶ client
   │  predict now                                          │
   └─ buffer inputs T+1..now                               ▼
                                          on correction: snap owned entity to
                                          snapshot@T, REPLAY buffered inputs
                                          (deterministic ⇒ exact convergence)

 txn: client optimistic op ─▶ server validate ─▶ accept(seq) | reject ─▶ client
                                                   restores pre-op snapshot byte-identical
```

**Docs:** research `netcode_prediction.md`; plan `doc/03_plan/app/game_engine/netcode_prediction_plan.md`.
