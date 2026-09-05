# Netcode: Prediction, Reconciliation & Transactional Replication

**Status:** Research | **Domain:** app/game_engine | **Date:** 2026-07-03
**Driver:** "Unreal 6 support" = Unreal-style networking — authoritative server,
replicated state, client prediction with server rewind/correction, plus reliable
transactional ops (inventory/trade atomics).

## 1. Local Infrastructure Inventory

### engine/net (skeleton exists, stringly-typed, no rollback)
`src/lib/nogc_sync_mut/engine/net/` — 4 files, ~11 KB, dirty-tracked but naive:
- `client.spl` — `GameClient`: `input_buffer:[InputCommand]`, `state_buffer:[StateSnapshot]`,
  `prediction_enabled`, `interpolation_factor`, `local_tick`/`server_tick`. **Buffers exist
  but there is NO rewind/replay/correction logic** — `receive_state` just appends+trims.
- `server.spl` — `GameServer`: authoritative tick loop, client connect/disconnect, latency,
  `tick_rate`. No input queue, no snapshot broadcast.
- `sync.spl` — `StateSync`: per-entity `[SyncField]` with `dirty` + `last_sync_tick`, authority
  string. **Values are `text`** (no binary, no delta compression).
- `rpc.spl` — `RPCDispatcher`: register/dispatch/log, `reliable:bool` flag. Log only, no transport.

This is the Unreal-ish shape (authority + replicated fields + RPC + prediction buffers) but
un-wired: no wire codec, no reconciliation math, no transactions.

### common/net wire codec — MANDATED BUT MISSING (key finding)
`std.common.net.byte_cursor.{ByteWriter}` and `std.common.net.addr.{ip_addr_to_bytes}` are
imported by `bgp/`, `ldap/`, `dtls/`, `ipsec/` build+parse modules — but **no physical file
exists** under `src/lib/common/net/` (only `src/lib/common/serialization/__init__.spl` stub).
The sanctioned wire-codec surface has to be *created*, not just consumed. Any netcode wire
protocol should land `src/lib/common/net/byte_cursor.spl` (ByteReader/ByteWriter) as its floor,
which also un-breaks the four existing protocol modules — shared win, not net-only cost.

### Determinism foundation — PROVEN (this is the whole enabler)
- `game2d/loop/driver.spl` — `LoopDriver.consume_fixed_steps(wall_dt_ns)`: ns-based fixed-step
  accumulator, exact `100ms@60Hz → 6 fixed_update` (spec-verified).
- `game2d/time/det_guard.spl` — `#[deterministic]` mode panics `GAME-DET-001` on `time.now()`/
  `rand()` outside a callback; inside returns simulated step time. **No hidden nondeterminism.**
- `test/03_system/engine/game2d_deterministic_loop_spec.spl` and
  `test/03_system/game3d/rollball_production_spec.spl` — fixed-timestep physics **identical across
  two independent runs** (2D and 3D, `PhysicsWorld3D` = `engine/physics2/world3d.spl`).
Determinism is the precondition for rewind-and-replay and for byte-exact convergence oracles.

### Supporting infra (transport + concurrency, for later real-socket wiring)
- Transport: `net/udp.spl`, `net/tcp.spl`, `net_server/{connection,listener}.spl`,
  `os/services/netstack/` (full L3/L4: ipv4/ipv6/udp/tcp/socket). UDP path exists.
- Concurrency: `std.actors.actor` — named-handler mailbox actors (`ActorRef.send`), fits the
  per-connection / server-tick loop later. Not needed for deterministic BDD.
- `udp_utils/` empty; `common/serialization/` stub. SDN is the config/save format, not a hot
  snapshot codec (use ByteWriter for snapshots).

## 2. External Models (cited) — ranked by fit

| # | Model | Fit to Simple | Verdict |
|---|-------|---------------|---------|
| a | **Snapshot interp + client prediction + server reconciliation** (Quake/Source/Overwatch, Gambetta/Gaffer) | Matches existing `GameClient` buffers + authoritative `GameServer`; standard for action games; indie-friendly | **Core** |
| b | **Deterministic lockstep + rollback** (GGPO) | We *already have* determinism → rewind-and-replay is cheap and byte-exact | **Reuse the replay mechanism** for local reconciliation, not P2P lockstep |
| c | **Authority + replicated state + RPC** (Unreal actor replication) | `StateSync` authority string + `RPCDispatcher.reliable` already mirror this | **Layer on top** (authority tags, reliable RPC) |
| d | **Server-authoritative transactions** (client optimism + accept/reject + cancel/rollback) | Inventory/trade; not covered by (a); needs explicit 2-phase op | **Add as its own layer** |

**Chosen: (a) as the backbone, with (b)'s rewind-and-replay as the correction engine, (c)'s
authority/RPC tags layered on, and (d) as a distinct transactional op layer.**

Why not pure lockstep (b as primary): no server authority → cheat-prone, no late-join, not
"Unreal-style." But because Simple's sim is already deterministic, we *borrow* GGPO's core trick —
on a server correction, snap the owned entity to the authoritative snapshot at tick `T`, then
**replay the buffered local inputs `T+1..now`**. Determinism guarantees this converges to an exact
position, which is what makes absolute-value BDD oracles possible (a nondeterministic sim could
only assert "close").

Standard sub-mechanisms adopted: monotonic **sequence numbers + acks** on every input/snapshot,
**delta compression** (send only `dirty` `SyncField`s vs last-acked baseline — `StateSync` already
tracks `dirty`), **snapshot interpolation** for *non-owned* remote entities (buffer + lerp between
two acked snapshots; `interpolation_factor` already present), **interest management** deferred
(indie scale — broadcast-all is fine first; add relevancy when entity count demands it).

### Transactions (d)
Optimistic client op → server validates against authoritative state → `accept(seq)` commits, or
`reject(seq, reason)` → client restores the **pre-op snapshot byte-identically** (deterministic
serialize of the affected sub-state, kept until ack). Atomicity is per-op sequence; ordering by
seq. This is the inventory/trade "atomic" surface, distinct from continuous movement replication.

## 3. Recommendation

Build the smallest server-authoritative slice on a **deterministic virtual clock + loopback**
(no real sockets for BDD): wire codec on the mandated `common/net` ByteReader/ByteWriter, a
`game_net` lib module (input buffer / prediction window / rewind-replay / correction), a
transactional accept/reject/cancel layer, and a simulated latency+loss harness. Determinism +
absolute oracles (predict N ahead, converge within K steps to exact positions, dropped/reordered
recovery, rejected-txn byte-identical rollback, two-client identical world hash) — see the plan.

## Sources
- [Client-Side Prediction and Server Reconciliation — Gabriel Gambetta](https://www.gabrielgambetta.com/client-side-prediction-server-reconciliation.html)
- [Networked Physics (2004) — Gaffer On Games](https://gafferongames.com/post/networked_physics_2004/)
- [Netcode Architectures Part 2: Rollback — SnapNet](https://www.snapnet.dev/blog/netcode-architectures-part-2-rollback/)
- [Determinism, Prediction and Rollback — coherence docs](https://docs.coherence.io/manual/advanced-topics/competitive-games/determinism-prediction-rollback)
- [Choosing the right network model — Mas Bandwidth](https://mas-bandwidth.com/choosing-the-right-network-model-for-your-multiplayer-game/)
- [GGPO — Rollback Networking SDK](https://www.ggpo.net/)
