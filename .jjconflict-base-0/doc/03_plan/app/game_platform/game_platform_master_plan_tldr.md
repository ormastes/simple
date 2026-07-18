# Game Platform Master Plan — TLDR

Six research lanes (opus/sonnet/haiku, fable-reviewed) → one phased plan.
Full doc: `game_platform_master_plan.md` (per-lane docs linked there).

Verified: engine is large but games bypass it (breakout hand-rolls AABB);
`common/net/byte_cursor` imported by 4 modules but missing; zero encoders
(PNG/WAV) repo-wide; 5 physics specs broken on `RawHandle.new()`; physics2/
is dead (0 callers); determinism already proven (rollback enabler).

```
P0 repair+foundations   P1 extraction        P2 tool CLIs        P3 netcode
├─ fix RawHandle specs  ├─ pixel oracles →   ├─ spritesheet      ├─ wire frames
├─ delete physics2/     │  game2d/3d libs    ├─ simple sound     ├─ predict+rewind
├─ byte_cursor.spl ─────┼─ breakout → engine ├─ model3d gen      ├─ transactions
├─ png_encode.spl ──────┤  physics + CCD     │  (seeded noise)   └─ loopback harness
└─ wav_encode.spl       └─ specs stay green  └─ SDN everywhere
```

Deferred (YAGNI, recorded): WFC/L-systems/marching-cubes, tracker sequencer,
GUI editors, real sockets/interest management, GPU solver.

Every phase lands via SSpec BDD with absolute oracles (known-answer noise
values, byte-identical renders, analytic collision results, convergence-to-
server-state positions); scenario outlines live in each lane plan.
