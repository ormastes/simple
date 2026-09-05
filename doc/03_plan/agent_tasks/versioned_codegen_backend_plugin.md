# Versioned backend plugin agent tasks

<!-- codex-design -->

- Lane A: common ABI/session/receipt contracts.
- Lane B: LLVM built-in adapter and equivalence fixtures.
- Lane C: Cranelift built-in adapter and Phase 3 symbol closure.
- Lane D: checked dynamic loader and negative admission fixtures.
- Lane E: driver/interpreter migration, defaults, CLI projection, cache keys.
- Lane F: system tests, performance/RSS evidence, SFFI and direct-access audit.

Shared names and test helpers are fixed by the design documents before lane
work begins. Lower-model sidecars: N/A for ABI or merge decisions; optional only
for read-only call-site inventory. Merge owner: primary implementation agent.
Final reviewer: best available normal/highest-capability agent, independent of
implementation lanes.

