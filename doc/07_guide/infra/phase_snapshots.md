# Phase snapshots (2026-08-17)
Immutable per-phase binaries with lineage-encoded names so later phases never
crash when an agent's fix changes the live tree/binary hash.

Naming: phase1_<t1>/            — seed binary snapshot taken at epoch t1
        phase1_<t1>_phase2_<t2>/ — stage binary built BY phase1_<t1>, snapped at t2
        ..._phase3_<t3>/         — full lineage; each dir holds `simple` (+ .a if needed)

Rules:
- A snapshot is copied ONCE at phase completion and never overwritten.
- Phase N+1 builds/tests/tool-builds run against an explicit snapshot path,
  never bin/simple and never the in-place stage output (those get replaced).
- A new fix landing = a NEW generation (new t1); running phase2/3 tasks keep
  their old lineage until they finish, then next round uses the newest.
