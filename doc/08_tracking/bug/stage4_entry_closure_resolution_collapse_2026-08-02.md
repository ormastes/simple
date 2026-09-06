# Stage 4 entry-closure facade provenance collapse

- **Status:** FIXED (focused; Stage 4 verification pending)
- **Owner:** `codex-stage4-bootstrap-close`
- **Found:** 2026-08-02, x86_64 Stage 4 phase 3
- **Area:** pure-Simple HIR module-surface resolution

Stage 4 reported 1,713 unresolved names/types across 234 files after HIR
finalization. Definitions such as `time_now_unix_micros`, `SdnValue`, `Symbol`,
`Span`, and `GpuBarrierScope` existed and had been parsed. Generated package
facades recorded plain exports without source-module provenance, while the
declarations lived in direct package siblings. The legacy resolver could chase
explicit, aliased, and glob re-exports but not an undeclared plain facade
export; duplicate `src/std` and `src/lib` surfaces also made the flat-global
fallback intentionally ambiguous.

`ModuleSurface` now retains compact export origins. Every surface-construction
boundary runs a deterministic post-build resolver using a package/name owner
index: facade-local declarations shadow siblings, one physical sibling wins,
and multiple physical owners fail closed. HIR re-export lookup consumes this
provenance before its legacy bounded chase.

Exact plain function/type and adjacent direct-shadow, explicit/alias/glob,
physical-alias, and ambiguity coverage passed in the focused HIR specs. Full
Stage 4 remains a separate verification gate.
