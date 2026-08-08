# TODO — Build real live-capture infrastructure for E7 domain evidence profiles

- Status: open, not yet scoped into sub-lanes. Distinct from the untyped-evidence
  migration backlog (that is a search-and-triage problem over existing specs; this is new
  engineering to build capture drivers that don't exist yet).
- Landed foundation these lanes build on: `src/lib/common/spec/evidence/format/{terminal_grid,
  action_trace,text_protocol,binary_layout,scene_profile,simulation_profile,audio_profile,
  ml_profile,json_document}.spl` — all currently take CONSTRUCTED input, proven by unit spec,
  never a live source.
- Proven precedent for what "live" means in this codebase's typed-evidence terms:
  `src/lib/common/spec/evidence/format/exec_capture.spl` (real process, via
  `std.nogc_sync_mut.sffi.system.process_run`) and `format/file_capture.spl` (real file I/O
  via `std.io_runtime` + `std.common.crypto.sha256`).
- What remains, per domain, each its own scoped sub-lane (none started):
  - TUI: a real terminal driver feeding `terminal_grid.spl`'s `TerminalSnapshot` from an
    actually-running TUI process, not a constructed row list. Candidate integration point:
    `src.lib.nogc_sync_mut.ui_test.sgtti` / `SgttiTestDriver`, already used elsewhere in the
    repo for TUI/GUI test automation — read `doc/07_guide/infra/sspec_typed_evidence.md` §3
    and the interactive reference example
    (`test/03_system/tools/spipe/examples/interactive_surface_manual_spec.spl`) before
    starting; that example is explicitly fixture-driven today and documents this exact gap.
  - GUI action trace: same SGTTI driver, live dispatch instead of constructed
    `UiActionStep` records.
  - 2D/3D scene: a real Draw IR / Engine2D/Engine3D readback feeding `scene_profile.spl`,
    not a hand-built `DrawScene`/`Scene3D`. See `doc/07_guide/ui/rendering/backend_isolation_guide.md`
    for the facade rules this MUST go through (never touch backend/`rt_*` calls directly
    from a typed-evidence adapter).
  - Simulation: a real running simulation harness feeding `simulation_profile.spl`'s
    `TimelineEvent` stream.
  - Audio: real captured samples (file or live) feeding `audio_profile.spl`, likely via
    `file_capture.spl` composed with an audio-file decoder, once one exists in
    `src/lib/common/`.
  - ML: a real model run feeding `ml_profile.spl`'s `MlMetric`/`MlPrediction` records —
    depends on what ML runtime, if any, this repo has a facade for; needs its own research
    pass before design.
- Resume: this is NOT ready to hand to a single agent as one lane — each domain needs its
  own research pass (what real capture surface already exists in this repo per domain,
  matching the "reuse the facade, don't touch `rt_*` directly" discipline in
  `.claude/skills/spipe.md`) before a design doc can be written, the way
  `untyped_evidence_migration_design.md` was written before that lane's implementation
  started. Do not skip straight to implementation.
- Estimated scope: multi-session, likely one dedicated research+design+implement cycle per
  domain (TUI, GUI, 2D/3D, simulation, audio, ML) — not a single bounded task.
