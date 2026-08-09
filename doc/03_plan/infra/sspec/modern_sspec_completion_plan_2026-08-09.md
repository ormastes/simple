# Modern SSpec — Completion Plan & Design for Remaining Gaps (2026-08-09)

Written after a goal-audit ("is the sspec plan really done, any gap or hidden
mocking?") run 2026-08-09 against origin/main. Companion to the wave plan
(`modern_sspec_parallel_agents_plan.md`) — that doc records what landed; this
one designs what remains.

## Audit verdict

**Core implementation: done and re-verified.** All E0–E9 modules exist on
origin/main; docgen's evidence loader is wired into `generator.spl`; the live
regeneration gate passes (`check-spipe-docgen-regeneration-live: PASS — 4
example(s) checked, 0 failed`); core proof specs re-run green on the pushed
bytes (`typed_evidence_oracle_spec` 28/28, `terminal_grid_spec` 21/21,
`exec_capture_spec` 6/6 with real processes).

**No hidden mocking found — but a large honest fixture surface remains.**
Every fixture-driven artifact is explicitly labeled as such (honesty notes in
the reference manuals, docstrings in the adapters). The gap is not deception;
it is that live capture exists for only a sliver of the system:

| Path | Input source | Status |
|---|---|---|
| `exec_capture.spl` | real process (`process_run`) | LIVE, 6 examples |
| `file_capture.spl` | real file I/O + sha256 | LIVE, 7 examples |
| `live_terminal_capture_spec.spl` | real subprocess stdout → `TerminalSnapshot` | LIVE (first slice, 2026-08-09) |
| 30 migrated legacy specs | real captures via `untyped_capture.spl` | LIVE |
| `terminal_grid` (interactive), `action_trace`, `scene_profile`, `simulation_profile`, `audio_profile`, `ml_profile`, `json_document`, `text_protocol`, `binary_layout` | constructed fixtures only | FIXTURE |
| 3 E8 reference manuals | hand-built fixtures (labeled) | FIXTURE |

**Gaps found by the audit:**

- **G1 (fixed in the same change as this plan):** the LLM wiki
  (`feature_expert/modern_sspec/skill.md`) still claimed "only E0
  implemented, E2–E9 design-only" — stale since the waves landed, violating
  its own Update Rule. Corrected with an audit-verified status section.
- **G2 — live-capture coverage:** 1 of ~6 evidence domains has any live
  input path. Tracked: `sspec_live_capture_infrastructure_2026-08-08.md`.
- **G3 — migration backlog:** 37 migrated + 143 rejected of 1119 rows
  (180 triaged, 939 untouched). Tracked:
  `untyped_evidence_migration_backlog_2026-08-08.md`.
- **G4 — verification binary:** every green result above ran on the
  disclosed Rust SEED (`bin/release/x86_64-unknown-linux-gnu/simple`, seed
  banner confirmed). Sanctioned as temporary repair evidence, but repo policy
  requires the pure-Simple self-hosted binary; nothing has been re-proven on
  it because no self-hosted deploy currently exists in this tree.
- **G5 — one unresolved candidate cluster:** `nvme_vfat_baseline_script_spec.spl`
  (17 rows, genuine `rt_process_run_timeout` captures) times out at 90s under
  the test runner; left unmigrated, needs a slow-lane pass.

## Task plan

### T1 — Self-hosted re-verification gate (G4) — do FIRST, blocks trust in everything else
1. Rebuild + deploy: `scripts/setup/setup.shs && bin/simple build bootstrap`,
   then redeploy per `.claude/rules/bootstrap.md` (copy to
   `bin/release/<triple>/` via `.new` + `mv`).
2. Prove binary identity positively (capability probe, not banner/size —
   see memory: banner and size both lie).
3. Re-run the three core proof specs + the two regeneration check scripts on
   the self-hosted binary; record results in the wave plan's E1 row.
4. Acceptance: `bin/simple --version` shows no seed banner AND
   `typed_evidence_oracle_spec` 28/28 on that binary.
   Estimated: 1 session (bootstrap is hours; the re-runs are minutes).

### T2 — Live-capture domain lanes (G2) — one research→design→impl cycle per domain
Common design (proven by the terminal slice): each domain gets a small
`capture_<domain>` provider that (a) drives a REAL source through an existing
repo facade — never `rt_*` directly, (b) populates the SAME struct the
fixture path builds (`TerminalSnapshot`, `ActionTrace`, `DrawScene`, ...), so
everything downstream (evidence projection, comparator, docgen) is unchanged,
(c) lands with one spec whose assertion path contains no fixture literal,
plus a sabotage/revert proof.

| Order | Domain | Real source (facade) | Target struct | Notes |
|---|---|---|---|---|
| 2a | TUI interactive | in-process `Compositor`/`UIState` via `SgttiTestDriver.from_tui_state` | `TerminalSnapshot` | SGTTI is NOT a process launcher (verified); use it for the in-process interactive case: drive a real UIState, snapshot per step. Keystroke dispatch + settle per `action_trace.spl`'s `SettleCondition`. |
| 2b | GUI action trace | same SGTTI in-process dispatch | `ActionTrace` | Record real dispatched steps instead of hand-built `UiActionStep`s; 2a and 2b share one lane. |
| 2c | JSON/text protocol | real process stdout via `capture_exec` | `json_document`/`text_protocol` input | Cheapest: compose existing live provider with existing pure adapter; one spec each. |
| 2d | Binary layout | real bytes from a real file via `file_capture.spl` | `binary_layout` input | e.g. read a real ELF header; compose file_capture + binary_layout. |
| 2e | 2D/3D scene | Engine2D/Draw IR readback through `doc/07_guide/ui/rendering/backend_isolation_guide.md` facade | `DrawScene` | Needs its own research pass — headless backend availability decides feasibility. |
| 2f | Simulation | a real run of an existing sim harness emitting `TimelineEvent`s | `simulation_profile` input | Research pass first (which harness exists). |
| 2g | Audio / ML | file-based: real decoded samples / real model-run metrics | `audio_profile` / `ml_profile` input | Blocked on decoder / ML-runtime facade existence; research first, may defer with explicit blocker docs. |

Sequencing: 2c and 2d are one-session wins (compose two already-live pieces).
2a/2b is one focused lane. 2e–2g each start with a bounded research report
before any design/impl (per the TODO's "do not skip straight to
implementation" rule).

### T3 — Migration backlog continuation (G3)
Continue exactly the batch protocol that landed batches 1–9 (triage rule,
additive-only, sabotage/revert per batch, row-level audit-doc merge against
fresh origin — never whole-blob). Expected yield stays low (~0–7 per 20-40
rows); treat as background work, batches of ~25, any number of sessions.
Explicitly NOT a completion gate for the feature — the design doc scopes it
as incremental.

### T4 — Slow-lane NVMe cluster (G5)
One dedicated pass for `nvme_vfat_baseline_script_spec.spl` with a 10-minute
budget: establish HEAD baseline first, then triage its 17 rows. If the spec
cannot complete even at that budget, mark the rows
`reject: unverifiable-within-runner-budget` with the measured evidence.

## Non-goals
- Driving the backlog (T3) to 0 in any single session.
- Building new grammar/DSL surface — all remaining work composes existing
  records and facades.
