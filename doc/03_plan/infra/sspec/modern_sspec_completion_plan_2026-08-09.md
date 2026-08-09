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
| `live_json_capture_spec.spl` | real subprocess stdout → `json_document` (closed JSON-pointer oracle) | LIVE (T2c, landed 2026-08-09) |
| `live_text_protocol_capture_spec.spl` | real subprocess stdout → `text_protocol` frame parse | LIVE (T2c, landed 2026-08-09) |
| `live_binary_capture_spec.spl` | real file round-trip bytes → `binary_layout` PTE decode | LIVE (T2d, landed 2026-08-09) |
| `live_interactive_surface_spec.spl` | real in-process widget mutations → `WinTextSnapshot` rows + `ActionTrace` | LIVE (T2a/T2b, 2026-08-09) |
| `live_scene_capture_spec.spl` | real `builder.label`→`compute_layout`→`widget_tree_to_draw_cmds` → `DrawScene` | LIVE (T2e, 2026-08-09) |
| `live_simulation_capture_spec.spl` | real `ChaosScheduler.pick_next` decisions → `TimelineEvent` | LIVE (T2f, 2026-08-09) |
| `live_audio_capture_spec.spl` | real PCM16 WAV bytes → real `decode_wav` → `audio_profile` | LIVE (T2g, 2026-08-09) |
| 37 migrated legacy specs | real captures via `untyped_capture.spl` | LIVE |
| `ml_profile` | constructed fixtures only — real torch facade unreachable under the interpreter runtime (blocked, documented) | FIXTURE |
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

### T1 — Self-hosted re-verification gate (G4) — **BLOCKED 2026-08-09, still owed**
Attempted 2026-08-09; stopped at its own safety gate and recorded in
`doc/08_tracking/todo/sspec_self_hosted_reverification_2026-08-09.md`: four competing
bootstrap/native-build jobs were already running (one directly in this repo tree) on a
99%-full disk (62G free), and no self-hosted binary is deployed. Starting a fifth build
would have risked the machine for every session. This remains the single caveat on ALL
green results in this feature. Original procedure retained below.

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
| 2a | TUI interactive | in-process widget store via `SgttiTestDriver.from_tui_state` | `TerminalSnapshot` | **LANDED 2026-08-09** — `live_interactive_surface_spec.spl` (2 ex): real `set_prop` mutations on the widget store, rows read back from the post-mutation `WinTextSnapshot`. |
| 2b | GUI action trace | same SGTTI in-process dispatch | `ActionTrace` | **LANDED 2026-08-09** — same spec records the real dispatched steps. |
| 2c | JSON/text protocol | real process stdout via `capture_exec` | `json_document`/`text_protocol` input | **LANDED 2026-08-09** — `live_json_capture_spec.spl` + `live_text_protocol_capture_spec.spl`, both green/red/green sabotage-proven. |
| 2d | Binary layout | real bytes from a real file via `file_capture.spl` | `binary_layout` input | **LANDED 2026-08-09** — `live_binary_capture_spec.spl`: real file round-trip, PTE value derived only from read-back bytes, sabotage-proven. |
| 2e | 2D/3D scene | real `builder.label` → `compute_layout` → `widget_tree_to_draw_cmds` | `DrawScene` | **LANDED 2026-08-09** — `live_scene_capture_spec.spl`; pure-arithmetic headless path, no GPU/window/backend call. 3D scene readback still open. |
| 2f | Simulation | real `ChaosScheduler.pick_next` (RoundRobin, seeded) | `simulation_profile` input | **LANDED 2026-08-09** — `live_simulation_capture_spec.spl`; 5 real scheduling decisions, oracle hand-derived from the RoundRobin formula. |
| 2g | Audio / ML | audio: real `decode_wav`; ML: none reachable | `audio_profile` / `ml_profile` | **AUDIO LANDED 2026-08-09** (`live_audio_capture_spec.spl`, real RIFF/WAVE bytes through the real parser, rms/peak hand-computed). **ML BLOCKED** — `rt_torch_*` externs do not resolve under the interpreter runtime `bin/simple test` uses; documented in `doc/08_tracking/todo/live_ml_capture_blocked_2026-08-09.md` rather than faked. |

**Status 2026-08-09: T2 substantially complete.** 2a/2b/2c/2d/2e/2f and the audio half of
2g all landed, written by parallel guided agents and independently re-verified (blob
re-hash + re-run + tautology review; one agent's evidence-derived oracle was rewritten to
hand-reasoned literals before landing). Remaining: ML (blocked, documented) and 3D scene
readback (2e covered 2D only).

### T3 — Migration backlog continuation (G3)
Continue exactly the batch protocol that landed batches 1–9 (triage rule,
additive-only, sabotage/revert per batch, row-level audit-doc merge against
fresh origin — never whole-blob). Expected yield stays low (~0–7 per 20-40
rows); treat as background work, batches of ~25, any number of sessions.
Explicitly NOT a completion gate for the feature — the design doc scopes it
as incremental.

### T4 — Slow-lane NVMe cluster (G5) — **DONE 2026-08-09**
Baseline measured GREEN 16/16 within the 600s budget, so the earlier "90s timeout" was
budget, not breakage. All 16 rows triaged and rejected with evidence-backed reasons: row 9
emits structured `key: value` stdout but its values embed run-specific interpolated
mount/image paths, so an exact typed check would be built from the same variables
(tautological); rows 29-257 each assert a single substring on a fixed stderr diagnostic,
where an exact check on full stderr adds brittleness without precision.

## Non-goals
- Driving the backlog (T3) to 0 in any single session.
- Building new grammar/DSL surface — all remaining work composes existing
  records and facades.
