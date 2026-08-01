# UI Test Infrastructure Feature Expert

## Role

Own feature-specific process knowledge for the planned Playwright-like UI test
API (`std.ui_test`): a single `UiTest` facade over five/seven lanes (Tui, Gui,
WebSimple2d, WebChrome, Electron, Scene2d, Scene3d) behind one `UiLane` trait,
a lazy re-resolving `Locator`, polling matchers bridged into `std.spec`, and
budget-aware pixel asserts. As of this writing **only P0 (the shared
diagnostics primitives, `std.diag`) is implemented** — see the
[diagnostics](../diagnostics/skill.md) feature expert for that module. P1-P6
(the session/locator/lane drivers themselves) are designed but not built.

## Pipeline Links

- [research](../../skill_command/skills/pipe/research/skill.md)
- [design](../../skill_command/skills/pipe/design/skill.md)
- [impl](../../skill_command/skills/pipe/impl/skill.md)
- [verify](../../skill_command/skills/pipe/verify/skill.md)
- [release](../../skill_command/skills/pipe/release/skill.md)
- [spipe skill](../../../../.claude/skills/spipe.md) — "UI-lane specs &
  diagnostics" section is the entry point for anyone writing a spec today.

## Feature Links

- Research: `doc/01_research/ui/testing/ui_test_infra_research.md` (all
  file:line claims underlying the design are verified there).
- Design: [doc/05_design/ui/testing/ui_test_infra_design.md](../../../../doc/05_design/ui/testing/ui_test_infra_design.md)
  — §1 core model (`UiTest.launch`, `UiSession`, `Locator`, `UiLane` trait),
  §2 per-lane event injection tiers, §3 module layout
  (`src/lib/nogc_sync_mut/ui_test/`), §4 `FrameClock`/`TestClock`, §5 teardown,
  §6 stage log (consumes std.diag), §7 3D seam, §8 std.diag contract (owned
  here by reference, owned in practice by the diagnostics feature expert),
  §9 open decisions.
- Plan: [doc/03_plan/ui/testing/ui_test_infra_plan.md](../../../../doc/03_plan/ui/testing/ui_test_infra_plan.md)
  — phases P0 (DONE, diag) through P6 (Electron + evidence-gate migration
  demos), each sized ~1 agent-day, independently landable.
- P0 module (implemented, the one piece that exists today):
  [diagnostics feature expert](../diagnostics/skill.md) /
  [src/lib/nogc_sync_mut/diag.spl](../../../../src/lib/nogc_sync_mut/diag.spl).
- Existing facilities the design reuses (not redesigned): `std.spec` BDD core,
  `std.play` polling expect/locator/CDP launcher, SGTTI snapshot driver
  (`ui_test/sgtti.spl`), `ui.test_api` `inject_event` surface, `WmBridge.
  handle_input`, `InputBackend` trait, `Engine2DReadback`, golden-gate/
  `evidence.env` conventions, TUI `Screen.render()`, engine3d CPU rasterizer.

## What exists vs what's designed-only

- **Implemented today:** `std.diag` (P0) only — see
  [diagnostics feature expert](../diagnostics/skill.md) for its full API,
  gotchas, and spec (`test/01_unit/lib/nogc_sync_mut/diag_spec.spl`, 13/13
  green).
- **Designed, not implemented (P1-P6):** `UiTest.launch`, `UiSession`,
  `Locator`/selector grammar, `expect_ui`/`expect_session` matchers, the
  per-lane drivers (`ui_test/lanes/{tui,gui,web_simple2d,web_chrome,electron,
  scene}.spl`), `FrameClock`/`TestClock`, pixel-budget asserts, and
  `session.write_evidence(...)`. None of these files exist yet at
  `src/lib/nogc_sync_mut/ui_test/` beyond the pre-existing `client`, `http`,
  `parse`, `sgtti`, `types` modules the design reuses.
- Do not hand-roll a UI driver against `ui.test_api`/SGTTI/`WmBridge` directly
  in a new spec — follow the P1-P6 plan phase order (P1 = TUI lane first,
  cheapest to prove the API shape) instead, or extend the plan if a phase is
  insufficient.

## Known constraints (from the design's own honesty section)

- Deferred by design: hardware-3D lane (engine3d GPU backends are stubs),
  macOS OS-level CGEvent injection, winit-queue synthetic injection
  (bootstrap-only seed change + dual-handle-table hazard), Playwright-style
  trace recording, browser contexts/isolation, codegen/recorder.
- GUI lane injects at compositor dispatch tier, not the winit queue (queue
  injection needs a seed extern — bootstrap-only policy).
- Web pixel full-page render is ~6 min/frame (quadratic-CSS bug,
  `doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md`)
  — pixel asserts are designed budget-aware (small viewports, region-only,
  explicit `budget_ms` override) rather than assuming the fix lands first.
- Interpreter-mode test runner verifies file loading, not `it`-block
  execution — every lane phase ships its own evidence-gate `.shs` that greps
  spec output rather than trusting the aggregate `Passed/Failed` summary.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area (especially when a
P1-P6 phase lands), add or refresh links here BEFORE committing, so the next
agent starts from the current project state — update the "what exists vs
what's designed-only" section first, since that is the fact most likely to
go stale.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
