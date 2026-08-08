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
- ~~Interpreter-mode test runner verifies file loading, not `it`-block
  execution~~ — **CORRECTED 2026-08-05, this was stale.** `bin/simple test` DOES
  execute `it` bodies: a deliberately-wrong oracle fails with
  `expected 0 to equal 999` and exit 1 (verified 2026-07-28, recorded in
  `.claude/rules/testing.md`). What is still true is the narrower statement:
  running a spec file through
  `SIMPLE_EXECUTION_MODE=interpreter bin/simple run <spec>` can emit only lint
  warnings and never reach execution. The evidence-gate `.shs` per lane phase
  remains right — but for the reasons in "Reading the verdict" below, not
  because `it` bodies do not run.

## Reading a lane's verdict (2026-08-05)

Evidence gates in this feature area must score the **verdict line**, and it
matters which one:

- `bin/simple test` → `Results: N total, M passed, K failed`
  (`src/app/test_runner_new/test_runner_single.spl:225`).
- `bin/simple run` → `N examples, M failures`, singular `1 failure`, and
  **ANSI-colour-wrapped** (`src/compiler_rust/driver/src/cli/test_output.rs:164`,
  `:251`). These two patterns do not match each other's output; a lane grepped
  the wrong one and retracted a landed claim.
- Best: the per-file `SPEC FILE VERDICT: <path> declared>=N executed=N passed=N
  failed=N dropped=N` line (`5b57a79f8ba`,
  `src/compiler_rust/driver/src/cli/basic.rs:144`) — one authoritative line per
  file, stdout, last.

Never `tail -1` (the per-`describe` line is printed per group and the file-level
failure goes to stderr). Never gate on exit status alone (an unresolved `use` is
only a WARN, exit 0; 143/255 with no output are kill/timeout, not results).
Compare `executed` counts, not just failures. `check()` is a real assertion, a
bare `assert` is inert, and only the last failing `expect` per example prints.
Full list: `.claude/skills/spipe.md` §"Reading the verdict — how a spec run lies
to you"; runner-side detail:
[test_runner layer expert](../../layer_expert/test_runner/skill.md).

## Adjacent lane: WM showcase (docs 2026-08-05, code owned elsewhere)

The WM showcase (2D + web + GUI windows under a window manager, with a taskbar
derived from live window state, capture-verified) overlaps this feature's GUI
lane but is **not** built on `std.ui_test` — that API is still P1-P6
designed-only. Its live-derivation path is `build_taskbar_model`
(`src/app/ui.web/taskbar_shell.spl:55`, running list from
`UiWindowSurfaceRegistry.bindings`); its capture contract is
`src/os/compositor/hosted_wm_capture_evidence.spl` (P6 PPM + pixel-class
counts). All nine `showcase_catalog()` readiness bits are `false` and
`test/01_unit/lib/common/ui/showcase_catalog_spec.spl:55` asserts it, so nothing
in that lane is declared launchable yet. Contract and evidence levels:
`doc/05_design/showcase_apps.md`, `doc/05_design/showcase_apps_gui.md`,
`doc/03_plan/agent_tasks/showcase_apps.md`.

## Update Rule

After research, requirements, architecture, design, implementation,
verification, or release work changes this feature area (especially when a
P1-P6 phase lands), add or refresh links here BEFORE committing, so the next
agent starts from the current project state — update the "what exists vs
what's designed-only" section first, since that is the fact most likely to
go stale.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
