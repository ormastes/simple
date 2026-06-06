# Plan - Unify UI Test Libs on SGTTI (TUI / GUI / Web / 2D)

**Date:** 2026-06-06
**Feature:** `ui_test_sgtti`
**Architecture:** `doc/04_architecture/ui/ui_test_architecture.md`
**Depends-for:** `doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md` (Phase 5)
**Status:** Proposed
**Owners:** `src/lib/nogc_sync_mut/ui_test`, `src/lib/common/ui/win_text_access`,
`src/os/compositor/gtti`

## Goal

Give GUI / web / 2D an in-process, headless semantic test path that shares the
`UITestClient` vocabulary, and expose one configurable interface
(`tui` | `gui` | `both`) so a single test body runs against either surface -
without forking a new element model or changing the HTTP protocol path.

## API Contract

- Canonical executable specs import `use std.spec`.
- `use std.spipe` remains a compatibility alias for older or SPipe-named specs.
- UI/SGTTI helpers expose capture/query/action data through
  `std.common.ui.win_text_access` and the `play_wm_text_*` MCP/CLI adapters.
- New UI-specific expectations must be helper functions layered inside SPipe
  `it` blocks. They must not replace `describe`, `it`, `expect`, or the
  canonical matcher vocabulary.
- SGTTI assertions target semantic text/tree data: source, surface id, node id,
  role/kind, text, visibility, focus, staleness, and routed-action result.
  Pixel, backend, and native-window fidelity stays in dedicated GUI evidence
  lanes.

## Review of the current test libs (what exists)

- **HTTP path - `src/lib/nogc_sync_mut/ui_test/` (`client.spl`).**
  `UITestClient` over HTTP `/api/test/*`; returns `ElementInfo`
  (id/kind/visible/focused/enabled/selected/text/props). Solid for the S4
  surfaces (web, tui-web) but **requires a running server**. The other three
  memory tiers (`gc_async_mut`, `gc_sync_mut`, `nogc_async_mut`) are 1-3 line
  re-export shims of this one - no tier-specific logic.
- **SGTTI path - `common.ui.win_text_access` + `os.compositor.gtti`.**
  In-process `WinTextSnapshot` over four sources; `win_text_find_nodes` /
  `win_text_route_action`. Compositor source runs **headless in WM_MODE_HIDDEN**.
  `UiAccessNode` already carries every assertable field. Used by
  `gtti_spec.spl` and `play_wm_text_*` MCP - **not by any test client**.
- **TUI path - widget/state model.** `async_tui_spec.spl` drives
  `UIState`/`UITree`/`UIEvent` + `builder`/`state` directly. **Not on the shared
  semantic surface** (TUI is S1 per `shared_ui_contract.md`).
- **`semantic_contract.spl`.** Designated S1/S2 owner;
  `SemanticElementInfo.from_access(node)` reshapes a `UiAccessNode`. Reuse this -
  do not write a parallel node->element mapping.

### Findings -> improvements

1. GUI/web/2D cannot be asserted in-process with the `UITestClient` vocabulary.
   Add an SGTTI-backed driver (additive sibling, not a rewrite of `client.spl`).
2. TUI is off the shared surface. Provide the `UIState -> WinTextSnapshot` lift
   so TUI joins the same interface.
3. No config targets tui/gui/both with one body. Add target config plus a parity
   check for `both`.
4. Headless GUI needs a heavy `Compositor` fixture. Add an ergonomic snapshot
   provider to amortize fixture cost.

## Guardrails

- **No fork.** Driver returns canonical `UiAccessNode` (or
  `SemanticElementInfo` via the owner). Reuse pub `win_text_find_nodes` /
  `win_text_route_action`.
- **Additive.** `UITestClient` (HTTP) untouched; SGTTI driver is a new sibling
  module. The four memory-tier shims keep re-exporting.
- **Contract discipline.** SGTTI assertions stay inside `shared_ui_contract`
  v1's allowed set (identity/state/text/structure). Layout/CSS/position remain
  Protocol v2 (the Draw IR extension), never a v1 edit.
- **SPipe discipline.** New specs use `use std.spec`; `use std.spipe` stays a
  compatibility alias. UI helpers do not replace SPipe `expect` or the
  canonical matcher set.
- **Two evidence tiers.** Semantic (SGTTI) complements, never replaces, the
  pixel bitmap gates / Engine2D readback oracle.
- **Pure Simple.** `.spl` only; verify with `bin/simple check` + a `bin/simple
  run` probe (the runner only checks file load, not `it`-block execution).
  Never skip a failing test without approval.

## Phases

### Phase 1 - SGTTI test driver (GUI/web/2D in-process)

- New `src/lib/nogc_sync_mut/ui_test/sgtti.spl`:
  - `SgttiTestDriver` over a `WinTextSnapshot`, methods mirroring `UITestClient`:
    `get_element`, `get_elements`, `check_exists`, `check_visible`,
    `check_focused`, `check_enabled`, `check_selected`, `check_text`, `click`,
    `type_text` (actions via `win_text_route_action`).
  - Returns canonical `UiAccessNode`; lookup by `canonical_id` then `widget_id`.
  - Export from `ui_test/__init__.spl`.
- **Spec:** `test/01_unit/lib/nogc_sync_mut/ui_test/sgtti_spec.spl` over a
  hand-built `WinTextSnapshot` (no compositor needed for the unit).
- **Verify:** `bin/simple check` + probe `bin/simple run` asserting node lookup
  and `check_visible`/`check_text` truths.
- **Exit:** GUI-shaped snapshot asserts in-process with no HTTP server.

### Phase 2 - Target config + parity (`tui` | `gui` | `both`)

- Add `UI_TEST_TARGET_TUI/GUI/BOTH` + `ui_test_targets(target)` expansion.
- Add `SgttiParityResult` + `sgtti_parity_check(tui, gui, id)` requiring
  visible/focused/enabled/selected agreement; `both` passes only on parity.
- **Spec:** parity passes on agreeing snapshots, fails on divergence/missing.
- **Exit:** one driver vocabulary, surface chosen by config.

### Phase 3 - TUI onto the shared surface

- Helper lifting a TUI `UIState` to a `WinTextSnapshot`:
  `ui_access_snapshot_from_state(state, [])` ->
  `win_text_simple_ui_snapshot(...)` (`simple_ui` source).
- Migrate 1-2 representative TUI specs to the shared driver (keep, do not
  delete, the widget-model specs). Do not migrate native-backend-dependent tests.
- **Exit:** a TUI spec and a GUI spec share one test body via the target config.

### Phase 4 - Ergonomic headless GUI snapshot provider

- A `gui_test_snapshot(...)` helper that builds the headless `Compositor`
  fixture (backend + cursor) and returns a `WinTextSnapshot`, so GUI tests stop
  copying the `gtti_spec.spl` boilerplate.
- **Exit:** GUI test setup is a single call; documented fixture cost removed.

### Phase 5 - Engine2D / web semantic assertions

- Pair existing bitmap gates with an SGTTI assertion that the Draw IR batch
  produced the expected node tree before raster (semantic + pixel together).
- **Exit:** at least one engine2d/web scene asserts both tiers.

## Cross-link: Draw IR inspection depends on this

`doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md` **Phase 5** (gated
`/api/test/draw-ir`, `?id=`, `/diff`, `/layout`) and **Phase 6**
(`expect_draw`) read the in-process snapshot substrate. They are **blocked on
Phases 1-2 here**:

- `expect_draw` is the SGTTI driver's assertion vocabulary extended with
  layout/geometry fields (Protocol v2, capability-gated), implemented as a
  helper inside normal SPipe specs.
- `/api/test/draw-ir` serves the same `WinTextSnapshot`/Draw IR composition the
  SGTTI driver queries.

Sequencing: land `ui_test_sgtti` Phases 1-2 first, then Draw IR plan Phases 5-6.
The Draw IR model/SDN/Draw.io work (its Phases 1-3) is independent and can run
in parallel.

## Definition of done

1. SGTTI driver asserts GUI/web/2D in-process, headless, with the `UITestClient`
   vocabulary; HTTP path unchanged.
2. One configurable interface (`tui` | `gui` | `both`) with a real parity check.
3. TUI lifted onto the shared surface; a shared body runs on both.
4. Headless GUI fixture reduced to one provider call.
5. Architecture (full + TLDR), guide, skill docs, and this plan describe one
   consistent `std.spec` canonical / `std.spipe` compatibility API.
