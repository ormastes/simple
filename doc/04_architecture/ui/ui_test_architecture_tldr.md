<!-- codex-architecture -->
# UI Test Architecture - TLDR

Short version of `doc/04_architecture/ui/ui_test_architecture.md`. Key decision:
unify TUI and GUI/web/2D testing behind **one configurable interface**
(`tui` | `gui` | `both`) backed by **SGTTI**, so GUI can be asserted in-process
and headless the way TUI is - without forking a new element model or breaking
the HTTP protocol path.

## Two layers today

```
              UI under test
                   |
     +-------------+-------------+
     v                           v
(A) HTTP /api/test/*        (B) SGTTI in-process
 UITestClient                win_text_access snapshot
 -> ElementInfo              -> WinTextSnapshot -> [UiAccessNode]
 needs a server              no server, no display backend
 web, tui-web (S4)           compositor unit tests, MCP
```

Gap: GUI/web/2D has **no in-process semantic test path** sharing the
`UITestClient` vocabulary. TUI uses a **third** route (widget/state model
directly). SGTTI closes the gap.

## API rule

New specs import `use std.spec`; `std.spipe` remains a compatibility alias.
UI helpers such as SGTTI checks and future `expect_draw` run inside normal
SPipe `it` blocks and do not replace `expect` or the canonical matcher set.

## SGTTI in one picture

```
sources ---> WinTextSnapshot ---> find_nodes / route_action ---> assert
 trace32       access: UiAccessSnapshot
 simple_ui <-- TUI  (win_text_simple_ui_snapshot from UIState)
 host_wm
 compositor <- GUI  (gtti_snapshot_from_compositor, WM_MODE_HIDDEN = headless)
```

`UiAccessNode` already has every assertable field (id/kind/visible/focused/
enabled/selected/text/props) - **no new element type needed**.

## Target: one interface, config-selected surface

```
target = tui | gui | both
            |
   +--------+--------+
   v                 v
TUI snapshot     GUI snapshot (headless)
   +-------+---------+
           v
  same methods: get_element / check_visible / check_focused /
  check_enabled / check_selected / check_exists / check_text / click
           |
   both -> parity: state must agree on tui AND gui
```

Public SGTTI Phase 2 API: `UI_TEST_TARGET_TUI`, `UI_TEST_TARGET_GUI`,
`UI_TEST_TARGET_BOTH`, `ui_test_targets`, `SgttiParityResult`, and
`sgtti_parity_check`.
Phase 5 adds `sgtti_snapshot_from_draw_ir_batch` and
`sgtti_snapshot_from_draw_ir_composition` so Draw IR scenes can assert their
semantic node tree before Engine2D pixel readback.

## Rules

- **No fork.** Driver returns canonical `UiAccessNode` (or the owner's
  `SemanticElementInfo`); reuse pub `win_text_find_nodes` / `win_text_route_action`.
- **Additive.** `UITestClient` (HTTP) stays; SGTTI driver is a sibling.
- **Two evidence tiers.** Semantic (SGTTI, headless, fast) + pixel (existing
  bitmap gates / Engine2D readback - still the pixel oracle).
- **TUI parity is a target, not today.** TUI is S1; it must be lifted onto a
  `WinTextSnapshot` (`UIState -> ui_access_snapshot_from_state -> simple_ui source`)
  before the shared interface applies.
- **Layout/CSS/position stay out of v1.** Those become assertable only via the
  Draw IR inspection extension (Protocol v2, gated) - which **depends on SGTTI**.
- **Headless GUI isn't free.** Needs a `Compositor` fixture; plan adds an
  ergonomic snapshot provider.

## Source files

| File | What |
|---|---|
| `src/lib/common/ui/win_text_access.spl` | SGTTI core (snapshot/query/action, 4 sources) |
| `src/os/compositor/gtti.spl` | Compositor -> snapshot, headless in hidden WM |
| `src/lib/common/ui/semantic_contract.spl` | `SemanticElementInfo.from_access` (S1/S2 owner) |
| `src/lib/common/ui/access_types.spl` | `UiAccessNode` canonical type |
| `src/lib/nogc_sync_mut/ui_test/client.spl` | `UITestClient` (HTTP path) |
| `test/01_unit/os/compositor/gtti_spec.spl` | Headless SGTTI compositor test |

## Open next

- [Full doc](ui_test_architecture.md)
- [Improvement plan](../../03_plan/ui/ui_test/ui_test_sgtti_plan.md)
- [Shared UI contract](shared_ui_contract.md)
- [Draw IR inspection](../../01_research/ui/draw_ir/draw_io_sdn_draw_ir.md)
