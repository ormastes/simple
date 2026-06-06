<!-- codex-architecture -->
# UI Test Architecture - TUI / GUI / Web / 2D

Status: draft-v1 (2026-06-06)
Owners: `src/lib/nogc_sync_mut/ui_test`, `src/lib/common/ui/win_text_access`,
`src/os/compositor/gtti`, `src/lib/common/ui/semantic_contract`,
`src/app/ui.test_api`

Related:

- `doc/04_architecture/ui/shared_ui_contract.md` (semantic contract, Protocol v1)
- `doc/04_architecture/ui/simple_gui_stack.md` (render/Draw IR stack)
- `doc/01_research/ui/draw_ir/draw_io_sdn_draw_ir.md` (Draw IR inspection)
- `doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md` (improvement plan)

## Purpose

This document is the canonical architecture for **how UI is tested** across
Simple surfaces: TUI, GUI, web, and the 2D renderer. It separates the two test
layers that exist today, names which surface uses which, and defines the target
state: one configurable test interface (`tui` | `gui` | `both`) backed by SGTTI
so GUI/web/2D can be asserted in-process and headless the same way TUI is.

It is a companion to `shared_ui_contract.md` (which defines the semantic
contract and HTTP protocol) and `simple_gui_stack.md` (which defines the
render/Draw IR stack). This doc is about the test access between them.

## Test-Library API Contract

New executable UI specs use canonical SPipe imports:

```simple
use std.spec
```

`std.spipe` remains a compatibility alias for existing specs. Runtime-family
`std.<family>.spec` and `std.<family>.spipe` facades must expose the same public
test helpers. UI-specific helpers, including SGTTI checks and future
`expect_draw`, run inside normal SPipe `it` blocks and do not replace
`describe`, `it`, `expect`, or the canonical matcher set.

## Two test layers (and the gap)

There are two distinct ways UI state is read for assertions today. They are not
competitors; they are different transports for the same semantic truth, but they
are not yet unified behind one interface.

```
                       UI under test
                            |
        +-------------------+-------------------+
        |                                       |
   (A) HTTP protocol                     (B) SGTTI in-process
   /api/test/*                           win_text_access snapshot
        |                                       |
   UITestClient                         gtti_snapshot_from_compositor (GUI)
   (client.spl)                         win_text_simple_ui_snapshot   (TUI)
        |                                       |
   ElementInfo (id/kind/                 WinTextSnapshot
   visible/focused/...)                  -> [UiAccessNode] (same fields)
        |                                       |
   needs a running server                no server, no display backend
   (web, tui-web = S4)                   (headless, hidden WM mode)
```

| Layer | Module | Transport | Element type | Needs server? | Used by today |
|---|---|---|---|---|---|
| (A) HTTP protocol | `ui_test/client.spl` `UITestClient` | HTTP `/api/test/*` | `ElementInfo` | yes | Web Backend, TUI-Web Proxy (S4) |
| (B) SGTTI in-process | `common.ui.win_text_access` + `os.compositor.gtti` | in-memory snapshot | `UiAccessNode` | no | compositor unit tests, `play_wm_text_*` MCP |

**The gap.** GUI / web / 2D rendering has no in-process semantic test path that
shares the `UITestClient` vocabulary. To assert GUI state today a test either
stands up a full HTTP server or hand-builds an SGTTI snapshot and walks nodes
manually. TUI tests take a third, separate route entirely. This doc's target
state closes that gap.

## SGTTI: the in-process inspection core

SGTTI (Simple Gui Texture Tree Interface) is the read-only snapshot/query/action
core in `src/lib/common/ui/win_text_access.spl`. It normalizes four sources into
one `WinTextSnapshot`:

- `WIN_TEXT_SOURCE_TRACE32` - TRACE32 text windows
- `WIN_TEXT_SOURCE_SIMPLE_UI` - Simple UI access snapshots (the TUI/GUI path)
- `WIN_TEXT_SOURCE_HOST_WM` - host WM top-level windows
- `WIN_TEXT_SOURCE_COMPOSITOR` - SimpleOS compositor surfaces (headless GUI)

```
WinTextSnapshot
  access : UiAccessSnapshot
            nodes : [UiAccessNode]   # canonical_id, surface_id, widget_id,
                                     # kind, visible, focused, enabled,
                                     # selected, text_value, props,
                                     # child_ids, action_names
  sources: [WinTextSource]           # id, kind, confidence, capabilities, stale
```

Core operations (all `pub`, all pure over a snapshot value):

- `win_text_find_nodes(snapshot, surface_id, kind, text_query, limit)` -> query
- `win_text_route_action(snapshot, WinTextActionRequest)` -> action resolution
- `win_text_node_supports_action`, `win_text_default_action` -> capability checks

Key property: `UiAccessNode` already carries every assertable field the shared
UI contract allows (id = `canonical_id`, text = `text_value`, plus
`visible`/`focused`/`enabled`/`selected`/`kind`/`props`). No new element model is
needed to assert against it. `semantic_contract.spl`'s `SemanticElementInfo`
(`SemanticElementInfo.from_access(node)`) is a richer reshape of the same node
for the S1/S2 semantic API; tests may use either, but neither forks a third type.

## How to test GUI / web / 2D with SGTTI

The GUI/web/2D surfaces render through the compositor or the Engine2D/web
renderer. SGTTI gives them an in-process semantic tree without a display backend
or HTTP server via the compositor source in hidden WM mode.

```
Compositor (WM_MODE_HIDDEN)            # populates surface tree, no display
   |  gtti_snapshot_from_compositor(comp, wm_mode, captured_at_ms, now_ms)
   v
WinTextSnapshot (source = compositor)  # confidence "high"
   |  win_text_find_nodes / win_text_route_action
   v
assert: visible / focused / kind / text / geometry props (x,y,width,height)
```

Two evidence tiers, used together:

1. **Semantic tier (SGTTI).** Assert the structure and state of the surface: the
   window exists, is focused, has the expected title/kind/children, and geometry
   props. Fast, headless, deterministic, no pixels.
2. **Pixel tier (bitmap evidence).** Assert rendered pixels via existing bitmap
   gates and Engine2D CPU-fallback readback. This stays the pixel oracle; SGTTI
   does not replace it.

For 2D specifically, the Draw IR executor already exposes pixel readback; SGTTI
adds the semantic assertion that the Draw IR batch produced the expected node
tree before raster. The Draw IR inspection extension is built on SGTTI: its
gated `/api/test/draw-ir` endpoint reads the same snapshot substrate.

`gtti_snapshot_from_compositor` takes a real `Compositor`. A GUI test must build
a headless compositor fixture, as `gtti_spec.spl` does today. The improvement
plan adds an ergonomic snapshot provider to amortize that fixture.

## How to test TUI

TUI tests today do not use the shared semantic surface. They drive the
widget/state model directly (`common.ui.widget.{UIState, UITree, UIEvent}`,
`common.ui.builder.{column, text_widget, build_tree}`,
`common.ui.state.{update_state}`). Per `shared_ui_contract.md`, TUI is an S1
target: it is not yet on the semantic/SGTTI path. So tui/gui interface parity is
a target state, not current reality.

The bridge already exists to lift TUI onto SGTTI:

```
TUI UIState
  |  ui_access_snapshot_from_state(state, [])        # common.ui.access
  v
UiAccessSnapshot
  |  win_text_simple_ui_snapshot(snapshot, ...)      # win_text_access
  v
WinTextSnapshot (source = simple_ui)   # same shape the GUI compositor produces
```

Once TUI emits a `WinTextSnapshot`, the same SGTTI query/assert vocabulary
applies, which is what makes one configurable interface possible.

## Target state: one configurable interface (`tui` | `gui` | `both`)

The improvement is an in-process driver that mirrors the `UITestClient`
vocabulary over a `WinTextSnapshot`, with a target config selecting the
surface(s). Same method names regardless of surface; `both` requires parity.

```
        config: target = tui | gui | both
                        |
          +-------------+-------------+
          v                           v
   TUI snapshot                 GUI snapshot
   (simple_ui source)           (compositor source, headless)
          |                           |
          +------------+--------------+
                       v
            one driver interface
   get_element / get_elements / check_visible /
   check_focused / check_enabled / check_selected /
   check_exists / check_text / click / type_text
                       |
              target == both?
                       |
                       v
            parity check: element state must
            agree across tui + gui (both pass)
```

Design constraints:

- Return the canonical `UiAccessNode` or the owner's `SemanticElementInfo`;
  never fork a third element record.
- Reuse the pub `win_text_find_nodes` / `win_text_route_action` core; the driver
  is a thin facade, not a reimplementation.
- Keep this additive: `UITestClient` (HTTP) is unchanged; the SGTTI driver is a
  sibling. S4 surfaces keep their HTTP tests.
- Action routing over a snapshot verifies routability; live mutation happens
  through the owning compositor/session, after which the test re-snapshots.
- Keep helper methods inside SPipe scenarios. They do not redefine SPipe's
  assertion DSL or matcher vocabulary.

## Relationship to the other contracts

- **`shared_ui_contract.md` (semantic, Protocol v1).** SGTTI assertions live
  inside v1's allowed set (identity/state/text/structure). Layout/CSS/absolute
  position remain out of v1 and only become assertable via the Draw IR
  inspection extension (Protocol v2, capability-gated).
- **`simple_gui_stack.md` (render stack).** SGTTI sits beside the render path:
  the compositor/renderer produce pixels (pixel tier) and a node tree (semantic
  tier). The Draw IR (`draw_ir.spl`) is the render IR; SGTTI is the test access
  over the surfaces that consume it.
- **Draw IR inspection (`draw_io_sdn_draw_ir.md`).** The gated
  `/api/test/draw-ir` + `expect_draw` work depends on SGTTI as the in-process
  snapshot substrate - see the plan's cross-link.

## Files

| File | Role |
|---|---|
| `src/lib/common/ui/win_text_access.spl` | SGTTI core: snapshot/query/action, four sources |
| `src/os/compositor/gtti.spl` | Compositor -> `WinTextSnapshot` (headless in hidden WM) |
| `src/lib/common/ui/semantic_contract.spl` | S1/S2 owner: `SemanticElementInfo.from_access` |
| `src/lib/common/ui/access_types.spl` | `UiAccessNode` / `UiAccessSnapshot` canonical types |
| `src/lib/common/ui/access.spl` | `ui_access_snapshot_from_state` (TUI/GUI state lift) |
| `src/lib/nogc_sync_mut/ui_test/client.spl` | `UITestClient` (HTTP `/api/test/*`) |
| `src/lib/nogc_sync_mut/ui_test/types.spl` | `ElementInfo` / `UIStateInfo` (HTTP shape) |
| `src/app/ui.test_api/handler.spl` | `/api/test/*` server routes |
| `test/01_unit/os/compositor/gtti_spec.spl` | Existing headless SGTTI compositor test |

## Open next

- Improvement plan: `doc/03_plan/ui/ui_test/ui_test_sgtti_plan.md`
- Draw IR inspection plan: `doc/03_plan/ui/draw_ir/draw_io_sdn_draw_ir_plan.md`
- Semantic contract: `doc/04_architecture/ui/shared_ui_contract.md`
- TLDR: `doc/04_architecture/ui/ui_test_architecture_tldr.md`
