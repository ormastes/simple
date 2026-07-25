<!-- codex-design -->
# UI CLI LLM Access — GUI Design

**Feature:** `ui_cli_llm_access`  
**Status:** conceptual evidence fixture; not a production inspector

The feature does not add a production Access Inspector or source selector.
Existing GUI and TUI fixtures are exercised through the CLI. The mockup below
is normative design guidance for a future evidence fixture only.

## Inspector layout

```text
┌ Access Inspector ──────────────────────────────────────────────────────────┐
│ Source [Simple UI ui-7 ▾]  Revision 42  ● live  [Refresh] [JSON]           │
├ Windows / Surfaces ───────┬ Semantic tree ────────────┬ Details / History ┤
│ ● main                    │ ▾ main#root       panel   │ ID main#build      │
│   Simple Editor           │   ├ main#title    text    │ Kind button        │
│ ○ build-log               │   └ main#build    button  │ State enabled      │
│   Build Log (TUI)         │                          │ Actions [click]     │
│                           │ Find [build________]     │ [Run click]        │
│                           │ Kind [button ▾] [Find]   │                    │
│                           │                          │ act-000184 request │
│                           │                          │ act-000184 ok      │
└───────────────────────────┴──────────────────────────┴────────────────────┘
```

The source selector can display `simple_ui`, `trace32`, `host_wm`, or
`compositor`. Changing it swaps the adapter; it does not change list/result,
error, output-mode, or safety semantics.

## Interaction design

1. **Refresh/list:** reads the normalized top-level inventory and shows source,
   revision, capture time, staleness, bounds, and unavailable fields.
2. **Select surface:** runs `surface` where semantic descendants exist. A host
   WM row shows only its root because descendants are intentionally unsupported.
3. **Find:** applies the shared bounded selector. Results retain canonical IDs.
4. **Act:** action buttons come only from advertised capabilities. The dialog
   shows target, action, current revision, timeout, and confirmation policy.
5. **Observe/history:** after dispatch, the inspector refreshes and selects the
   correlated request/result events. A timeout or failed observation does not
   rewrite the adapter result as success.

## Source-specific presentation

| Source | Inventory | Detail content | Actions |
|---|---|---|---|
| Simple GUI/TUI | live `UiAccessSurface` records | full canonical semantic tree | node-advertised semantic actions |
| TRACE32 | catalog/session windows | captured text lines and catalog metadata | cataloged open/capture/actions |
| Host WM | live top-level windows | root record and honest WM metadata only | adapter-advertised focus/type/click/screenshot |
| SimpleOS compositor | compositor surfaces | semantic data supplied by SGTTI adapter | advertised compositor actions |

TRACE32 capture commands, host-WM enumeration, and Simple UI refresh remain
inside their adapters. The inspector never imports those backend records.

## State and failure visuals

```text
┌ Action blocked ───────────────────────────────────────┐
│ stale_target                                         │
│ main#build no longer exists at revision 44.          │
│                                                      │
│ [Refresh and locate target]                 [Close]  │
└──────────────────────────────────────────────────────┘
```

- Empty is a valid panel state: `0 windows`, with `truncated=no`.
- Unavailable shows the typed `source_unavailable` failure and recovery hint.
- Stale data carries a visible `STALE` badge and capture age.
- Disabled, busy, defunct, destructive, and prompt-crossing states disable the
  action button or require explicit confirmation; they are never bypassed.
- Color supplements icon, code, and text; keyboard focus is always visible.

## GUI/TUI evidence capture

The system spec launches an existing GUI fixture and existing TUI fixture,
then drives both through the CLI grammar:

1. Capture GUI before action:
   `doc/06_spec/image/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/gui-before.png`.
2. Save matching `snapshot --json` and `find --json` protocol evidence under
   `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/protocol/`.
3. Act on the canonical ID, refresh, and assert the correlated history pair.
4. Capture GUI after action as `gui-after.png`.
5. Save TUI before/after text or ANSI captures as `tui-before.txt` and
   `tui-after.txt` under
   `build/test-artifacts/03_system/app/ui_cli_llm_access/feature/ui_cli_llm_access/tui/`.
6. Generate the operator manual with `**Screenshots:**` and
   `**TUI Captures:**` metadata linking these artifacts.

The GUI golden verifies visible state and layout at a stable viewport. Semantic
assertions verify identity, state, capability, action, and history. Pixel
evidence alone is insufficient. GUI/web/2D evidence pairs the semantic/SGTTI
snapshot with DrawIR structure when applicable, then checks CPU-oracle/backend
pixel parity and records selected backend, readback, fallback, retained-cache,
culling, dirty-area, and draw-call provenance.

## Accessibility

- Full keyboard traversal follows source, inventory, tree, details, then history.
- Tree rows expose role, expanded state, selected state, and canonical ID.
- Status changes use a polite live region; action failure uses an assertive one.
- Action confirmation names the exact source, target, action, and consequence.
- The inspector follows platform scaling, contrast, reduced-motion, and focus
  indicator settings.

## Explicit non-goals

- No replacement GUI renderer or desktop automation product.
- No fabricated host-window descendants.
- No pixel-coordinate fallback when a semantic action is absent.
- No second inspector-specific snapshot or history model.
