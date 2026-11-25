# TUI Design Mockup: Caret Suite A2UI Surface & Regions

**Feature:** `a2ui_dynamic_app_interfaces`  
**Design Doc:** [a2ui_dynamic_app_interfaces.md](a2ui_dynamic_app_interfaces.md)

## Caret Suite A2UI Layout (`caret.screen.sdn`)

```
+------------------------------------------------------------------------------+
| [region: workspace] Caret Suite                                              |
| 2 visible sessions (ready)                                                   |
+-----------------------------------+------------------------------------------+
| [region: roster]                  | [region: detail]                         |
| Find agent: [________________]    | Agent A                                  |
| [Refresh]                         | ---------------------------------------- |
|                                   | (sanitized plain-text pane preview or    |
| > [Agent A]                       |  "No preview available" when denied)     |
|   Running; turn unknown; CPU unav |                                          |
|   [Agent B]                       |                                          |
|   Running; waiting for approval;  |                                          |
|   CPU 0%                          |                                          |
+-----------------------------------+------------------------------------------+
| [region: composer] Message to Agent A                                        |
| [ /draft/body (Message-only; slash text stays data)               ] [ Send ] |
| Outcome: Sent to a1 [gen=2:v2_detailed]                                      |
+------------------------------------------------------------------------------+
```

## Region Capability Ceilings (Trusted `caret.authority.sdn`)

- `workspace` (`parent: null`): `discover, read, subscribe, invoke, compose`
- `roster` (`parent: workspace`): `read, subscribe, invoke` (`caret.select`, `caret.refresh`)
- `detail` (`parent: workspace`): `read, subscribe` (no `invoke`, no `composer` mounting)
- `composer` (`parent: workspace`): `read, subscribe, invoke` (`caret.send` Message-only with user activation)
- CLI integration (`cs_main.spl`): `/a2ui` slash inspection in interactive TUI; `--a2ui` and `--a2ui-json` non-interactive modes.
