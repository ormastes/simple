<!-- codex-design -->
# UI Access Protocol — TUI Mockup

**Feature:** `ui_access_protocol`
**Date:** 2026-04-15

## CLI Shape

```text
$ simple ui snapshot
UI Access Snapshot (v1)
Mode: NORMAL
Active surface: main
Surfaces: 2

[surface:main] Main Window [active]
  [main#root] panel text="" children=[main#title,main#submit_btn] actions=[]
  [main#title] text text="Hello Access" children=[] actions=[]
  [main#submit_btn] button text="Submit" children=[] actions=[submit,click]

[surface:popup] Confirm Dialog
  [popup#dialog_root] dialog text="Confirm" children=[popup#ok] actions=[click,submit]
  [popup#ok] button text="OK" children=[] actions=[click]
```

## Typical Flow

```text
$ simple ui find --surface popup --kind button --text ok
$ simple ui act --canonical popup#ok --action click
$ simple ui history --surface popup --count 10
```

## TUI Design Notes

- prefer surface-first grouping
- show canonical IDs inline
- keep history separate from the current tree
- reserve JSON output for machine use; default TUI output should stay readable
