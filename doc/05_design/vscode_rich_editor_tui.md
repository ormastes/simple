<!-- codex-design -->
# VS Code Rich Editor UI Sketch

**Feature:** `vscode_rich_editor`  
**Date:** 2026-04-12

## Primary Editor Layout

```text
┌──────────────────────────────────────────────────────────────┐
│ Simple Rich Editor                                          │
├──────────────────────────────────────────────────────────────┤
│ 1  use math                                                 │
│ 2                                                          │
│ 3  val loss = [LOSS]   rendered loss block                  │
│ 4                                                          │
│ 5  val eq = [MATH]    rendered equation at natural height   │
│ 6                                                          │
│ 7  [IMAGE BLOCK]                                           │
│ 8                                                          │
│ 9  val raw = m{ x + y }   <- when cursor enters block      │
└──────────────────────────────────────────────────────────────┘
```

## Interaction Model

- cursor outside block:
  - rendered widget replaces raw source
- cursor inside block:
  - raw source is revealed for editing
- invalid block:
  - error widget appears in-place without crashing the editor

## Visual Rules

- math widgets use inline or block presentation depending on block type
- images render as block widgets with bounded width
- placeholders and errors use VS Code theme variables
- the editor keeps standard line numbers, selection behavior, and search UX
