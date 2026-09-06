# UI Architecture TLDR

Simple UI is a semantic-state-first stack. Shells display or transport state;
Simple keeps ownership of widgets, events, layout, accessibility, and dirty
regions.

```text
App state
  -> semantic UI tree
  -> layout/style intent
  -> UiAccessSnapshot
  -> Render IR / Draw IR
  -> Engine2D or web adapter
  -> host shell
```

UI test evidence has two lanes:

```text
semantic lane: UiAccessNode(id, state, text, x/y/w/h) -> SGTTI or /api/test
pixel lane: Draw IR / framebuffer readback -> bitmap coordinate assertions
```

Open next:

- `00_ui_architecture.md`
- `simple_gui_stack.md`
- `ui_test_architecture.md`
- `web/00_web_framework_architecture.md`

