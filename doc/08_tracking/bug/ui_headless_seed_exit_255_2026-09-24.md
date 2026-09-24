# Bug — `bin/simple ui headless <file.ui.sdn>` exits 255 silently under the seed

Date: 2026-09-24. Found by the rendering-gates lane (NFR-002 step e).

## Symptom

`SIMPLE_LIB=src bin/simple ui headless <file.ui.sdn>` exits 255 with no
output — for the new
`examples/06_io/ui/rendering/rendering_items.ui.sdn` AND for the stock
`examples/06_io/ui/demo.ui.sdn` control. Both JIT and interpreter lanes.

## Not an sdn/entry defect

The same sdn parses fine via `parse_ui_to_tree`, and calling
`app.ui.none.app.run_headless` directly prints "Headless UI completed."
with exit 0. The defect is in the `ui` CLI dispatch path (src/app/ui —
the `headless` subcommand), not in the document or the headless runner.

## Impact

The item-list parse gate cannot run through the sanctioned CLI. Gates use
the direct `run_headless` call path instead. Same family as the recorded
`ui web` seed bug (`ui_web_seed_exits_before_bind_2026-09-24.md`): the
seed's `ui` subcommand dispatch is fragile.

## Expected

`bin/simple ui headless <sdn>` parses and runs the document headlessly,
printing the completion line, exit 0 — or a real error message on parse
failure.
