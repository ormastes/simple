# GUI, web, and WM showcase live interaction evidence

Source: `test/03_system/ui_showcase/showcase_live_interaction_evidence_spec.spl`.

Run a real launcher with `SIMPLE_SHOWCASE_REQUIRE_INTERACTION=1`. PASS
requires at least one presented frame, an internal-window click, a scrollbar
drag, typed text, a positive left-panel offset mirrored exactly to the linked
right panel, and a zero offset on the independent free-panel negative control.

Missing GUI windows, missing web document paths, or incomplete semantic
evidence prints a target-specific `showcase_*_live_status=fail` row with a
reason and exits nonzero. Complete runs print PASS with
`reason=interaction-complete`.

The WM launcher additionally requires `SIMPLE_WM_FRAME_EXPORT=1`, a positive
exported pixel count and checksum, and a positive frame sequence. This prevents
the WM warm no-op presentation path from being mistaken for a delivered frame.

This contract validates the semantic receipt. Screenshot capture and native
input injection remain external live-run artifacts and must not be inferred
from this headless spec.
