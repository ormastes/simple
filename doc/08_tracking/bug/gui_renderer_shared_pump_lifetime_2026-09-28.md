# GUI renderer aliases and shared winit pump lifetime

Status: implementation on draft dynload branch; live GUI integration remains
unverified with a source-matched self-hosted Simple runtime.

## Failure modes found

- A mapping lease protected the cached code address but did not stop
  `GuiRenderer.close()` from freeing a window during another call or through
  a copied renderer.
- Winit returned event-loop handle `1` for every loop on a thread. One
  renderer could free the shared pump while another renderer still used it.
- Per-thread window and event IDs could select an unrelated object after a
  renderer crossed threads. The global event poll could consume a sibling
  window's input.
- Window, loop, and event destructors return C `bool`; the integer dynamic
  caller did not match those return types.

## Implemented boundary

The renderer registers its window under a never-reused session ticket and
retains a mapping use until teardown. Each operation reserves the window and
checks the provider's thread-local loop identity before calling cached
symbols. Close checks creator-thread access while the session is admitted,
then claims exclusive destruction. Wrong-thread and busy close refuse without
retiring the session. Retained renderer aliases consult the shared owner;
identity fields stay unchanged after close.

The provider now uses unique loop, window, and event handles, polls events by
window, and frees its loop only after the last window is removed. Destructors
use the typed C-boolean bridge and require both a successful transport and a
true provider result. A failed partial teardown quarantines its mapping pin
and session so no stale symbol or already-freed window is reused.

## Remaining evidence

- Build and run `test/02_integration/gui/gui_renderer_shared_pump_integration.spl`
  on a real GUI main thread with the rebuilt `libspl_winit` provider and a
  source-matched self-hosted Simple binary. It checks busy and alias close,
  two windows on one pump, and presentation after the first close.
- Run the existing macOS window registration SPipe scenario with external
  window and input observation.
- Exercise wrong-thread refusal and partial teardown fault injection on
  macOS and Linux. The current review is static for those cases.
- Rebuild any older provider before using the new mandatory window count and
  per-window poll symbols.
