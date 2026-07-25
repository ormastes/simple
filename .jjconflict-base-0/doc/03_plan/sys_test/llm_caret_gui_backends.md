# LLM Caret GUI Backends — System Test Plan

1. Assert launch argument parsing for Electron and Metal modes.
2. Assert the pure reducer turns `test` + Enter into a submit action.
3. Assert dummy dispatch returns `hello` and post-submit HTML exposes both
   semantic turns.
4. Assert HTML lowers to a non-empty HTML-AST Draw IR composition.
5. On macOS, launch the native surface and require Metal device-readback
   provenance plus a nonblank screenshot and post-key semantic evidence.
6. Launch Electron against Caret, submit `test`, and assert the visible `hello`
   response, focus, BrowserWindow runtime identity, and screenshot.
7. Re-run the existing CLI/TUI/browser interface spec.
