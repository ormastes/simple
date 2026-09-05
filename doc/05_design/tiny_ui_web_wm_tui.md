<!-- codex-design -->
# Tiny UI/Web/WM TUI design

Tiny TUI is a host verification surface for the same semantic tree. It renders fixed `TinyCell` records into current/previous bounded buffers and emits normalized terminal row diffs.

The primary fixture is a fullscreen root containing a heading, clipped scrolling list, text input, checkbox, progress indicator, button, and popup. Tab/Shift-Tab changes focus; arrows scroll/select; text events edit; Enter activates; Escape closes the popup.

System evidence captures normalized text/ANSI under `build/test-artifacts/03_system/app/tiny_browser/feature/tiny_ui_web_wm/`. Differential fixtures compare bounds, cells, focus order, and actions with equivalent FTXUI behavior while recording intentional terminal/font differences.
