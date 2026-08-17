<!-- codex-design -->
# Tiny UI/Web/WM GUI design

The GUI/browser surface is one borderless output-sized root under Tiny WM kiosk policy. A bounded popup overlays it without desktop chrome.

The reference page contains a heading, paragraph, checkbox, text input, button, progress bar, and vertically scrolling list. Keyboard focus is always visible; pointer capture persists through a press/release sequence; clipped children never draw or hit outside their effective clip.

Host and RV32 captures use the same admitted page and stable bitmap font. GUI goldens/diffs live under `doc/06_spec/image/03_system/app/tiny_browser/feature/tiny_ui_web_wm/`; framebuffer checksums and typed receipts accompany images so screenshots are not the only oracle.
