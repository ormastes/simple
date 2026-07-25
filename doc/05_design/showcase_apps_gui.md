<!-- codex-design -->
# Showcase apps GUI design

The catalog presents three equal cards: **2D Rendering**, **Web Standards**, and **GUI Widgets**. Each card shows three surface badges—Standalone, Host WM, and SimpleOS WM—with `ready`, `blocked`, or `skipped` state derived from the canonical catalog rather than hardcoded UI text.

The 2D window is an 800x600 labeled gallery with rectangle/line, curve/shape, gradient/effect, image/text, clip, mask, and engine-composition sections. The web window uses normal browser chrome above the single standards page. The widget window retains its gallery, with interactive controls visibly changing state.

Host-WM and SimpleOS-WM windows keep the same content/title and add normal titlebar, focus, minimize/restore, close, and taskbar behavior. Failure views show app ID, surface, phase, and backend/transport cause; they never replace content with a plausible blank frame.

