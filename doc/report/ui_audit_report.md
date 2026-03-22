# UI Library Audit Report

**Date:** 2026-03-22
**Scope:** All 23 widget types across 7 backends (TUI, Web, Electron, Tauri, VSCode, None, MCP)

## 1. Widget Feature Matrix

### 1.1 Widget Rendering Support

| Widget | TUI | Web | Electron | Tauri | VSCode | None |
|--------|-----|-----|----------|-------|--------|------|
| panel | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| text | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| list | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| table | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| progress | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| menubar | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| statusbar | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| input | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| tabs | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| button | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| checkbox | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| dropdown | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| textfield | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| image | ✓* | ✓ | ✓ | ✓ | ✓ | ✓ |
| divider | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| dialog | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| tooltip | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| tree | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| treenode | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| scroll | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| textarea | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| heading | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| label | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |

*TUI image shows placeholder `[IMG: alt]` only — no actual image rendering.

### 1.2 Widget State Support

| Widget | Focus | Disabled | Readonly | Error | Theme |
|--------|-------|----------|----------|-------|-------|
| panel | TUI+HTML | — | — | — | ✓ |
| text | TUI+HTML | — | — | — | ✓ |
| list | TUI+HTML | — | — | — | ✓ |
| table | TUI+HTML | — | — | — | ✓ |
| progress | — | — | — | — | ✓ |
| menubar | — | — | — | — | ✓ |
| statusbar | — | — | — | — | ✓ |
| input | TUI+HTML | TUI+HTML | TUI+HTML | TUI+HTML | ✓ |
| tabs | TUI+HTML | — | — | — | ✓ |
| button | TUI+HTML | TUI+HTML | — | — | ✓ |
| checkbox | TUI+HTML | TUI+HTML | — | — | ✓ |
| dropdown | TUI+HTML | TUI+HTML | — | — | ✓ |
| textfield | TUI+HTML | HTML | TUI+HTML | TUI+HTML | ✓ |
| image | HTML | — | — | — | ✓ |
| divider | — | — | — | — | ✓ |
| dialog | TUI+HTML | — | — | — | ✓ |
| tooltip | — | — | — | — | ✓ |
| tree | TUI+HTML | — | — | — | ✓ |
| treenode | TUI | — | — | — | ✓ |
| scroll | TUI+HTML | — | — | — | ✓ |
| textarea | TUI+HTML | HTML | TUI+HTML | HTML | ✓ |
| heading | — | — | — | — | ✓ |
| label | TUI+HTML | — | — | — | ✓ |

### 1.3 Interaction & Event Support

| Widget | TUI Interact | Web Click | Web Change | Web Hover | Unicode Match |
|--------|-------------|-----------|------------|-----------|--------------|
| panel | — | — | — | — | ✓ |
| text | — | Focus | — | — | ✓ |
| list | Selection | ✓ Click | — | ✓ | ✓ ▸ |
| table | Sort/Filter | ✓ Sort | ✓ Filter | ✓ Row | ✓ ▲▼ |
| progress | — | — | — | — | ✓ █░ |
| menubar | — | ✓ Submenu | — | ✓ | ✓ ▾ |
| statusbar | — | — | — | — | ✓ |
| input | Edit | Focus | ✓ Change | — | ✓ ▸─ |
| tabs | Switch | ✓ Tab | — | ✓ | ✓ ━│ |
| button | Click | ✓ Action | — | ✓ | ✓ ┣┫ |
| checkbox | Toggle | ✓ Toggle | — | ✓ | ✓ ✓ |
| dropdown | Select | — | ✓ Change | — | ✓ ▾▿ |
| textfield | Edit | Focus | ✓ Change | — | ✓ │█ |
| image | — | — | — | — | ✓ |
| divider | — | — | — | — | ✓ ─ |
| dialog | — | — | — | — | ✓ ╔═╗ |
| tooltip | — | — | — | ✓ Hover | ✓ ╭╮ |
| tree | Toggle | ✓ Toggle | — | ✓ | ✓ ▼▶ |
| treenode | Toggle | ✓ (via tree) | — | ✓ | ✓ ▼▶ |
| scroll | Scroll | Native | — | ✓ Scrollbar | ✓ █░ |
| textarea | Edit | Focus | ✓ Change | — | ✓ |
| heading | — | — | — | — | ✓ ─ |
| label | — | Focus | — | — | ✓ |

## 2. Backend Consistency Matrix

### 2.1 Architecture

| Aspect | TUI | Web | Electron | Tauri | VSCode | None |
|--------|-----|-----|----------|-------|--------|------|
| Render Engine | Screen buffer | HTML DOM | HTML DOM | HTML DOM | HTML DOM | HTML DOM |
| Shared render_html_tree() | — | ✓ | ✓ | ✓ | ✓ | ✓ |
| Shared generate_css() | — | ✓ | ✓ | ✓ | ✓ | — |
| Shared generate_js() | — | ✓ | — | — | Custom | — |
| Transport | Direct | WebSocket | IPC stdin/stdout | IPC stdin/stdout | postMessage | Queue |
| Viewport Default | Terminal | 1920×1080 | 1280×720 | 1280×720 | 800×600 | 80×24 |
| Mouse | — | ✓ | ✓ | ✓ | ✓ | — |
| Color | ANSI | CSS | CSS | CSS | CSS | — |
| Images | Placeholder | ✓ | ✓ | ✓ | ✓ | — |
| Native Dialogs | — | — | ✓ | ✓ | — | — |

### 2.2 Output Consistency

| Comparison | Status | Notes |
|-----------|--------|-------|
| Electron = Tauri | ✓ IDENTICAL | Same render_html_tree() + generate_css(), same viewport |
| Web = Electron | ✓ CONSISTENT | Same HTML/CSS, different transport (WS vs IPC) |
| Web = Tauri | ✓ CONSISTENT | Same HTML/CSS, different transport (WS vs IPC) |
| VSCode ≈ Web | ~ SIMILAR | Same HTML, custom JS (postMessage vs WS), smaller viewport |
| TUI ≈ Web | ~ EQUIVALENT | Same layout/data, different rendering (ANSI vs CSS) |
| None = Web HTML | ✓ IDENTICAL | Same HTML, headless (no CSS/JS applied) |

### 2.3 Theme Consistency

| Color Role | TUI (ANSI) | CSS Hex (Dark) | Match? |
|-----------|-----------|----------------|--------|
| Background | — | #1e1e2e | — |
| Foreground | WHITE | #cdd6f4 | ✓ |
| Accent | CYAN | #89b4fa | ~ Blue vs Cyan |
| Success | GREEN | #a6e3a1 | ✓ |
| Error | RED | #f38ba8 | ~ Red vs Pink |
| Warning | YELLOW | #fab387 | ~ Yellow vs Peach |
| Dim | DIM | #6c7086 | ✓ |
| Border | — | #45475a | ✓ |
| Surface | — | #313244 | ✓ |

## 3. Bugs Found & Fixed

| # | Severity | Component | Issue | Status |
|---|----------|-----------|-------|--------|
| 1 | CRITICAL | TUI Tree | ASCII `v`/`>` markers instead of Unicode ▼/▶ | **FIXED** |
| 2 | CRITICAL | HTML Tree | ASCII `v`/`>` markers instead of Unicode ▼/▶ | **FIXED** |
| 3 | CRITICAL | TUI Progress | No value clamping (negative/overflow possible) | **FIXED** |
| 4 | HIGH | HTML Input | Missing `value`, `readonly`, `disabled` attributes | **FIXED** |
| 5 | HIGH | TUI Input | Missing `readonly`, `disabled` checks | **FIXED** |
| 6 | HIGH | HTML Dropdown | Missing `disabled` attribute, no `selected` on options | **FIXED** |
| 7 | HIGH | HTML Checkbox | Used native `<input>` instead of div-based custom checkbox | **FIXED** |
| 8 | HIGH | HTML Dialog | Missing overlay wrapper, wrong CSS class | **FIXED** |
| 9 | HIGH | HTML Menubar | Submenu used `<ul>/<li>` instead of `<div>` matching CSS | **FIXED** |
| 10 | HIGH | HTML Button | Missing `type="button"` attribute | **FIXED** |
| 11 | HIGH | HTML Textfield | Missing `disabled` attribute | **FIXED** |
| 12 | HIGH | CSS | Missing 9 CSS classes (overlay, check-box, status, disabled states) | **FIXED** |
| 13 | HIGH | JS | Missing change handlers for input/textfield/textarea | **FIXED** |
| 14 | HIGH | JS | Checkbox handler referenced native input (old structure) | **FIXED** |
| 15 | CRITICAL | Electron | No CSS included in HTML output — unstyled rendering | **FIXED** |
| 16 | CRITICAL | Tauri | No CSS included in HTML output — unstyled rendering | **FIXED** |
| 17 | MEDIUM | HTML Progress | Bad inline styles, didn't match CSS structure | **FIXED** |
| 18 | LOW | UIEvent | Action has no `value` field — uses name encoding instead | Known limitation |
| 19 | LOW | Tooltip HTML | Shows `[?]` trigger, content only on hover | By design |
| 20 | LOW | TUI Image | Placeholder only, no actual image rendering | By design |

## 4. Code Duplication

| Component | Files | Wasted KB | Recommendation |
|-----------|-------|-----------|----------------|
| ElectronApp / TauriApp | 2 × app.spl | ~9 KB | Extract shared DesktopApp base |
| AsyncElectronApp / AsyncTauriApp | 2 × async_app.spl | ~10 KB | Extract shared AsyncDesktopApp base |
| ElectronBackend / TauriBackend | 2 × backend.spl | ~6 KB | Extract shared DesktopBackend trait |
| IPC re-export wrappers | 2 × ipc.spl | ~0.8 KB | Import directly from shared protocol |
| **Total** | **8 files** | **~26 KB** | Could reduce to 4 shared + 4 thin wrappers |

## 5. Files Modified

| File | Changes |
|------|---------|
| `src/app/ui.render/widgets.spl` | 17 fixes across TUI and HTML renderers |
| `src/app/ui.web/html.spl` | Added 9 CSS classes, fixed JS checkbox handler, added input change handlers |
| `src/app/ui.web/async_ws.spl` | Added focus event parsing |
| `src/app/ui.electron/backend.spl` | Added CSS wrapping to HTML output |
| `src/app/ui.electron/app.spl` | Added CSS wrapping to HTML output |
| `src/app/ui.tauri/backend.spl` | Added CSS wrapping to HTML output |
| `src/app/ui.tauri/app.spl` | Added CSS wrapping to HTML output |
| `src/lib/common/ui/widget.spl` | Added heading/label to parse_widget_kind() |
| `src/lib/common/ui/event.spl` | Added focus and tab action handlers |
| `src/lib/common/ui/__init__.spl` | Expanded exports |
| `src/app/ui.tui/screen.spl` | Unicode box-drawing (single, double, rounded) |
