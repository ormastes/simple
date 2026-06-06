# Mobile Simple-GUI → HTML/CSS/WASM → Tauri2 — Plan & Verified Status (2026-06-06)

Goal (user): Simple GUI **generates** HTML/CSS/WASM; **Tauri2** hosts that UI;
events + UI data flow Simple↔webview. Replace the current hard-coded-HTML path.

## Intended architecture

```sdn
(pipeline mobile-simple-wasm-gui
  (node app        "*.spl exports simple_app_init/render/event")
  (node compile    "bin/simple compile --target wasm32 -> .wasm (exports + simple.gui custom section)")
  (node host       "Tauri2 webview JS: load .wasm, call render -> mount HTML+CSS")
  (node events     "DOM event -> simple_app_event(name,target_id) -> re-render")
  (edge app compile) (edge compile host) (edge host events) (edge events host))
```

## Verified by checking (evidence in build/, doc/09_report/mobile_tauri_*)

- **Step 1 — render+events live.** Android: Simple-runtime MDI renders on arm64
  emulator; real adb tap/text/scroll/drag processed (touch-drag bug fixed,
  `touch-action:none`). iOS sim: WKWebView renders an interactive page and
  processes real taps/typing. *Caveat:* those demos used hard-coded / hand-written
  HTML, not Simple-generated UI; on Android the Simple process exits before events
  (events handled by JS, not Simple).
- **Step 2 — linkage.** Tauri shell ↔ subprocess uses an openWindow/render
  `SubprocessMessage` IPC (stdin/stdout). A richer envelope protocol exists in
  `web_render_api.spl` (`WebRenderSnapshotEnvelope`/`PatchEnvelope` = UI data,
  `WebRenderInputEnvelope` = events) but is **not** wired to Tauri.
- **Step 3 — generation exists, partly.** `bin/simple compile hello_wasm_gui.spl
  --target wasm32` → valid 4380-byte wasm exporting `simple_app_init`,
  `simple_app_render`, `simple_app_event` + a `simple.gui` custom section (the
  `.spl` source). Render/event **logic runs inside wasm** (`render_probe=8`,
  `event_probe=5`). `web_render_api_spec` (17) + `wasm_hello_gui_spec` (19) pass.

## The concrete blocker for Step 4 (genuine, not faked)

The compiled wasm **exports no `memory`** and `simple_app_render()` returns
`undefined` → the generated HTML string is **unreachable** by a host. The
existing Electron "browser execution evidence" mounts *pre-known* HTML and only
asserts the probe counts — it does not render the wasm's actual output (a partial
false-green: logic-ran ≠ HTML-rendered).

To unblock, the Simple **wasm backend** must: (a) export linear `memory`; and
(b) make `simple_app_render`/`simple_app_event` return a readable `(ptr,len)`
for the `text` (or export `rt_string_data`/`rt_string_len` accessors). This is
compiler/ABI work in `src/compiler/70.backend` (wasm) + runtime string repr.

### Update (2026-06-06): WASM backend is skeletal — deeper than an ABI tweak

Confirmed via `wasm-objdump`: `simple_app_render` is compiled to `() -> nil`
with body **size=2** (an empty stub). `wasm_codegen_adapter.spl` self-describes
"body stub with unreachable" and "default stub: treat unknown types as i32";
the string-building body is never emitted and `text` returns are dropped. So the
wasm backend has **no string/heap codegen** — making the WASM GUI render for real
is a major compiler subsystem (real wasm codegen for strings/heap/memory), not a
small fix. **Decision (user: "WASM-first, IPC fallback"): fall back to the IPC
path now**; WASM GUI codegen tracked as a separate large compiler effort.

### Update 2: the "Simple generates HTML from a model" path is also unbuilt

Intensive check of the UI stack found there is **no used `WidgetNode → HTML`
renderer**: every Simple GUI example (`hello_wasm_gui.spl`,
`builder_matrix_wasm_gui.spl`) **hard-codes** its `<main>…</main>` body string and
uses the built `WidgetNode` tree only for `all_widget_ids()` / validation. Worse,
the widget model is inconsistent: `widget_store_ops.spl` defines
`struct WidgetNode: id: text` (id only) with kind/props/children in separate
process-global registries (the known "widget_store_ops stub"). So a genuine
model→HTML renderer requires first untangling the widget model.

Net: **both** routes to truly Simple-generated UI are large builds:
- WASM route → implement string/heap codegen in the stub wasm backend.
- Model→HTML route → reconcile the widget model + write a `WidgetNode`-tree→HTML
  renderer + a stay-alive Simple event loop + Tauri event-forwarding to stdin.

This is multi-PR work, not a single-session fix. Recommend confirming scope and
doing it as a tracked feature with per-step specs + emulator verification.

## IPC fallback (active path): Simple generates UI + handles events, live

Simple process **stays alive**, generates HTML/CSS via the UI builder, and
handles events over the existing subprocess stdin/stdout `SubprocessMessage` /
`WebRenderInputEnvelope` channel — genuine Simple-generated UI + Simple-handled
events on Tauri2, no hard-coded HTML, no wasm dependency.

## Next milestones

1. Fix wasm string ABI (export memory + readable text return) — unblocks live render.
2. Tauri2 webview loader: load `.wasm`, `simple_app_render`→mount HTML+CSS,
   DOM events→`simple_app_event`. Verify on desktop, then Android+iOS.
3. Replace `dist/index.html` + the hard-coded smoke with the Simple-WASM GUI.
4. Widget showcase via `builder_matrix_wasm_gui.spl` — all widgets, verified live.
