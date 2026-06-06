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

## Landed (2026-06-06)

- **Pure-Simple HTML generator** `src/lib/common/ui/mobile_html_gen.spl`: a leaf
  node model (`HtmlNode` = tag + attrs + text + children) + `html_node_render`
  (recursive, escaping) + `html_gen_document`. Simple now genuinely *generates*
  HTML from a model instead of pasting strings, without depending on the stubbed
  `widget_store_ops`. Verified by `test/01_unit/lib/common/ui/mobile_html_gen_spec.spl`
  (7 absolute-oracle assertions: exact markup, escaping, nesting, document wrap)
  — confirmed real via a negative control (wrong-expectation spec fails).

## CORRECTION (2026-06-06): the real generate+events pipeline already exists & works

Earlier this doc said "no `WidgetNode→HTML` renderer" and "both routes are large
builds" — **that was wrong** (I searched only `src/lib`). The full pipeline lives
in `src/app/`:
- `app.ui.render.html_widgets.render_html_tree(node, state)` — genuine widget
  catalog → HTML (button/input/panel/table/progress/menubar/tree/vbox/hbox …),
  **26-test spec passes** (`test/01_unit/app/ui/html_render_spec.spl`).
- `app.ui.web.html.generate_css(state)` — CSS generation.
- `src/app/ui/main.spl` + `src/app/ui.tauri/app.spl` — stay-alive event loop:
  initial render → poll stdin → `update_state` → re-render.
- The Tauri shell already invokes it for `.ui.sdn` entries:
  `simple run src/app/ui/main.spl tauri <entry.ui.sdn>` (see
  `simple_subprocess_args_for`), and forwards DOM events back as `ShellMessage`
  (`action`/`keypress`/`input`/`quit`) to the subprocess stdin.

**Verified end-to-end** (desktop, exact shell invocation + piped events):
`… tauri demo_table_list.ui.sdn` with `{"type":"action",…}` then `{"type":"quit"}`
emitted **2 `render` IPC messages** (initial + post-event re-render) whose HTML
contained real generated widgets (12 `widget-panel`, 4 `<input>`, 4 `<table>`).
So Simple genuinely generates the UI from a model AND handles events live.

**So the mobile gap is narrow and concrete:** the mobile shell bundles a 6-line
hard-coded smoke as `SIMPLE_MOBILE_ENTRY_SOURCE` instead of running the real app.
To close it: bundle a `.ui.sdn` + make the cross-compiled mobile runtime run
`src/app/ui/main.spl tauri <ui.sdn>` on-device (needs the `src/app/ui*` + `src/lib`
sources or an AOT build reachable in the package), then events flow over the
already-wired stdin channel. `mobile_html_gen.spl` remains a lightweight,
dependency-free alternative for simple surfaces.

Bug found: `simple ui <mode> <file>` mis-marshals the mode arg (prints a pointer:
"Unknown mode '381699817928'"); use the `run src/app/ui/main.spl tauri <file>`
form. Track as a CLI arg-marshalling bug.

## Verified live (2026-06-06): Simple-generated GUI renders on both mobile targets

Built the hello UI **from the `mobile_html_gen` model** (no hard-coded body),
wrapped it with `html_gen_document`, and loaded the resulting HTML into the Tauri
shell's webview in external-URL mode:
- **iOS simulator** (`build/tauri_ios_mdi/ios_simple_generated_gui.png`) and
  **Android emulator** (`build/tauri_android_mdi/android_simple_generated_gui2.png`)
  both render the same UI (Home/Apps taskbar, Run + "simple run gui" command bar,
  "Hello World" button, "Generated WASM UI" input) — matching the existing
  hand-authored hello reference structure.

So "Simple GUI generates HTML/CSS" is now real and **renders correctly on both
platforms**. Transport here is a dev HTTP serve of the Simple-generated HTML; the
remaining integration is to (a) generate at build time + bundle, and (b) keep the
Simple process alive to handle events + re-render (the IPC event loop).

## Agent-team findings (2026-06-06)

**AOT-to-mobile is a dead-end now** (investigated + attempted on the Android
emulator): `native-build` ignores `--target` (builds host Mach-O);
`compile --target aarch64-linux-android` only emits an SMF container (exit 127 on
device, not a runnable ELF). Missing: `--target` plumbing in native-build,
Android/iOS target presets, Mach-O writer (iOS), cross-compiled runtime; also
upstream-blocked on seed LLVM. Android ≈ days, iOS ≈ weeks. → use source bundle.

**Source-bundle layout (de-risked, proven from isolation):**
- Module resolution uses `find_project_root` (walks up from the entry for a dir
  containing `src/`), **not `SIMPLE_LIB`**. So the bundle must be
  `<BUNDLE>/src/{app,lib,os,type}/…` and run as
  `simple run <BUNDLE>/src/app/ui/main.spl tauri <ui.sdn>`.
- Closure (proven self-sufficient, 368 widget markers rendered from `/tmp` with
  no repo access): `src/app/{io,common,ui*}` (2.5 MB) + `src/lib` minus heavy
  dirs (skia/scipy/scv/viz/cc/blink/compiler/editor/lint) (39 MB) + `src/os`
  whole (11 MB) + `src/type` (52 KB); `src/std` omitted (resolver finds
  `src/lib` first). **Total ≈ 54 MB** (the minimal app.ui-only set is NOT
  sufficient — `main.spl` statically imports all 8 backends).

**Widget showcase:** `examples/06_io/ui/widget_showcase_mobile.ui.sdn` renders
**33 widget kinds** via `render_html_tree`. Catalog gaps (no HTML renderer; silent
drop): command_bar, sidebar, glass_title_bar, workspace_tabs, command_palette,
toast, sheet_modal, context_menu, inspector, utility_rail, status_chip,
selection_pill, empty_state. Prop gaps (renderer reads, SDN parser doesn't copy):
switch `on`, card `subtitle`, heading `level`, button `icon-id`, search_bar
`show_cancel`, navigation_bar `large_title`.

## Next milestones

1. Fix wasm string ABI (export memory + readable text return) — unblocks live render.
2. Tauri2 webview loader: load `.wasm`, `simple_app_render`→mount HTML+CSS,
   DOM events→`simple_app_event`. Verify on desktop, then Android+iOS.
3. Replace `dist/index.html` + the hard-coded smoke with the Simple-WASM GUI.
4. Widget showcase via `builder_matrix_wasm_gui.spl` — all widgets, verified live.
