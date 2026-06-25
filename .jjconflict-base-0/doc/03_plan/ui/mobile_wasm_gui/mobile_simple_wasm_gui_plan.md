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
for the `text` through a stable text ABI facade. This is compiler/ABI work in
`src/compiler/70.backend` (wasm) + runtime string repr.

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
the full widget catalog via `render_html_tree`.

**Step 5 DONE (2026-06-06): the 13 missing catalog renderers added.** Added HTML
renderers in `src/app/ui.render/html_widgets.spl` (+ match arms) for the kinds the
`render_html_tree` match had no arm for (previously silently dropped):
`glass_title_bar`, `sidebar`, `command_bar`, `workspace_tabs`, `command_palette`,
`toast`, `sheet_modal`, `context_menu`, `inspector`, `utility_rail`, `status_chip`,
`selection_pill`, `empty_state`. Markup matches the existing glass CSS classes
(`widget-*` + `ws-tab`/`pill-item`/`rail-icon` `.active`, `palette-item`,
`context-item`, `inspector-title`, `sheet-handle`, `empty-subtitle`, etc.);
interactive kinds emit `data-action` (`ws_tab_*`, `pill_*`, `rail_*`) so events
flow over the existing channel. Verified: 39/39 `html_render_spec.spl` tests pass
(13 new absolute-oracle cases) + the showcase (now exercising all 13) renders all
13 classes + structural markers through the real pipeline (`bin/simple run … tauri
…` → 700 KB HTML, grep-confirmed). Prop gaps (renderer reads, SDN parser doesn't
copy) remain a separate item: switch `on`, card `subtitle`, heading `level`,
button `icon-id`, search_bar `show_cancel`, navigation_bar `large_title`.

## Landed (2026-06-06): source-bundle wiring into the mobile shell

The mobile Tauri shell now embeds + extracts the proven source bundle and runs
the **real** `render_html_tree` pipeline on device (replacing the 6-line smoke):

- `tools/tauri-shell/scripts/build-ui-bundle.shs` — stages the self-sufficient
  closure (`src/app/{io,common,ui*}` + `src/lib` minus heavy dirs + `src/os` +
  `src/type` + `widget_showcase_mobile.ui.sdn`) and gzip-tars it to
  `ui_bundle.tar.gz` (**8.0 MB**; gitignored, not committed).
- `build.rs` — `ui_bundle_include_line()` embeds the tarball as
  `MOBILE_UI_BUNDLE: Option<&[u8]>` (env `SIMPLE_MOBILE_UI_BUNDLE` overrides;
  defaults to the sibling `ui_bundle.tar.gz`; `None` when absent so the crate
  still compiles).
- `Cargo.toml` — `flate2` + `tar` for on-device decompression.
- `lib.rs` — `prepare_bundled_ui_bundle()` gunzip-untars to
  `<tmp>/simple-tauri-shell/ui-bundle/bundle/` (size-marker guarded). `run()`
  prefers the bundle's `widget_showcase_mobile.ui.sdn` over the smoke entry and
  passes the **absolute** `<root>/src/app/ui/main.spl` as `ui_main` via the new
  `simple_subprocess_args_with_main`, so `find_project_root` resolves the module
  graph to `<root>` on device. Explicit `SIMPLE_ENTRY`/argv still take precedence.

Desktop shell verified compiling (`cargo check`, clean).

### Live on Android emulator (2026-06-06): real pipeline runs on device

Built the APK (embeds the 8 MB bundle), installed on `emulator-5554`, launched.
Logcat proves the cross-compiled Simple runtime **extracted the bundle and ran
the genuine `src/app/ui/main.spl tauri widget_showcase_mobile.ui.sdn`** pipeline:
the full module graph loaded (engine2d/sffi gc-warnings) and it emitted a
`{"type":"render",...}` IPC with **`html_len=344229`** (344 KB of generated HTML
carrying the real `generate_css` design tokens) → `eval OK` (mounted in the
Tauri2 webview). This is the real generate-on-model pipeline, NOT the 6-line smoke.

**Bug found + fixed (honest):** the first device render was **unstyled** (black
text on white, only top widgets visible). Root cause in `handle_subprocess_message`
Render handler: it `DOMParser`-parsed the full document but applied only
`parsed.body.innerHTML`, **discarding `parsed.head`** — the `<style>` with all the
CSS. Fix: extract the head's `<style>` text into a persistent
`<style id="simple-render-css">` and copy `data-*`/`class` theme attributes from
the generated `<html>`/`<body>`. Rebuilding + re-verifying on device.

Preflight oracle (desktop, extracted bundle exactly as device extracts it):
`bin/simple run <bundle>/src/app/ui/main.spl tauri <bundle>/widget_showcase_mobile.ui.sdn`
→ EXIT 0, 1 render, genuine widgets (46 `widget-button`, 50 `widget-gallery`,
36 `widget-checkbox`, 12 `<button>`, 8 `<input>`, 2 `<table>`).

**Android: DONE + verified** (styled render + tap/scroll events live, pushed).

### iOS (2026-06-06): same pipeline, runtime-embed fix for Xcode

The bundle + CSS fix are platform-agnostic (same lib.rs). The known iOS blocker
was that **Xcode invokes cargo with a sanitized env**, so build.rs never saw
`SIMPLE_IOS_RUNTIME_AARCH64_SIM` → the runtime wasn't embedded → in-app placeholder.
Fix: `runtime_include_line_with_file_default` embeds the iOS-sim runtime from a
committed-path sibling file `ios_runtime_aarch64_sim.bin` (gitignored) when the env
is unset — so it survives Xcode. The UI bundle already used this file-default
pattern, so it embeds on iOS too with no env. lib.rs already selects
`IOS_RUNTIME_AARCH64_SIM` under `cfg(target_os=ios, aarch64, sim)`.
Rebuilt the deleted iOS-sim runtime (`cargo build --release --target
aarch64-apple-ios-sim -p simple-driver` → 31.5 MB Mach-O arm64), copied to the
sibling path, built the iOS app (`cargo tauri ios build --debug --target
aarch64-sim`; the device archive needs signing, the sim target doesn't).

**LIVE on iPhone 17 sim (2026-06-06): real pipeline in-app, at render parity
with Android.** The app extracts the embedded runtime + bundle, **spawns the
Simple subprocess in-app** (the sim permits exec — the prior blocker was env, now
fixed), runs `main.spl tauri showcase`, emits the same `html_len=344229` real
generated HTML (verified widgets: `widget-menubar` File/Edit, `widget-table`
Alice/Bob/Carol, `widget-tree` src/main.spl, `widget-card`, `widget-textfield`),
and paints the full styled dark-glass UI in WKWebView.

**Two iOS-specific bugs found + fixed (honest — first render was blank white):**
1. **ATS blocked the webview nav.** The mobile branch hardcoded
   `WebviewUrl::External("http://tauri.localhost/inline-shell.html")`. os_log
   showed `didFailProvisionalLoadForFrame ... NSURLErrorDomain code=-1022` — iOS
   App Transport Security rejects plain `http://`; iOS serves assets via the
   secure `tauri://localhost` scheme. Failed nav → blank webview, and the render
   eval'd against a dead document (`eval OK` is NOT proof of paint). Fix: use
   `WebviewUrl::App("inline-shell.html")`, which resolves the correct per-platform
   scheme (secure `tauri://` on iOS, `http://tauri.localhost` on Android).
2. **No real base asset.** `inline-shell.html` was a made-up URL with no asset
   (Android tolerates the 404 and still paints injected DOM; iOS does not). Added
   a real minimal `dist/inline-shell.html` (served from `frontendDist`) as the
   base document, so the App-scheme nav resolves on both platforms.

### iOS build errors fixed (2026-06-06): `cargo tauri ios build` now succeeds

The default `cargo tauri ios build` (device archive) failed with three chained
errors; all fixed in `gen/apple/project.yml` (xcodegen source; regenerate the
`.xcodeproj` with `xcodegen generate`):
1. **Signing** — `error: Signing requires a development team` (exit 65). This
   machine has **0 signing identities** and the sim needs none, so disable the
   requirement: `CODE_SIGNING_ALLOWED: NO`, `CODE_SIGNING_REQUIRED: NO`,
   `CODE_SIGN_IDENTITY: ""`. (For a real device, set `DEVELOPMENT_TEAM` and flip
   back on.)
2. **Platform-mismatched swift lib** — `OTHER_LDFLAGS` hardcoded
   `/iphonesimulator` → device builds linked a sim-built `libswiftCompatibility56.a`
   (`building for 'iOS', but linking in object file built for 'iOS-simulator'`).
   Use the dynamic `$(PLATFORM_NAME)` leaf.
3. **Wrong toolchain root** — `$(TOOLCHAIN_DIR)` resolved to the Metal cryptex
   toolchain (no swift-compat libs) → `library 'swiftCompatibility56' not found`.
   Use `$(DEVELOPER_DIR)/Toolchains/XcodeDefault.xctoolchain/usr/lib/swift/$(PLATFORM_NAME)`.

Both `cargo tauri ios build` (device, unsigned) and `--target aarch64-sim` now
**BUILD SUCCEEDED**; the sim app reinstalls and still renders the styled showcase.

### Final status (2026-06-06): both platforms — build + render + events ✅

Same source, config-only platform difference. Verified live on the same current
bundle (33 + 13 widgets):
- **Android emulator-5554:** APK builds/installs/launches; full styled showcase
  renders (`html_len≈346 KB`); a real `adb` tap on the tab bar → subprocess
  re-render IPC.
- **iPhone 17 sim:** sim app builds/installs/launches; identical styled showcase;
  a real (computer-use) tap on the Search tab → **Home→Search switch** + re-render.

Docs updated: `doc/07_guide/platform/mobile/tauri_mobile_guide.md` (§1b live
source-bundle mode + corrected iOS build fixes) and the SPipe UI skill
`.claude/skills/lib/spipe_ui.md` (mobile sanity section).

## Next milestones

1. Fix wasm string ABI (export memory + readable text return) — unblocks live render.
2. Tauri2 webview loader: load `.wasm`, `simple_app_render`→mount HTML+CSS,
   DOM events→`simple_app_event`. Verify on desktop, then Android+iOS.
3. Replace `dist/index.html` + the hard-coded smoke with the Simple-WASM GUI.
4. Widget showcase via `builder_matrix_wasm_gui.spl` — all widgets, verified live.
