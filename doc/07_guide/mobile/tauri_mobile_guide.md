# Tauri Mobile Guide — Simple GUI on iOS & Android

How to render a Simple GUI (`.ui.sdn`) layout as a native iOS / Android app via
the Tauri v2 shell (`tools/tauri-shell`), using the **embedded static page**
mode. For the dashboard-over-HTTP mode (live server + `SIMPLE_DASHBOARD_URL`)
see [ios_dev_guide.md](ios_dev_guide.md).

## 1. How it works

```
.ui.sdn  ──parse──▶ UIState ──render_html_tree──▶ HTML+CSS
                                   │
                       (render_mobile_page helper)
                                   ▼
              tools/tauri-shell/dist/index.html   ← frontendDist
                                   │  embedded at build time
                                   ▼
        Tauri v2 shell (iOS WKWebView / Android WebView)
```

The same Simple GUI lib that renders the desktop Tauri/web backends renders the
mobile page — one widget tree, one HTML/CSS pipeline. On mobile with no bundled
`simple` runtime the shell simply displays the embedded page (no live subprocess
needed for a static layout).

Build the embedded page from any `.ui.sdn`:

```sh
SIMPLE_EXECUTION_MODE=interpret bin/simple run \
  examples/ui/render_mobile_page.spl \
  examples/ui/mobile_hello.ui.sdn \
  tools/tauri-shell/dist/index.html
```

`examples/ui/mobile_hello.{ui.sdn,spl}` is the reference app — it exercises
list, button, textbox (input/textfield), scroll, checkbox and radio over the
touch-enabled mobile backend (`TauriBackend.new_mobile` / `run_tauri_mobile`).

## 2. Responsive layout (small vs big screen)

Phone readability comes from two pieces, both emitted by the renderer:

1. **Viewport meta** — `web_render_full_html` emits
   `<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">`.
   Without `width=device-width` mobile WebKit lays out at ~980px and shrinks the
   whole page, making everything tiny.
2. **Responsive `@media` CSS** — `generate_css` appends breakpoints keyed to the
   planned `LayoutProfile` size classes in `common/ui/profile.spl`:
   - **compact** (`<= 600px`, phone): single column, full-bleed panels, 16px base
     font (also stops iOS input-focus zoom), 44px touch targets, stacked rows.
   - **regular** (`601–1200px`, tablet): 2-column grid.
   - **expanded** (`> 1200px`, desktop): default multi-column layout.

The webview applies the size class from its real device width, so this needs no
server-side viewport plumbing. `common/ui/profile.spl` exposes the same
breakpoints (`Breakpoints`, `SizeClass`, `LayoutProfile`, `ProfileResolver`) for
app code that wants to branch the widget tree by `orientation` / size class.

## 3. iOS (simulator)

Prereqs: macOS + Xcode, `rustup target add aarch64-apple-ios-sim`,
`cargo install tauri-cli --version ^2`.

```sh
cd tools/tauri-shell
cargo tauri ios build --debug --target aarch64-sim
```

### Fixes baked into `gen/apple/project.yml`

Newer Xcode (16/26) needs the iOS target settings below — after editing
`project.yml` you **must** re-run `xcodegen generate` in `gen/apple/`, because
`cargo tauri ios build` reuses the existing `.xcodeproj` and does not re-run
xcodegen:

```yaml
settings:
  base:
    # absolute path — $(TOOLCHAIN_DIR)/$(PLATFORM_NAME) did not resolve at link
    OTHER_LDFLAGS: $(inherited) -L<Xcode>/Toolchains/XcodeDefault.xctoolchain/usr/lib/swift/iphonesimulator -lswiftCompatibility56 -lswiftCompatibilityConcurrency
    ENABLE_DEBUG_DYLIB: NO   # Xcode preview debug-dylib link also fails the swift-compat shim
```

Symptom without these: `Undefined symbols ... __swift_FORCE_LOAD_$_swiftCompatibility56`
(and `…Concurrency`) at the final link.

Install + launch + screenshot:

```sh
xcrun simctl boot "iPhone 17 Pro"
APP="$(find ~/Library/Developer/Xcode/DerivedData/simple-tauri-shell-*/Build/Products/debug-iphonesimulator -maxdepth 1 -name '*.app' | head -1)"
xcrun simctl install booted "$APP"
xcrun simctl launch booted com.simple.ui
xcrun simctl io booted screenshot /tmp/ios.png
```

## 4. Android (emulator)

The Android SDK lives at `~/Library/Android/sdk`. Export the env (not on `PATH`
by default):

```sh
export ANDROID_HOME=~/Library/Android/sdk
export NDK_HOME="$ANDROID_HOME/ndk/27.0.12077973"
export PATH="$ANDROID_HOME/platform-tools:$ANDROID_HOME/emulator:$PATH"
```

Build, boot, install, launch:

```sh
cd tools/tauri-shell
cargo tauri android build --debug --target aarch64   # → app-universal-debug.apk

emulator -avd Pixel7 -no-snapshot -gpu swiftshader_indirect &
adb install -r src-tauri/gen/android/app/build/outputs/apk/universal/debug/app-universal-debug.apk
adb shell am start -n com.simple.ui/.MainActivity
adb exec-out screencap -p > /tmp/android.png
```

## 5. Widgets & 2D

- **RadioButton** (`type: radio` in `.ui.sdn`) — single radios or option groups;
  selecting emits `select_<group>_<index>` (handled by the existing list-select
  path in `common/ui/event.spl`). Renders in HTML and TUI.
- **2D canvas backend** (`app.ui.render.canvas2d`) —
  `scene_to_canvas_html(scene, id)` translates a `RenderScene` (rect / circle /
  line / text) into an HTML5 `<canvas>` 2D-context replay script for the mobile
  webview. Vector commands stay crisp at any DPI and avoid marshalling raw pixel
  buffers across the interpreter FFI. Demo: `examples/ui/mobile_2d.spl` (run
  under `SIMPLE_EXECUTION_MODE=interpret`).

## 6. Troubleshooting

| Symptom | Cause / fix |
|---------|-------------|
| Page tiny / unreadable on phone | Missing device-width viewport meta — ensure the page came from the current renderer (§2). |
| Statusbar shows literal `{app.mode}` | `expand_template` must substitute unconditionally (interpreter `index_of` misses brace needles); ensure the current `html_widgets.spl`. |
| iOS link error `__swift_FORCE_LOAD_$_swiftCompatibility56` | Add the swift-compat `OTHER_LDFLAGS` + `ENABLE_DEBUG_DYLIB: NO`, then `xcodegen generate` (§3). |
| Android "no space left on device" | Mobile builds + emulator need headroom; `src/compiler_rust/target/debug` can be a large stale cache (bin/simple uses `bin/release/<triple>/simple`). |
| Android emulator System-UI ANR | CPU starvation from concurrent builds — not a code bug; let builds finish. |
| Mobile app shows a "no bundled Simple runtime" card | Expected when there is no cross-compiled `simple`; the shell now shows the embedded static page instead (set `SIMPLE_BIN` / a bundled runtime / `--url` for a live subprocess). |
