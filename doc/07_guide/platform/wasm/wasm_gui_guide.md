# WASM Native GUI Guide

How the Simple GUI renders on mobile and WM targets via the no-JavaScript WASM
surface path (`wasm32-simple-ui`). This path bypasses the browser JS runtime
entirely — the WASM module talks directly to the host surface through a minimal
`simple_ui.*` import contract.

## 1. Targets

| Target constant | Platform | Triple | Viewport |
|----------------|----------|--------|----------|
| `WEB_RENDER_TARGET_ANDROID_WASM` | Android | `wasm32-simple-ui-android` | 412x915 |
| `WEB_RENDER_TARGET_IOS_WASM` | iOS | `wasm32-simple-ui-ios` | 390x844 |
| `WEB_RENDER_TARGET_HOST_WM_WASM` | Host WM | `wasm32-simple-ui-host-wm` | 800x600 |
| `WEB_RENDER_TARGET_SIMPLEOS_WM_WASM` | SimpleOS WM | `wasm32-simple-ui-simpleos` | 800x600 |

All targets defined in `src/lib/common/ui/web_render_api.spl`.

## 2. Module Contract

### 2.1 Allowed imports

```
env.memory
simple_ui.present
simple_ui.input
simple_ui.image
simple_ui.text
simple_ui.time_now_ms
```

### 2.2 Denied imports

Filesystem (`fs.readFile`, `fs.writeFile`), network (`net.connect`,
`http.request`), process (`process.exit`, `process.spawn`), and environment
(`env.getenv`) are rejected at validation time.

### 2.3 Required exports

```
simple_app_init
simple_app_render
simple_app_event
```

The host calls `simple_app_init` once, then loops `simple_app_render` per frame
and dispatches events through `simple_app_event`.

## 3. Hello GUI — Deterministic Validation

The hello-world GUI in `src/lib/common/ui/wasm_hello_gui.spl` validates the full
pipeline without needing a working cross-compiler. It generates deterministic
HTML/CSS artifacts for each target.

```sh
bin/simple run src/lib/common/ui/wasm_hello_gui.spl
```

### Evidence functions

| Function | Returns |
|----------|---------|
| `wasm_hello_gui_artifact_for_target(target)` | HTML + CSS + metadata |
| `wasm_hello_gui_compile_plan_for_target(target)` | Triple, linker, output path |
| `wasm_hello_gui_event_evidence(target)` | Button/scroll/text/command event checks |
| `wasm_hello_gui_surface_evidence_for_target(target)` | Required vs present surfaces |
| `wasm_hello_gui_target_packages()` | All 4 target packages |

### Render contract (per target)

Each target's render contract specifies:
- Viewport dimensions (target-specific)
- Layout: `column-gap-8-padding-16`
- Button/input min-height: 44px
- Image surface: 64x64
- Primitives: rect, circle, line (128x48 bounds)
- Taskbar + command bar surfaces
- DPI: `target-native`

## 4. Compile Pipeline

The compile pipeline is defined but the real WASM linker path is still being
hardened. Current state:

1. `wasm_hello_gui_compile_plan_for_target(target)` produces a `WasmHelloGuiCompilePlan`
   with source entry, target triple, linker, and output path.
2. `wasm_hello_gui_compile_request(plan, wasm_linker_path, wasi_sysroot, source_available)`
   produces the full compile request with command line.
3. `wasm_hello_gui_compile_result_for_request(request, artifact_exists)` evaluates
   whether the compiled `.wasm` file exists and is valid.

### Compiled artifact evidence

`WasmHelloGuiCompiledArtifactEvidence` checks:
- WASM magic bytes and version
- SMF marker presence
- Required exports (`simple_app_init`, `simple_app_render`, `simple_app_event`)
- UI export/string tables
- Event string tables

## 5. ABI Validation

`web_render_wasm_no_js_validation_error(req, meta)` checks that:
- The request targets a no-JS target
- The metadata ABI matches the expected target ABI
- Encoded bytes and layout bytes are non-zero
- Command count is positive

`web_render_wasm_no_js_is_valid(req, meta)` returns true if no validation error.

## 6. Platform-Specific Notes

### Android
- Default viewport: 412x915 (Pixel 7 logical dimensions)
- Launcher entry: `android-native-wasm-surface`
- Shell runtime: `android:no-js:wasm32-simple-ui`
- See [android_dev_guide.md](android_dev_guide.md) for emulator setup

### iOS
- Default viewport: 390x844 (iPhone 14 logical dimensions)
- Launcher entry: `ios-native-wasm-surface`
- Shell runtime: `ios:no-js:wasm32-simple-ui`
- Cannot test on Linux; prepare artifacts and validate contract only
- See [ios_dev_guide.md](ios_dev_guide.md) for Xcode simulator setup

### Host WM / SimpleOS WM
- Default viewport: 800x600
- Used for desktop window manager integration
- Launcher entries: `host-wm-native-wasm-window`, `simpleos-wm-native-wasm-window`

## 7. Source Code

| What | Where |
|------|-------|
| Render targets & ABI | `src/lib/common/ui/web_render_api.spl` |
| Hello GUI artifacts | `src/lib/common/ui/wasm_hello_gui.spl` |
| Layout profiles | `src/lib/common/ui/profile.spl` |
| iOS CSS overrides | `src/lib/common/ui/ios_css.spl` |
| iOS theme | `src/lib/common/ui/ios/theme.spl` |
| Design tokens | `src/lib/common/ui/design_tokens.spl` |
