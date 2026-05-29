# iOS Development Guide

Guide for building and running Simple apps — specifically the LLM Dashboard — as iOS apps via the Tauri v2 shell.

## 1. Prerequisites

| Requirement | Minimum version | Notes |
|-------------|----------------|-------|
| macOS | Ventura (13) or later | Required by Xcode 15 |
| Xcode | 14.0 | Install from Mac App Store |
| Xcode Command Line Tools | matching Xcode | `xcode-select --install` |
| Rust toolchain | stable | `rustup default stable` |
| Tauri CLI | 2.x | installed by `ios-setup.shs` |
| CocoaPods | any recent | `sudo gem install cocoapods` (if pod install fails) |

The `simple` binary must be on `$PATH` or symlinked as `bin/simple` (created by `scripts/setup.sh`).

## 2. Setup

Run the automated setup script once per machine:

```sh
sh tools/tauri-shell/scripts/ios-setup.shs
```

The script:
1. Confirms you are on macOS.
2. Verifies Xcode >= 14 via `xcodebuild -version`.
3. Adds three Rust cross-compilation targets:
   - `aarch64-apple-ios` — physical device (arm64)
   - `aarch64-apple-ios-sim` — Apple Silicon simulator
   - `x86_64-apple-ios` — Intel Mac simulator
4. Checks for `cargo tauri`; installs `tauri-cli ^2` if absent.

## 3. Running the LLM Dashboard in iOS Simulator

### Automated (recommended)

```sh
sh tools/tauri-shell/scripts/ios-dashboard.shs
```

This script:
1. Starts `bin/simple agents --gui --ios --port 3001` in the background.
2. Polls `nc -z 127.0.0.1 3001` up to 30 times (1 s sleep) until the port is ready.
3. Sets `SIMPLE_DASHBOARD_URL=http://localhost:3001`.
4. Runs `cargo tauri ios dev` from `tools/tauri-shell/`.
5. Kills the background server on exit (`trap`).

Custom port:

```sh
sh tools/tauri-shell/scripts/ios-dashboard.shs --port 3005
```

### Manual

```sh
# Terminal 1 — start dashboard server in iOS mode
bin/simple agents --gui --ios --port 3001

# Terminal 2 — launch simulator once port 3001 is ready
cd tools/tauri-shell
SIMPLE_DASHBOARD_URL=http://localhost:3001 cargo tauri ios dev
```

### What `--ios` does

- Forces web GUI mode (`--gui` implied).
- Constructs `DashboardServer` with `is_ios=true`.
- Bypasses login auth — safe for local WKWebView use.
- Injects iOS CSS overrides (SF Pro font, `#007AFF` accent, 44 pt touch targets, safe-area insets, `-webkit-overflow-scrolling: touch`).
- Adds `Cache-Control: no-store` response header for faster dev iteration.

The `simple ios dashboard` CLI form is also supported:

```sh
bin/simple ios dashboard --port 3001
```

## 4. Building for Physical Device

```sh
sh tools/tauri-shell/scripts/ios-dashboard.shs --device
```

Or manually:

```sh
cd tools/tauri-shell
cargo tauri ios build
```

This produces an `.xcarchive` in `tools/tauri-shell/src-tauri/gen/apple/build/`.  
To distribute, open the archive in Xcode Organizer and use the standard App Store / Ad Hoc export flow.

The Xcode project is at `tools/tauri-shell/src-tauri/gen/apple/simple-tauri-shell.xcodeproj`.  
Bundle ID: `com.simple.ui` (set in `project.yml`).  
iOS deployment target: 14.0.

## 5. Architecture Notes

```
iOS Simulator / Device
└── WKWebView (Tauri v2)
      │  loads URL from SIMPLE_DASHBOARD_URL env var
      │  (set by ios-dashboard.shs before cargo tauri ios dev)
      ▼
  HTTP server  — bin/simple agents --gui --ios --port 3001
      │         (TCP, binds 0.0.0.0; simulator shares host network)
      ▼
  DashboardServer (is_ios=true)
      │  route GET /agents → serve_agents() without auth check
      ▼
  generate_agents_html_with_ios(store, true)
      │  appends ios_css_overrides() inside <style>
      │  adds apple-mobile-web-app meta tags
      ▼
  Browser-rendered HTML with iOS CSS tokens
```

**Key files:**

| File | Role |
|------|------|
| `src/app/llm_dashboard/gui/ios_css.spl` | CSS override string (leaf module) |
| `src/app/llm_dashboard/gui/html_views.spl` | `generate_agents_html_with_ios(store, is_ios)` |
| `src/app/web_dashboard/server.spl` | `DashboardServer.new_ios(port, dir)` |
| `src/app/llm_dashboard/main.spl` | `--ios` flag parsing, `run_ios_dashboard()` |
| `src/app/cli/main.spl` | `case "ios"` CLI routing |
| `tools/tauri-shell/src-tauri/src/lib.rs` | Tauri shell; reads `SIMPLE_DASHBOARD_URL` |
| `tools/tauri-shell/src-tauri/gen/apple/` | Xcode project (committed) |

## 6. Troubleshooting

**`xcodebuild: error: SDK "iphonesimulator" cannot be located`**  
Run `sudo xcode-select --switch /Applications/Xcode.app/Contents/Developer` and retry.

**`cargo tauri ios dev` hangs or errors on simulator boot**  
Open Xcode, go to Simulator menu → Erase All Content and Settings on the target simulator, then retry.

**`nc: command not found` in ios-dashboard.shs**  
Install via `brew install netcat` or use `curl --retry 30 --retry-connrefused` as an alternative.

**Server starts but WKWebView shows blank page**  
Check `SIMPLE_DASHBOARD_URL` is set correctly. Open Safari → Develop → Simulator → inspect the WKWebView for console errors.

**Port already in use**  
Change port: `sh tools/tauri-shell/scripts/ios-dashboard.shs --port 3005`

**CocoaPods errors on fresh clone**  
```sh
cd tools/tauri-shell/src-tauri/gen/apple
pod install
```

## 7. Environment Variables Reference

| Variable | Default | Description |
|----------|---------|-------------|
| `SIMPLE_DASHBOARD_URL` | (none) | URL the Tauri WKWebView loads. Set by `ios-dashboard.shs`. |
| `SIMPLE_BIN` | (none) | Path to `simple` binary; used by Tauri shell in non-URL mode. |
| `SIMPLE_LLM_DASHBOARD_ADMIN_USER` | `admin` | Bootstrap admin username (non-iOS mode only). |
| `SIMPLE_LLM_DASHBOARD_ADMIN_PASSWORD` | `llm-dashboard` | Bootstrap admin password (non-iOS mode only). |
