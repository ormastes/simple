# Tauri + Simple Integration Status

**Date:** 2026-03-22  
**Status:** In Progress  
**Scope:** Current Tauri desktop path in this repo

## Summary

The current Tauri path is **not** pure Simple.

It is a hybrid:
- **Rust/Tauri shell** owns the native window, webview, and JS bridge
- **Simple** owns UI parsing, tree/state handling, and HTML/IPC generation

This is the current runtime split:

```text
Tauri Window (Rust)
  -> loads app://index.html
  -> spawns `simple ...`
  -> reads stdout/stderr
  -> injects rendered HTML into the webview
  -> forwards click/key/resize back to Simple

Simple UI runtime
  -> parses .ui.sdn
  -> builds UI state
  -> renders HTML fragment
  -> prints JSON IPC messages
```

## What Is Working

### 1. Tauri shell HTML load is fixed

The shell now loads the real frontend page instead of an embedded data URL.

Relevant file:
- [tools/tauri-shell/src-tauri/src/main.rs](/Users/ormastes/simple/tools/tauri-shell/src-tauri/src/main.rs)

Current behavior:
- loads `app://index.html`
- logs subprocess stdout/stderr
- logs entry-file existence/readability
- shows status in the window when the subprocess fails

### 2. Entry file readability is now visible

The shell now reports whether the requested `.ui.sdn` file:
- exists
- can be opened for reading

Example log:

```text
[tauri-shell] entry file status: path='examples/ui/hello_tauri.ui.sdn' exists=true readable=true
```

### 3. `simple ui` command path now exists in the Rust driver

A narrow UI dispatch path was added in:
- [src/compiler_rust/driver/src/main.rs](/Users/ormastes/simple/src/compiler_rust/driver/src/main.rs)

And a dedicated entry file was added:
- [src/app/ui/cli_entry.spl](/Users/ormastes/simple/src/app/ui/cli_entry.spl)

`simple ui --help` now works in the rebuilt debug driver.

## Current Blockers

### 1. Circular import around `app.ui`

This is the main remaining structural bug.

The interpreter shows circular import warnings involving:
- [src/app/ui/__init__.spl](/Users/ormastes/simple/src/app/ui/__init__.spl)

Current symptoms:
- importing backend entrypoints through `app.ui`
- or through backend package paths that route back through `app`
- causes partial/empty exports
- `run_tauri` becomes unresolved at runtime

Observed failure:

```text
error: semantic: function `run_tauri` not found
```

### 2. `app.ui.tauri.app` is not cleanly runnable in the current interpreter

Direct execution of:
- [src/app/ui.tauri/app.spl](/Users/ormastes/simple/src/app/ui.tauri/app.spl)

still fails with parser/semantic diagnostics around the current `match ... =>` style.

So even bypassing the UI CLI layer does not yet give a clean Tauri app launch.

### 3. Backend auto-detection still references the wrong shell binary name

Current detection in:
- [src/app/ui/detect.spl](/Users/ormastes/simple/src/app/ui/detect.spl)

still checks for:
- `simple-gui`

but the built binary in this checkout is:
- `simple-tauri-shell`

That means auto-detection can incorrectly conclude Tauri is unavailable.

## Tauri-Specific Mistakes Found

### Rust shell mistakes

Files:
- [tools/tauri-shell/src-tauri/src/main.rs](/Users/ormastes/simple/tools/tauri-shell/src-tauri/src/main.rs)
- [tools/tauri-shell/index.html](/Users/ormastes/simple/tools/tauri-shell/index.html)
- [tools/tauri-shell/dist/index.html](/Users/ormastes/simple/tools/tauri-shell/dist/index.html)

Mistakes:
- The shell originally did not load the real frontend HTML.
- `.ui.sdn` launch assumed `simple ui tauri ...` even when the given Simple binary did not support it.
- stderr used to be effectively invisible from the UI side.
- shell-side success detection is still weaker than it should be because `simple ui --help` only proves CLI dispatch exists, not that the backend graph is valid.

### Simple-side Tauri mistakes

Files:
- [src/app/ui/cli_entry.spl](/Users/ormastes/simple/src/app/ui/cli_entry.spl)
- [src/app/ui/__init__.spl](/Users/ormastes/simple/src/app/ui/__init__.spl)
- [src/app/ui.tauri/app.spl](/Users/ormastes/simple/src/app/ui.tauri/app.spl)
- [src/app/ui/detect.spl](/Users/ormastes/simple/src/app/ui/detect.spl)
- [src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs](/Users/ormastes/simple/src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs)

Mistakes:
- `app.*` resolution previously searched under `src/compiler` instead of `src/app`.
- the UI package export surface is too broad for the current interpreter import behavior and creates circular loading.
- the Tauri app file syntax is not accepted cleanly by the current interpreter path.
- Tauri shell detection uses the wrong binary name.

## What Was Fixed During This Investigation

### Fixed in Rust/Tauri shell

- Switched webview load to the real frontend page
- Added raw stdout/stderr logs
- Added entry file readability log
- Added in-window status reporting for subprocess failures
- Added compatibility preflight for `.ui.sdn` launch

### Fixed in driver/compiler

- Added a real `ui` command path in the Rust driver
- Added narrow Simple app dispatch for the UI command
- Fixed `app.*` path resolution to use `src/app`

## Why This Is Not “Pure Simple Tauri”

Tauri itself remains Rust-native in this repo.

That means:
- native window creation is Rust
- webview creation is Rust
- JS command bridge is Rust
- process orchestration is Rust

Simple can still own almost all application logic, but not the host runtime itself.

The practical target is:

```text
thin Rust Tauri host + mostly-Simple UI runtime
```

not:

```text
pure Simple Tauri host
```

## Recommended Next Steps

### 1. Break the `app.ui` circular import path

Best next step:
- reduce or split [src/app/ui/__init__.spl](/Users/ormastes/simple/src/app/ui/__init__.spl)
- avoid loading broad re-export graphs during Tauri CLI startup

### 2. Make the Tauri entry import path one-way

Goal:
- UI CLI entry should depend on Tauri runner
- Tauri runner should not route back through `app.ui` package exports

### 3. Normalize `src/app/ui.tauri/app.spl`

Bring it into the subset that the current debug interpreter accepts:
- remove or rewrite parser-hostile patterns
- confirm direct execution works before routing Tauri shell through it

### 4. Fix Tauri shell detection

Update:
- [src/app/ui/detect.spl](/Users/ormastes/simple/src/app/ui/detect.spl)

to check the actual binary name/path used in this repo.

## Current Honest Status

Today, the Tauri integration is improved but not yet launch-complete.

What is proven:
- Tauri frontend page loads
- entry file can be checked for readability
- `simple ui` command path exists in the Rust driver
- the remaining failures are now clearly in the Simple module/import/runtime layer

What is not yet proven:
- successful end-to-end `simple ui tauri <file.ui.sdn>` render inside the Tauri window
- stable `run_tauri` resolution through the current module graph
