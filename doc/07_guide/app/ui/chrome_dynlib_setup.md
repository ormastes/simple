# Chrome (CEF) Dynlib Setup

Stages the pinned Chromium Embedded Framework binary drop that the Chrome render dynlib
(`src/runtime/browser/chrome_render_shim.c`) links against. Without a drop the shim still
builds — in **stub** mode, where every entry point returns
`CHROME_RENDER_E_BACKEND_UNAVAILABLE` — so stage A of the probe runs on any host.

Pin data (version + per-platform archive names and SHA-256): `config/cef/cef_pin.sdn`.
It is the only place those values live; both setup scripts read it.

## Linux / macOS / MSYS git-bash

```sh
sh scripts/setup/setup-cef-dynlib.shs --check      # report; no network
sh scripts/setup/setup-cef-dynlib.shs --install    # download + verify + extract
eval "$(sh scripts/setup/setup-cef-dynlib.shs --env)"   # exports SIMPLE_CEF_ROOT/_LIB
sh scripts/setup/setup-cef-dynlib.shs --selftest   # fatal fixtures; no network
```

FreeBSD: CEF publishes no FreeBSD distribution, so `--check` reports
`cef_platform=unsupported` rather than guessing a near match.

## Windows (native PowerShell)

```powershell
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-cef-dynlib.ps1 -Check
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-cef-dynlib.ps1 -Install
powershell -ExecutionPolicy Bypass -File scripts\setup\setup-cef-dynlib.ps1 -Env
```

CEF ships `.tar.bz2` on every platform, Windows included; the twin extracts with `tar`
(bundled with Windows 10+), not `Expand-Archive`, which cannot read that format.

## Receipt keys

Every run of either script ends with this block; `cef_status` is always the last line.

| key | values |
|---|---|
| `cef_platform` | `linux64` `linuxarm64` `macosx64` `macosarm64` `windows64` `windowsarm64` `unsupported` |
| `cef_version` | the pinned version from `cef_pin.sdn` |
| `cef_lib` | absolute path to `libcef` once staged, else empty |
| `cef_sha256_status` | `pinned` `unpinned` `unset` `mismatch` |
| `macos_helper_status` | macOS only, see below |
| `cef_reason` | `ok` `no-cef-drop` `headers-absent` `libcef-absent` `pin-unset-refused` `download-failed-*` `extract-failed-*` … |
| `cef_status` | `present` (exit 0) / `missing` (exit 1-2) / `hash-mismatch` (exit 3) |

## Fail-closed rules

- A platform row whose `sha256:` is `UNSET` is **refused** by `--install`. `--allow-unpinned`
  (`-AllowUnpinned`) overrides it, prints a loud warning, and still records
  `cef_sha256_status=unpinned` — such a drop is never admitted evidence for any gate.
- A digest mismatch exits 3 and keeps the offending archive for inspection; it is never
  silently re-downloaded over.
- Unknown platform, missing downloader, or a missing `libcef` after extraction are all
  non-zero with the reason in `cef_reason=`.
- Nothing outside `build/cef/` is ever removed.

## Honest limitations (do not infer past these)

- **macOS Vulkan proof is unavailable.** macOS ANGLE backs onto Metal; `--use-angle=vulkan`
  is not a shipped backend there, so a macOS host records `vulkan-angle-unavailable` per
  `doc/07_guide/tooling/renderdoc_capture_infra.md:748`. Chrome merely being available is
  never Vulkan proof.
- **macOS helper `.app`.** CEF spawns its render/GPU subprocesses from a separate helper
  bundle. Whether that works when `libcef` is `dlopen`ed from a non-bundled CLI is
  UNVERIFIED (`macos_helper_status=required-unverified-from-non-bundled-cli`) — blocked row
  B2 of `doc/03_plan/ui/chrome_dynlib/chrome_dynlib_vulkan_showcase_plan.md`.
- **The pin itself is UNVERIFIED.** The authoring host had no network, so the version, the
  URL template and every digest in `cef_pin.sdn` are placeholders. Fill them from the
  publisher's index — not from a file you already downloaded, which proves only that the
  file is itself.
