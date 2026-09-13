# Chrome (CEF) Dynlib Setup

Stages the pinned Chromium Embedded Framework binary drop that the Chrome render dynlib
(`src/runtime/browser/chrome_render_shim.c`) links against. Without a drop the shim still
builds — in **stub** mode, where every entry point returns
`CHROME_RENDER_E_BACKEND_UNAVAILABLE` — so stage A of the probe runs on any host.

Pin data (the version LINE, plus each platform's index key and in-drop library path):
`config/cef/cef_pin.sdn`. Both setup scripts read it and neither carries a second copy.
Archive names and digests are **not** there — they come from the publisher index at install
time; see "What is pinned" below.

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
| `cef_sha256_status` | `pinned` `unpinned` `unset` `mismatch` `unadmitted` |
| `cef_index_sha1` | the publisher index's own sha1 for the resolved archive (install), or the one recorded at install (check) |
| `cef_archive` | the archive name resolved from the index (install only) |
| `cef_admitted_sha256` | the measured sha256 recorded at install, replayed by `--check` |
| `macos_helper_status` | macOS only, see below |
| `cef_reason` | `ok` `no-cef-drop` `headers-absent` `libcef-absent` `pin-unset-refused` `download-failed-*` `extract-failed-*` … |
| `cef_status` | `present` (exit 0) / `missing` (exit 1-2) / `hash-mismatch` (exit 3) |

## What is pinned (changed 2026-09-11 — read this before looking for a digest table)

`config/cef/cef_pin.sdn` pins the **version line** (`143.0.13`), not a table of archive
names and digests. It used to carry a per-platform `sha256:` column; all six rows were
`UNSET`, so every install needed `--allow-unpinned` and nothing was ever verified. A
hand-maintained table could only be copied from the publisher's own index (adding nothing)
or computed from an already-downloaded file (which proves only that the file is itself).

The admission chain is now four steps, and each one is visible in the receipt:

1. `--install` fetches `https://cef-builds.spotifycdn.com/index.json` (or reads a local copy
   given with `--index-file` / `-IndexFile`).
2. It resolves the archive whose `cef_version` **starts with** the pinned version and whose
   `type` is the pinned `distribution:` (`minimal`), for this platform only, and prints
   `cef_archive=` and `cef_index_sha1=`.
3. The downloaded archive is admitted against that publisher `sha1`. Only then is its
   sha256 measured and recorded at `build/cef/<version>/<platform>/admitted.sha256`.
4. `--check` never touches the network: it reads that record. A staged drop with **no**
   `admitted.sha256` reports `cef_sha256_status=unadmitted` and `cef_status=missing`,
   because nothing ever verified it — a present-looking directory is not admission.

The version prefix is matched, not the full string, because the published `cef_version`
carries build metadata (`143.0.13+g<hash>+chromium-143.x.y.z`) that is not knowable without
reading the index. If no index entry starts with the pin, `--install` is **refused** with
`cef_reason=version-not-in-index` rather than quietly installing a different version.

## Fail-closed rules

- A pinned version that is **not in the index** is refused by `--install`.
  `--allow-unpinned` (`-AllowUnpinned`) is the escape for a version that genuinely is not
  published there — a locally built or vendor-supplied drop. It prints a loud warning, skips
  step 3's publisher check only (steps 3-4's recording and step 4's replay still run), and
  records `cef_sha256_status=unpinned` — such a drop is never admitted evidence for any gate.
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
- **The pinned version is UNVERIFIED.** The authoring host had no network, so `143.0.13`
  and the index's exact JSON shape were never read from the publisher. The index PARSER is
  proven offline (`--selftest` fixtures 6-9, on a canned `index.json` that deliberately
  carries a second platform and a second version so a naive regex would pick the wrong
  digest), but `--install` has not been run anywhere. Confirm the version line against the
  index on the first host that has network; a wrong pin is refused, not silently
  substituted. The old per-platform digest table is gone — do not restore it. Fill from the
  publisher's index — not from a file you already downloaded, which proves only that the
  file is itself.

## Running the Chrome-backed showcase (S2) and its perf check (S3)

```bash
# Both backends, receipts, PPMs, aggregates. Fatal selftest runs first.
sh scripts/check/check-chrome-web-showcase-perf.shs --selftest
sh scripts/check/check-chrome-web-showcase-perf.shs [--renderdoc]

# One backend by hand (the check does this per backend):
SIMPLE_2D_BACKEND=vulkan SIMPLE_EXECUTION_MODE=interpreter SIMPLE_TIMEOUT_SECONDS=0 \
  bin/release/<triple>/simple run src/app/ui/chrome_showcase/main.spl
```

Outputs: `examples/06_io/ui/web_catalog/*.html` + `catalog.sdn` (the SHARED catalog — the
Simple web renderer showcase consumes the same files), `build/chrome-showcase/<backend>/
<tab>.ppm`, and `build/chrome-showcase/<backend>/receipt.env`.

Env knobs: `SIMPLE_2D_BACKEND`, `SIMPLE_CHROME_SHOWCASE_{WIDTH,HEIGHT,OUT}`,
`SIMPLE_SHOWCASE_BINARY{,_SIZE,_MTIME}`, `SIMPLE_WEB_SHOWCASE_PPM_DIR` (the peer PPM
directory for the pixel-diff row; absent ⇒ `chrome_vs_simple_pixel_diff_status=unavailable`).

**Read `frame_source` before reading anything else.** With no CEF drop the composited
frame is a deterministic arithmetic test pattern, stamped `frame_source=stub-pattern` with
a non-empty `reason` and verdict `environment-blocked`. That is what a run on this Mac
reports today. A run that composited real Chrome output says `frame_source=chrome`; there
is no third possibility and a receipt missing the key is classified `failed`.
