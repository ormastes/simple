# V4 Electron Packaging — First-class Target vs. Dev Preview

**Date:** 2026-04-14
**Status:** Decision (unblocks `doc/03_plan/gui_drawing_layer_variations.md` §5 item 3)
**Decision:** **Dev-preview only — V4 is build-able and wired into `wm_compare` as the Source-A reference renderer, but is NOT promoted to a shipped end-user target and NOT added to the release-artifact CI matrix.**

## 1. Context

`doc/03_plan/gui_drawing_layer_variations.md` §5 asks whether Electron is a
first-class shipping target or only a dev preview. The question is
load-bearing because it decides (a) whether V4 gets a CI lane that gates
`main`, (b) whether the release pipeline produces signed Electron bundles,
and (c) whether `src/app/ui.electron/` must reach feature parity with V1/V2
on the work matrix §4 item 6. `electron_capture.spl` is already wired into
the pixel-consistency pipeline as Source-A, which muddies the picture — the
Electron code isn't dead, but it plays a test-harness role, not an
end-user-shell role.

## 2. Options considered

### Option A — First-class shipped target

Promote V4 to a CI-gated release target: `.github/workflows/electron-tests.yml`
is repaired and made blocking; `bin/simple electron build` / `electron package`
(per `ELECTRON_VSCODE_WASM_PLAN.md`) are implemented; `src/app/ui.electron/main.spl`
lands with parity-screenshot enforcement in `wm_compare` matching V1/V2/V3.

### Option B — Dev-preview only (recommended)

Keep V4 build-able for developers. Retain `electron_capture.spl` as the
Source-A reference renderer inside `wm_compare`. Do **not** gate `main` on
Electron parity. Do **not** ship installers. Repair or retire the stale
`electron-tests.yml` workflow (which points at paths that no longer
exist). Leave the WASM Electron plan in `📋 PLANNED` — that work is a
distinct, headless-worker track, not V4-GUI.

### Option C — Archive/delete V4 entirely

Rejected. `electron_capture.spl` and `tools/electron-shell/screenshot.js`
are load-bearing for `wm_compare/html_compat.spl` and
`wm_compare/live_capture.spl` as Source-A (Chrome/Electron) reference.
Removing V4 wholesale would strip the cross-backend pixel-consistency
harness of its ground-truth renderer.

## 3. Evidence

### 3.1 LOC comparison (origin/main, `git show` + `wc -l`)

| Variant | Paths counted                                              | Lines  |
| ------- | ---------------------------------------------------------- | -----: |
| V1 app  | `src/app/ui.native/`                                       |      0 |
| V2 app  | `src/app/ui.gpu/`                                          |      0 |
| V3 app  | `src/app/ui.browser/` (1683) + `src/lib/.../browser_engine/` (5993) | **7676** |
| V4 app  | `src/app/ui.electron/` (509) + `src/os/compositor/electron_capture.spl` (160) | **669** |

**V3:V4 ratio ≈ 11.5 : 1.** V1/V2 app-side dirs are empty today — both
variants live inside `os/compositor/` + `lib/.../engine2d/`, so the app-side
LOC comparison reads V4 against V3 (the only other variant with a concrete
app-side adapter).

`src/app/ui.electron/` file breakdown:

```
 14  __init__.spl
101  app.spl
153  async_app.spl
109  backend.spl
124  bridge.js
  8  ipc.spl
```

Notably **no `main.spl`** — work-plan §4 item 6 ("Electron main/renderer
split … `src/app/ui.electron/main.spl` green in `wm_compare`") is
explicitly **"not yet planned"** in the matrix on origin/main.

### 3.2 Dependency cost

- `package.json` only exists under `src/app/vscode_extension/` and the
  vendored `vscode_extension_old/.vscode-test/` snapshot. **No top-level
  npm/pnpm workspace, no `electron-builder` config, no `.nvmrc`, no
  Electron version pin** on origin/main.
- Electron is invoked ad-hoc via `npx electron tools/electron-shell/screenshot.js`
  (`wm_compare/html_compat.spl:241`, `wm_compare/live_capture.spl:82-92`).
  It is a transient developer-toolchain dependency, not a pinned release
  dependency.
- `src/os/compositor/electron_capture.spl` (160 lines) externs:
  `os.compositor.wm_scene.{render_scene_to_backend}`,
  `os.compositor.diff_export`, `std.common.image.ppm_decode`,
  `std.nogc_sync_mut.ffi.io.{file_write_text, file_read_bytes}`, `std.io.{shell}`.
  Its header is explicit: *"Electron is used for display/preview only,
  not as a comparison renderer"* — the comparison renderer is
  `BrowserCompositorBackend`. This is a **capture/preview adapter, not a
  shell**.

### 3.3 Current completeness vs. `wm_compare`

`wm_compare` is the enforcement harness. Current backend coverage on
origin/main:

- **Source A** (reference): Electron via `capture_electron` / headless
  Chromium — WORKING. `html_compat.spl` and `live_capture.spl` both call it.
- **Source B**: `simple_browser_engine` (V3 path) — WORKING.
- **V1 (QEMU/baremetal)**: captured via `qemu_capture.spl` / `BrowserCompositorBackend`.
- **V2 hosted**: work-plan §4 item 3 still open (Cocoa/Win32 hosted
  surfaces not landed).
- **V4 as app target**: no scene runs end-to-end from `src/app/ui.electron/main.spl`
  because that file does not exist. Electron's wm_compare role today is
  **test-infrastructure**, not "V4 app path".

### 3.4 CI reference

`.github/workflows/electron-tests.yml` **exists** on origin/main
(matrix: `[ubuntu-latest, macos-latest, windows-latest] × [node 18, node 20]`),
but its `paths:` triggers target a stale tree:

```
- 'simple/std_lib/src/electron/**'
- 'simple/std_lib/test/electron/**'
- 'simple/std_lib/test/examples/electron_*.spl'
```

`git ls-tree origin/main` shows **zero files** under `simple/std_lib/`.
The workflow is effectively a dead CI lane — it never fires because its
watched paths don't exist, and none of the active Electron code
(`src/app/ui.electron/`, `src/os/compositor/electron_capture.spl`,
`tools/electron-shell/`) is in its filter. No other workflow references
Electron.

### 3.5 User-demand signals

- 17 recent commits touch Electron (see `git log --oneline origin/main --
  src/app/ui.electron/ src/os/compositor/electron_capture.spl …`). Notable:
  `8926770a37 feat: electron WM — multi-window IPC, menubar+dock widgets`,
  `c94d950e57 refactor(compositor): unify WM rendering — both paths use
  BrowserCompositorBackend for bit-identical output`.
- Commit theme skews strongly toward **unifying Electron as test harness**
  (pixel-consistency, BrowserCompositorBackend) rather than **shipping
  Electron apps to users**.
- `doc/03_plan/ELECTRON_VSCODE_WASM_PLAN.md` (2025-12-26, status 📋 PLANNED,
  14-week timeline) scopes Electron apps as **"UI-less applications
  (background workers, system services, language tools) rather than GUI
  applications."** That plan is explicitly not V4-GUI-shell work.
- No open tracker entry or TODO on origin/main says "ship Electron
  installers" — `electron_todo_scan` returns only pixel-consistency work
  items.

## 4. Recommendation

**Option B — dev-preview only.** V4's effective LOC on the app side is
~11× smaller than V3 (669 vs. 7676), it has no entry point
(`main.spl` absent), no npm workspace / electron-builder pin / Electron
version lock, and its single live CI workflow points at non-existent
paths. Meanwhile `electron_capture.spl` is genuinely load-bearing as
`wm_compare`'s Source-A reference renderer — deleting V4 would break the
pixel-consistency harness. The evidence says Electron has earned its
keep as a **test/preview adapter**, not as a shipping target. Promote
later only when all of the following gates close: (a) `src/app/ui.electron/main.spl`
lands and drives `browser_compositor_backend`; (b) `wm_compare` V4 scene
parity ≤1% perceptual delta against V1/V2/V3; (c) `electron-tests.yml`
`paths:` filter is rewritten to watch `src/app/ui.electron/**` and
`src/os/compositor/electron_capture.spl`, runs green on all three OSes,
and becomes a required check; (d) an `electron-builder` config + pinned
Electron version is committed under a top-level workspace. None of those
four gates are closed today.

## 5. Consequences

- **CI:** `.github/workflows/electron-tests.yml` is declared stale.
  Either retire it or rewrite its `paths:` filter to watch the real
  Electron tree (`src/app/ui.electron/**`,
  `src/os/compositor/electron_capture.spl`, `tools/electron-shell/**`)
  and explicitly mark it *non-blocking* until gates (a)–(d) close. Until
  then, Electron stays out of the required-check set.
- **Release:** No Electron installer artifacts are produced by
  `.github/workflows/release.yml` or `publish.yml`. No code-signing /
  notarization work is scheduled for V4.
- **Docs:** `doc/07_guide/ui_stack_guide.md` should mark V4 "dev
  preview"; `doc/03_plan/ELECTRON_VSCODE_WASM_PLAN.md` remains scoped to
  headless workers (orthogonal track).
- **Work matrix:** `gui_drawing_layer_variations.md` §4 item 6
  ("Electron main/renderer split ... green in `wm_compare`") remains
  *not yet planned* — consistent with dev-preview status.
- **§5 update:** All three original open decisions are now closed.
- **`electron_capture.spl` retention:** explicitly preserved in its
  Source-A role; the "Electron is used for display/preview only, not as
  a comparison renderer" contract in its header is now the documented
  project-wide stance.

## 6. Proposed diff to `doc/03_plan/gui_drawing_layer_variations.md` §5

```diff
 - ~~**V3 shell choice:** CEF embedding vs. growing `examples/browser` into
   a usable Chromium-class shell. See memory `project_browser_platform`.~~
   **DECIDED — Option B (simple_browser).** See
   [v3_shell_choice_2026-04-14.md](../01_research/domain/v3_shell_choice_2026-04-14.md).
 - ~~**GPU path for V2:** Vulkan everywhere vs. native (Metal/DX) per OS.
   Current modules favor both; pick per-platform default.~~
   **DECIDED — Metal on macOS, Vulkan on Linux + Windows + FreeBSD.** See
   [v2_gpu_defaults_2026-04-14.md](../01_research/domain/v2_gpu_defaults_2026-04-14.md).
-- **Electron packaging:** Are we shipping Electron as a first-class target
-  or only as a dev preview? This changes whether V4 is in CI.
+- ~~**Electron packaging:** Are we shipping Electron as a first-class target
+  or only as a dev preview? This changes whether V4 is in CI.~~
+  **DECIDED — Dev-preview only.** `electron_capture.spl` stays as `wm_compare`
+  Source-A reference renderer; no release artifacts; stale
+  `electron-tests.yml` to be retired or rescoped as non-blocking. See
+  [v4_electron_packaging_2026-04-14.md](../01_research/domain/v4_electron_packaging_2026-04-14.md).
```

And in the Decisions subsection near the bottom:

```diff
 ### Decisions
 - V3 shell choice → [v3_shell_choice_2026-04-14.md](../01_research/domain/v3_shell_choice_2026-04-14.md) — Option B
 - V2 GPU defaults → [v2_gpu_defaults_2026-04-14.md](../01_research/domain/v2_gpu_defaults_2026-04-14.md)
+- V4 Electron packaging → [v4_electron_packaging_2026-04-14.md](../01_research/domain/v4_electron_packaging_2026-04-14.md) — dev-preview only
```

## 7. References

- `doc/03_plan/gui_drawing_layer_variations.md` §2 (V4), §4 item 6, §5.
- `doc/03_plan/ELECTRON_VSCODE_WASM_PLAN.md` (2025-12-26, PLANNED,
  headless-workers scope).
- `src/os/compositor/electron_capture.spl` — Source-A capture adapter,
  header declares preview-only role.
- `src/app/ui.electron/{__init__, app, async_app, backend, bridge.js, ipc}.spl` — 509 LOC, no `main.spl`.
- `src/app/wm_compare/html_compat.spl`, `src/app/wm_compare/live_capture.spl` — Electron is the Source-A ground truth.
- `.github/workflows/electron-tests.yml` — stale `paths:` filter pointing at non-existent `simple/std_lib/**`.
- `src/app/ui.browser/` (1683) + `src/lib/gc_async_mut/gpu/browser_engine/` (5993) — V3 comparable-effort baseline.
- Sibling decision docs: `v3_shell_choice_2026-04-14.md`, `v2_gpu_defaults_2026-04-14.md`.
