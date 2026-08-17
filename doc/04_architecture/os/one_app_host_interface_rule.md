# One App, One Host Interface — no per-OS app forks

- **Date**: 2026-08-16
- **Status**: RULE (verified against the tree, see Evidence)
- **Applies to**: every app under `src/os/apps/**`, `src/app/**`, and any new
  userland service that runs on both SimpleOS and hosted OSes

## The rule

**An app is written ONCE and runs on every OS.** SimpleOS vs Linux/macOS/
Windows never means a second version of the app. The only things allowed to
vary are:

1. **The host interface implementation (HAL).** All platform difference lives
   behind one of the established boundaries:
   - `os.sosix.host.service_contract` — display/input/timer requests
     (`SosixDisplayRequest`, completion keys); per-OS adapters wrap each
     backend against it, sharing `host_services/display_adapter_common.spl`
   - `os.compositor.display_backend_core.CompositorBackend` — rendering;
     per-OS backends (`HostedCocoaBackend`, `HostedWin32Backend`,
     `HostedSdl2Backend`, winit, headless) chosen at ONE dispatch site,
     `select_hosted_backend()` (`hosted_backend.spl`)
   - `common.platform.dedicated_host.DedicatedHost` — memory mapping;
     `SimpleOsDedicatedHost` vs `PosixDedicatedHost`
2. **Configuration.** Feature availability, sizes, paths, backend selection —
   data, not forked code. A capability an OS lacks is modeled as an OPTIONAL
   capability on the interface (the pattern `as_glass_capable() -> ...?` uses:
   Cocoa returns self, others return nil), never as `if os == ...` in app code.

The app layer talks to `os.userlib.*` facades (e.g. `WindowClient`) and never
names an OS. **Default runtime family for host-interface code is
`nogc_async_mut`** (async, no GC) unless the surface is inherently synchronous
I/O — matching the stdlib layering in `.claude/rules/structure.md`.

## What is banned

- A `foo_simpleos.spl` sibling of `foo.spl` at the APP layer. (At the HAL
  layer, per-OS files are exactly where difference belongs.)
- `if target_os == ...` / `is_windows()` / `"simpleos"` branches in app logic.
  Platform predicates are allowed only inside a backend's own `try_create`
  guard or inside the HAL module itself.
- Adding a per-OS capability by copying an existing adapter/backend file.
  Extend the shared helper (`display_adapter_common.spl`) or add an optional
  capability trait instead.
- "Fixing" an app on one OS by importing that OS's modules into the app.

## Evidence this is achievable (measured 2026-08-16)

- `src/os/apps/**` (~150 files): **zero** platform conditionals. All
  `simpleos` hits are branding strings and target triples.
- One dispatch site selects the backend; apps reach the host only through
  `os.userlib.window.WindowClient` and SOSIX services.
- The two violations found were both duplication, not necessary forks, and
  both are fixed: triplicated display-adapter helpers (collapsed into
  `display_adapter_common.spl`, commit `40481819e92`) and the thrice-written
  browser jailed-render handshake (collapsed into
  `os.hosted.hosted_browser_render_session`, commit `43e199d5317`).

## Sanctioned asymmetries (do not "fix")

- `hosted_win32_mdi_probe.spl` — a raw-Win32 diagnostic harness driven by
  `check-windows-native-mdi-evidence.{shs,ps1}`; it bypasses
  `CompositorBackend` deliberately because it measures what the backend hides.
- Theme bootstrap pair (`simpleos_wm_theme_bootstrap.spl` vs
  `host_wm_theme_bootstrap.spl`) — freestanding boot has no package registry;
  both converge on `apply_theme_render_snapshot_to_wm_chrome`.
- Glass/blur — optional capability, correctly modeled through the interface.
- The tiny stack (`std.tiny.*`, `os/apps/tiny_browser`) is its OWN closed
  world by scope: it must not import the full compositor/Web renderer, and the
  large browser must not be wired into it.

## Checklist for a new app (copy into design docs)

1. Does the app import anything under `os.compositor.hosted_backend_*`,
   `os.sosix.host.*` adapters, or name an OS? → move it behind the HAL.
2. Is a per-OS difference expressed as config or an optional capability? →
   good. As a code branch or sibling file in the app? → redesign.
3. Host-interface additions default to `nogc_async_mut`.
4. Before writing a multi-step handshake against a host subsystem, search for
   the existing driver with `/usr/bin/grep -rn` (see `doc/glossary.md` →
   "Re-derived sequence").

See also: `doc/glossary.md` ("Host interface (hosted apps)", "Jailed render
session"), `doc/04_architecture/compiler/mdsoc_architecture_tobe.md` (MDSOC+),
`.spipe/tiny_ui_web_wm/state.md` (tiny-stack scope exclusions).
