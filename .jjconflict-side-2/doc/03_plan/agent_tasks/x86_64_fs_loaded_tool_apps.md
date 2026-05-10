# x86_64 FS-Loaded Tool Apps Completion Remainder

## Goal

Close the remaining gap for the existing `x64-desktop-uefi` lane so the six
tool apps already packaged on disk are proven end-to-end by the live guest
serial contract:

- `simple_browser`
- `simple_compiler`
- `simple_interpreter`
- `simple_loader`
- `llvm`
- `rust`

This is a remainder-only plan. Packaging, launcher registration, VFS aliasing,
and marker expectations already exist in the repo. Remaining work is limited to
proving that the live guest launch path actually satisfies the current contract
for those six apps.

## Current Repo Truth

The following work is already landed and should not be restated as primary
feature scope:

- Disk packaging for the six tool apps already exists in
  `scripts/make_os_disk.shs`.
- Canonical runtime app ids already exist as `/sys/apps/<name>`.
- Launcher-visible identities, compatibility aliases, and desktop shortcut
  wiring already exist in `src/os/services/launcher/launcher.spl`.
- VFS/kernel resolution already supports canonical filesystem app execution for
  `/sys/apps/<name>` with compatibility aliases and `.smf` sidecars treated as
  inputs.
- Host-side disk image validation and live serial marker expectations already
  exist.
- `src/os/qemu_runner.spl` `desktop_uefi_required_marker_fragments()` already
  defines the public live acceptance contract for `x64-desktop-uefi`.

## Remaining Delta

The remaining work is only to make the lane reliably pass with real,
process-backed proof for:

- `simple_browser`
- `simple_compiler`
- `simple_interpreter`
- `simple_loader`
- `llvm`
- `rust`

That means:

- prove guest launch behavior for each app on the canonical
  `/sys/apps/<name>` path
- reject resident-manifest fallback as completion evidence
- preserve `simple_browser` WM/render proof
- preserve the documented native-wrapper lane for `llvm` and `rust` while still
  requiring their toolchain markers

## Acceptance Contract

`src/os/qemu_runner.spl` marker requirements are the completion contract for
this plan. These markers are public acceptance interfaces, not implementation
suggestions.

Every successful live completion run must emit, for each target app:

- `[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/<app> bytes=`
- `[desktop-e2e] process-backed:ok app=<app> pid=`

Additional required proofs:

- `simple_browser`
  - `[desktop-e2e] wm-owner:ok app=simple_browser pid=`
  - `[desktop-e2e] render-proof:ok app=simple_browser pid=`
  - `[simple_browser] page_rendered app_id=/sys/apps/simple_browser`
- `llvm`
  - `[desktop-e2e] toolchain-launch:ok app=llvm mode=native-wrapper lane=x86_64-simpleos status=guest-exec tool=/usr/bin/clang`
- `rust`
  - `[desktop-e2e] toolchain-launch:ok app=rust mode=native-wrapper lane=x86_64-simpleos status=report-and-gate tool=/usr/bin/rustc aux=/usr/bin/cargo`

Resident-manifest fallback does not satisfy this plan, even if a window appears
or a launcher entry exists.

## Subsystem Ownership

### Disk / Media Layer

Touch this layer only if host validation or canonical app-id bytes are wrong.

- Preserve the existing disk packaging in `scripts/make_os_disk.shs`.
- Preserve FAT short-name compatibility and `.smf` sidecars as accepted inputs,
  not as runtime identity.
- Only change packaging if a host-side validation step proves that a target app
  or canonical app-id byte sequence is incorrect or missing.

### Launcher / VFS Resolution

Preserve canonical `/sys/apps/<name>` as the final identity after alias
normalization.

- Keep existing launcher names and Meta shortcuts for the six tool apps.
- Keep current alias normalization behavior for short-name and FAT-compatible
  inputs.
- Add aliases only if a failing focused test proves a specific missing input
  form.
- Do not let a compatibility alias become the final runtime identity reported by
  the lane.

### Runtime / Guest Launch

- `simple_browser` remains the reference filesystem-process desktop app.
- `simple_compiler`, `simple_interpreter`, and `simple_loader` may remain
  wrapper-like payloads in this pass, but they must still launch as real
  processes and emit `process-backed:ok` proof.
- `llvm` and `rust` remain wrapper frontends for x86_64 lane completion in this
  pass, but they must still emit both:
  - canonical `/sys/apps/<name>` VFS-read proof
  - process-backed launch proof
  - their required `toolchain-launch:ok` markers
- Resident fallback must fail closed if it reappears as the effective launch
  mode for any target app.

### Acceptance / Diagnostics

- `desktop_uefi_required_marker_fragments()` remains the source of truth.
- Failures must identify the missing app and missing proof family.
- The lane must fail closed if:
  - a required `vfs-app-read:ok` marker is absent
  - a required `process-backed:ok` marker is absent
  - `simple_browser` loses WM or render proof
  - `llvm` or `rust` loses its required toolchain marker
  - resident-manifest fallback reappears as effective completion behavior

## Non-Goals

The following are explicitly not part of the remaining work for this plan:

- porting full LLVM internals into a richer native SimpleOS app
- porting full Rust internals into a richer native SimpleOS app
- stage2/stage3 bootstrap convergence
- unrelated compiler failures outside what is strictly needed to re-run the
  lane
- broader argv/envp or process-image specification work that is not required to
  prove the six target apps on `x64-desktop-uefi`

## External Blockers

These remain external to this plan and must be called out directly rather than
absorbed into feature scope:

- any unresolved live-lane blocker that prevents a trustworthy
  `x64-desktop-uefi` rerun from HEAD
- any syscall-13 / direct-handoff regression that reintroduces
  resident-manifest fallback for packaged tool apps
- unrelated compiler or bootstrap failures that block broader work but do not
  change this plan's completion contract

## Accepted Default For This Milestone

x86_64 lane completion is satisfied by process-backed wrappers for these six
tool apps, not by full native tool implementations.

That default is accepted for:

- `simple_compiler`
- `simple_interpreter`
- `simple_loader`
- `llvm`
- `rust`

`simple_browser` still carries the extra desktop/render proof because it is the
reference process-backed filesystem desktop app in this set.

## Verification Plan

- Host disk image validation proves all six apps and companion `.smf` artifacts
  are present and contain canonical app-id bytes.
- Focused launcher/VFS tests prove alias inputs normalize to canonical
  `/sys/apps/<name>` identities.
- Focused runtime tests prove the launcher spawn path still uses the
  process-backed path for the six tool apps.
- Live `bin/simple os test --scenario=x64-desktop-uefi` proves all required
  marker families for all six apps.
- Negative checks prove the lane fails when:
  - a `vfs-app-read:ok` marker is missing
  - a `process-backed:ok` marker is missing
  - `simple_browser` loses WM/render proof
  - `llvm` or `rust` loses its required toolchain marker
  - resident-manifest fallback reappears as the effective launch mode

## Status

### Done

- Disk packaging already exists in `scripts/make_os_disk.shs` for:
  - `simple_browser`
  - `simple_compiler`
  - `simple_interpreter`
  - `simple_loader`
  - `llvm`
  - `rust`
- Canonical launcher identities and existing shortcut wiring already exist.
- Canonical `/sys/apps/<name>` alias normalization already exists.
- Host-side disk validation and live marker expectations already exist.
- `desktop_uefi_required_marker_fragments()` already requires the six tool-app
  VFS-read markers, process-backed markers, `simple_browser` render markers,
  and `llvm` / `rust` toolchain markers.

### Remaining

- Prove each target app launches through the canonical `/sys/apps/<name>` path
  in live guest execution.
- Prove each target app emits `process-backed:ok` evidence in the
  `x64-desktop-uefi` lane.
- Keep `simple_browser` WM/render proof intact while removing any effective
  dependence on resident fallback.
- Keep `llvm` and `rust` on the documented native-wrapper lane while still
  proving their required `toolchain-launch:ok` markers.
- Tighten failure diagnostics wherever needed so missing app and missing proof
  family are immediately visible.
