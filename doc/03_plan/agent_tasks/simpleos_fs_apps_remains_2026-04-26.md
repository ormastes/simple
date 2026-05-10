# SimpleOS FS Apps Remaining Plan - 2026-04-26

Feature: `simpleos_fs_apps_remains_2026-04-26`

## Goal

Close the remaining filesystem-app gap for the existing `x64-desktop-uefi`
acceptance lane so the six remaining tool apps are:

- packaged on disk under `/sys/apps/*`
- resolved canonically through launcher and VFS as `/sys/apps/<name>`
- launched as process-backed guest apps
- proven by the live QEMU serial contract in `src/os/qemu_runner.spl`

Target app set:

- `simple_browser`
- `simple_compiler`
- `simple_interpreter`
- `simple_loader`
- `llvm`
- `rust`

## Source Of Truth

- Packaging and prior remaining-scope notes:
  `doc/03_plan/agent_tasks/x86_64_fs_loaded_tool_apps.md`
- Process-backed migration and fallback-removal contract:
  `doc/03_plan/agent_tasks/simpleos_process_apps_plan.md`
- Authoritative live acceptance markers:
  `src/os/qemu_runner.spl` `desktop_uefi_required_marker_fragments()`
- FR-SOS-024 syscall-13 direct-handoff tracking and live blocker notes:
  `doc/08_tracking/feature_request/simpleos_os_requests.md`
  (`FR-SOS-024 — Complete syscall 13 direct user-process handoff`)
  `doc/09_report/fr_sos_024_desktop_disk_live_2026-04-22.md`
  `doc/08_tracking/todo/simpleos_stub_collision_freestanding_2026-04-21.md`

The `qemu_runner.spl` marker list is the completion contract, not a suggestion.
This plan closes the remaining fs-app/tool-app work against that contract.

## Scope

- Package the six target apps into the FAT32/NVMe disk image with canonical
  `/sys/apps/<name>` identity.
- Preserve compatibility aliases such as FAT short names and `.smf` sidecars
  only as inputs; they are not the primary runtime identity.
- Make launcher-visible naming, VFS reads, and process-backed launch evidence
  line up on the same canonical app id.
- Require the live serial stream to prove both:
  - `[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/<app> bytes=`
  - `[desktop-e2e] process-backed:ok app=<app> pid=`
- Preserve existing special proofs already required by the lane:
  - `simple_browser` WM owner and render proof
  - `llvm` / `rust` `toolchain-launch:ok` proof

## Out Of Scope

- New packaging formats beyond the existing disk image plus compatibility
  `.smf` artifacts already used by the lane
- New scheduler models, new kernel ABI, or a parallel launcher architecture
- Unrelated compiler fixes except for blockers strictly required to re-run the
  live lane
- Porting full LLVM or Rust toolchains into richer userland payloads beyond the
  documented native-wrapper acceptance lane

## Current Evidence And Gap

- `x86_64_fs_loaded_tool_apps.md` already defines the intended app set and the
  required VFS/process-backed marker families.
- `simpleos_process_apps_plan.md` records that the target model is VFS-loaded,
  scheduler-owned, process-backed apps and that packaged apps must stop hiding
  behind resident-manifest fallback.
- `src/os/qemu_runner.spl` already hard-requires all six tool-app
  `process-backed:ok` markers, all six tool-app `vfs-app-read:ok` markers, the
  `simple_browser` WM/render markers, and the `llvm` / `rust`
  `toolchain-launch:ok` markers for `x64-desktop-uefi`.
- FR-SOS-024 remains the authoritative requirement for the syscall 13
  direct-handoff/process-backed runtime path. This remainder plan narrows that
  broader requirement to the six tool apps already required by the current
  `x64-desktop-uefi` lane.
- FR-SOS-024 still remains open for full live coverage because the prior
  disk-live proof showed resident fallback instead of end-to-end
  process-backed evidence, and the current re-run path may still be blocked by
  the freestanding-stub symbol-weakness collision.

## Parallel Agent Ownership

### Agent 1 - Disk Packaging And VFS Bytes

Own packaging, aliases, and executable-byte availability.

- Ensure each target app exists on disk as `/sys/apps/<name>`.
- Ensure expected `.smf` companions remain present where the lane already
  expects them.
- Normalize FAT32 alias handling so short-name or compatibility aliases still
  resolve to the canonical `/sys/apps/<name>` identity.
- Verify host-side image inspection and manifest-byte checks for all six apps.

Acceptance:

- Host disk validation sees:
  - `simple_browser`, `simple_compiler`, `simple_interpreter`,
    `simple_loader`, `llvm`, `rust`
  - expected `.smf` companions for the same app set
- Serial emits, for each target app:
  - `[desktop-e2e] vfs-app-read:ok source=generic-vfs path=/sys/apps/<app> bytes=`

### Agent 2 - Launcher Resolution And Shortcut Wiring

Own launcher-visible app naming and launch routing.

- Keep canonical launcher identities:
  - `simple_browser`
  - `simple_compiler`
  - `simple_interpreter`
  - `simple_loader`
  - `llvm`
  - `rust`
- Preserve current short-name normalization such as `sbrowser`, `scompiler`,
  `sinterp`, and `sloader`.
- Extend alias handling only if a missing alias is proven by focused tests.
- Ensure launcher resolution prefers canonical `/sys/apps/<name>` execution
  identity and does not regress desktop shortcuts or shell command routing.

Acceptance:

- Launcher records canonical app ids for all six tool apps.
- No successful launch path reports a mismatched alias as the final app
  identity.
- Existing shortcut and command resolution remains green for the desktop lane.

### Agent 3 - Process-Backed Runtime Entry For Tool Apps

Own guest-exec/runtime behavior for the remaining tool apps.

- Keep `simple_browser` on the current filesystem-process desktop proof path.
- Make `simple_compiler`, `simple_interpreter`, and `simple_loader` prove
  process-backed guest launch even if their current payload stays wrapper-like.
- Keep `llvm` and `rust` on the documented native-wrapper lane and satisfy the
  explicit toolchain markers already enforced by `qemu_runner.spl`.
- Do not allow resident-manifest fallback to masquerade as completion for the
  six target apps.

Acceptance:

- Serial emits, for each target app:
  - `[desktop-e2e] process-backed:ok app=<app> pid=`
- `simple_browser` still emits:
  - `[desktop-e2e] wm-owner:ok app=simple_browser pid=`
  - `[desktop-e2e] render-proof:ok app=simple_browser pid=`
  - `[simple_browser] page_rendered app_id=/sys/apps/simple_browser`
- `llvm` and `rust` still emit:
  - `[desktop-e2e] toolchain-launch:ok app=llvm mode=native-wrapper lane=x86_64-simpleos status=guest-exec tool=/usr/bin/clang`
  - `[desktop-e2e] toolchain-launch:ok app=rust mode=native-wrapper lane=x86_64-simpleos status=report-and-gate tool=/usr/bin/rustc aux=/usr/bin/cargo`

### Agent 4 - Acceptance Contract And Live-QEMU Diagnostics

Own the authoritative `x64-desktop-uefi` contract and diagnostics.

- Treat `desktop_uefi_required_marker_fragments()` in `src/os/qemu_runner.spl`
  as the live completion source of truth.
- Tighten summary helpers or diagnostic reporting so failures identify:
  - missing VFS-read proof
  - missing process-backed proof
  - missing browser-specific proof
  - missing toolchain-specific proof
- Fail closed if any target app still relies on resident-manifest behavior in
  the live lane.

Acceptance:

- The lane fails when any required tool-app marker is absent.
- Diagnostics identify the exact missing app and proof family.
- Completion is rejected if resident-manifest fallback reappears for any target
  app.

### Agent 5 - Tracking And Closure Notes

Own planning/tracking cleanup around the remaining gap.

- Link this work directly to:
  - `doc/03_plan/agent_tasks/x86_64_fs_loaded_tool_apps.md`
  - `doc/03_plan/agent_tasks/simpleos_process_apps_plan.md`
  - `doc/08_tracking/feature_request/simpleos_os_requests.md`
  - `doc/09_report/fr_sos_024_desktop_disk_live_2026-04-22.md`
- Record that this closes only the fs-app/tool-app remainder for the current
  x64 desktop lane; it does not replace FR-SOS-024 as the owner of the
  underlying syscall 13 direct-handoff requirement.
- Keep external blockers explicit rather than burying them in implementation
  notes.

Acceptance:

- Dependencies, blockers, and done criteria are named in one place.
- Any unresolved external blocker is called out directly.

## Dependencies

- Disk image packaging path in `scripts/make_os_disk.shs` and any helper code it
  depends on
- Launcher resolution and shell/shortcut routing for `/sys/apps/*`
- VFS executable-byte resolution for packaged FAT32 apps
- Kernel direct-handoff/process creation path covered by FR-SOS-024
- `src/os/qemu_runner.spl` marker checks and diagnostics

## External Blockers

- The freestanding-stub symbol-weakness collision tracked in
  `doc/08_tracking/todo/simpleos_stub_collision_freestanding_2026-04-21.md`
  remains an external dependency if it still prevents a trustworthy live rerun
  from HEAD.
- Any blocker in syscall 13 direct handoff that reintroduces
  `resident-manifest` behavior for packaged tool apps is a stop-ship issue for
  this plan, not something to paper over with broader acceptance wording.

## Verification Plan

- Host disk-content validation for all six target apps and expected `.smf`
  companions.
- Focused launcher-resolution tests for canonical identity and short-name
  normalization.
- Focused VFS/executable-source tests proving canonical `/sys/apps/<name>`
  reads even when compatibility aliases are used as inputs.
- Live `x64-desktop-uefi` QEMU acceptance proving required markers for:
  - `simple_browser`
  - `simple_compiler`
  - `simple_interpreter`
  - `simple_loader`
  - `llvm`
  - `rust`
- Negative acceptance checks proving the lane fails when:
  - a target app lacks `vfs-app-read`
  - a target app lacks `process-backed:ok`
  - `simple_browser` lacks WM/render proof
  - `llvm` or `rust` lacks the required toolchain marker
  - resident-manifest fallback reappears for a target app

## Done Criteria

- All six target apps are packaged on disk and discoverable through canonical
  `/sys/apps/<name>` identity.
- The live serial stream for `x64-desktop-uefi` contains the required
  `vfs-app-read:ok` marker for each target app.
- The live serial stream for `x64-desktop-uefi` contains the required
  `process-backed:ok` marker for each target app.
- `simple_browser` still satisfies the WM/render acceptance proofs.
- `llvm` and `rust` still satisfy the native-wrapper `toolchain-launch:ok`
  proofs.
- The lane fails closed with actionable diagnostics if any of the above proof
  families are missing.
- Resident-manifest fallback is not accepted as completion evidence for the six
  target apps.

## Closure Note

This plan closes the remaining fs-app/tool-app work for the existing x64
desktop acceptance lane. It does not broaden scope into unrelated compiler
repairs, new app packaging systems, or scheduler redesign beyond what is
strictly required to re-run and satisfy the current contract.
