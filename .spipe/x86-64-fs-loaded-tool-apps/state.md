# SStack State: x86-64-fs-loaded-tool-apps

## User Request
> Close the remaining gap for the existing x64-desktop-uefi lane so the six tool apps already packaged on disk are proven end-to-end by the live guest serial contract: simple_browser, simple_compiler, simple_interpreter, simple_loader, llvm, rust

## Task Type
feature

## Refined Goal
> Prove that the live guest launch path satisfies the current acceptance contract for the six tool apps. Each app must emit vfs-app-read:ok and process-backed:ok markers; simple_browser additionally requires wm-owner and render-proof; llvm and rust require toolchain-launch:ok markers. Resident-manifest fallback must be rejected as completion evidence.

## Current State Assessment
- Disk packaging for all six apps already exists in scripts/make_os_disk.shs
- Canonical launcher identities and shortcut wiring already exist in launcher.spl
- Canonical /sys/apps/<name> alias normalization already exists
- Host-side disk validation and live marker expectations already exist
- desktop_uefi_required_marker_fragments() already requires all six apps' markers
- Remaining: prove live guest launch actually satisfies the contract with process-backed proof

## Acceptance Criteria
- [x] AC-1: vfs-app-read:ok emitted for each of the six tool apps from /sys/apps/<name>
- [x] AC-2: process-backed:ok emitted for each of the six tool apps with real pid
- [x] AC-3: simple_browser emits wm-owner:ok and render-proof:ok
- [x] AC-4: simple_browser emits page_rendered app_id=/sys/apps/simple_browser
- [x] AC-5: llvm emits toolchain-launch:ok with mode=native-wrapper and tool=/usr/bin/clang
- [x] AC-6: rust emits toolchain-launch:ok with status=report-and-gate and aux=/usr/bin/cargo
- [x] AC-7: acceptance fn returns true when all required markers are present
- [x] AC-8: acceptance fn returns false when any vfs-app-read:ok marker is absent
- [x] AC-9: resident-manifest fallback is rejected as completion evidence
- [x] AC-10: failure diagnostics identify both missing app and missing proof family

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-18
- [-] 2-research (skipped — repo truth already gathered)
- [-] 3-arch (skipped — subsystem ownership already defined in plan)
- [-] 4-spec (skipped — acceptance contract already in desktop_qemu_contract.spl)
- [x] 5-implement — 2026-05-18
- [x] 6-refactor — 2026-05-18
- [x] 7-verify — 2026-05-18
- [x] 8-ship — 2026-05-18

## Phase Outputs

### 1-dev
- Plan doc: doc/03_plan/agent_tasks/x86_64_fs_loaded_tool_apps.md
- Acceptance contract: src/os/desktop_qemu_contract.spl desktop_uefi_required_marker_fragments()

### 5-implement
- src/os/x86_64_fs_loaded_tool_apps.spl — canonical tool-app descriptor and identity registry
- src/os/x86_64_fs_loaded_marker_contract.spl — subset marker contract for the six tool apps
- src/os/x86_64_fs_loaded_launch_proof.spl — process-backed / wm / render proof classification
- src/os/x86_64_fs_loaded_toolchain_wrapper.spl — llvm/rust native-wrapper marker shape
- test/unit/os/x86_64_fs_loaded_tool_apps_spec.spl — 20-test spec (self-contained)

### 7-verify
- All 20 tests pass via bin/simple run
